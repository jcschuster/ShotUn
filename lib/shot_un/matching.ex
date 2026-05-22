defmodule ShotUn.Matching do
  @moduledoc """
  Decidable higher-order matching for the second-order fragment.

  Higher-order *matching* is the task of finding a substitution σ such
  that σ(s) ≡_βη t for two given terms s and t where t is _ground_
  (contains no free variables). General higher-order matching is
  decidable (Stirling 2009) but impractical to implement; this module
  restricts to Huet's second-order fragment, where every variable and
  constant in the problem has a type of order at most 2.

  Termination is guaranteed by a structural argument on the multi-set of
  right-hand sides: every imitation step strictly decreases the total
  size of the targets, and every projection step eliminates a flex
  variable without introducing new ones (for order-1 flex arguments) or
  introduces strictly-smaller-order metas (for order-2 flex arguments).
  No depth bound is needed.

  Inputs that violate the second-order or ground-target preconditions
  raise `ArgumentError`.
  """

  alias ShotDs.Data.{Substitution, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  alias ShotUn.{Bindings, Fragment, Internal, UnifSolution}

  @typep term_pair :: {Term.term_id(), Term.term_id()}
  @typep search_state :: %{
           pairs: [term_pair()],
           substs: [Substitution.t()]
         }

  @typep step_t ::
           :fail
           | {:solution, UnifSolution.t()}
           | {:branch, [search_state()]}
           | {:next, search_state()}

  @doc """
  Returns the lazy stream of all matchers for the given problem.

  Raises `ArgumentError` if any right-hand side has free variables, or if
  any type in the problem has order greater than 2.
  """
  @spec match([term_pair()] | term_pair()) :: Enumerable.t(UnifSolution.t())
  def match(pair_or_pairs)

  def match({l, r}) when is_integer(l) and is_integer(r), do: match([{l, r}])

  def match(pairs) when is_list(pairs) do
    validate!(pairs)
    do_match(pairs)
  end

  defp do_match(pairs) do
    Stream.resource(
      fn ->
        TF.start_scratchpad()

        scope =
          for {l, r} <- pairs,
              id <- [l, r],
              fvar <- TF.get_term!(id).fvars,
              into: MapSet.new(),
              do: fvar

        {[%{pairs: pairs, substs: []}], scope}
      end,
      fn
        {[], _scope} = acc ->
          {:halt, acc}

        {stack, scope} ->
          case explore_branch(stack) do
            nil ->
              {:halt, {[], scope}}

            {raw_solution, new_stack} ->
              cleaned = clean_solution(raw_solution, scope)
              committed = commit_solution(cleaned)
              {[committed], {new_stack, scope}}
          end
      end,
      fn _ -> TF.stop_scratchpad() end
    )
  end

  defp validate!(pairs) do
    Enum.each(pairs, fn {l, r} ->
      unless Fragment.ground?(r) do
        raise ArgumentError,
          message:
            "ShotUn.Matching requires a ground right-hand side. " <>
              "Pass the pattern on the left and the target on the right."
      end

      unless Fragment.bounded_order?(l, 2) and Fragment.bounded_order?(r, 2) do
        raise ArgumentError,
          message:
            "ShotUn.Matching only handles second-order problems " <>
              "(every type in the problem must have order ≤ 2). " <>
              "Use ShotUn.unify/3 with a depth bound for higher-order inputs."
      end
    end)
  end

  ##############################################################################
  # SEARCH ENGINE
  ##############################################################################

  @spec explore_branch([search_state()]) :: {UnifSolution.t(), [search_state()]} | nil
  defp explore_branch([]), do: nil

  defp explore_branch([current | remaining]) do
    case step(current) do
      :fail -> explore_branch(remaining)
      {:solution, sol} -> {sol, remaining}
      {:branch, branches} -> explore_branch(branches ++ remaining)
      {:next, updated} -> explore_branch([updated | remaining])
    end
  end

  @spec step(search_state()) :: step_t()
  defp step(%{pairs: [], substs: substs}),
    do: {:solution, %UnifSolution{substitutions: substs, flex_pairs: []}}

  defp step(%{pairs: [{l, r} | rest]} = state) do
    if l == r do
      {:next, %{state | pairs: rest}}
    else
      left = TF.get_term!(l)
      right = TF.get_term!(r)
      evaluate_pair(left, right, state, rest)
    end
  end

  @spec evaluate_pair(Term.t(), Term.t(), search_state(), [term_pair()]) :: step_t()
  defp evaluate_pair(term_1, term_2, state, rest)

  defp evaluate_pair(%Term{type: t1}, %Term{type: t2}, _s, _r) when t1 != t2, do: :fail

  defp evaluate_pair(
         %Term{head: %{kind: :co} = c} = left,
         %Term{head: %{kind: :co} = c} = right,
         state,
         rest
       ) do
    case Internal.decompose(left, right) do
      {:ok, new_pairs} -> {:next, %{state | pairs: new_pairs ++ rest}}
      :error -> :fail
    end
  end

  defp evaluate_pair(
         %Term{head: %{kind: :bv} = left_head} = left,
         %Term{head: %{kind: :bv} = right_head} = right,
         state,
         rest
       ) do
    if Internal.same_bound_slot?(left, left_head, right, right_head) do
      case Internal.decompose(left, right) do
        {:ok, new_pairs} -> {:next, %{state | pairs: new_pairs ++ rest}}
        :error -> :fail
      end
    else
      :fail
    end
  end

  # Direct flex binding when the flex side has no args and no outer binders.
  defp evaluate_pair(
         %Term{head: %{kind: :fv} = var, args: [], bvars: []},
         right,
         state,
         rest
       ),
       do: bind(var, right, state, rest)

  # Flex-rigid: imitation through constants, projection through any arg.
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :co}}, state, rest),
    do: do_bindings([:imitation, :projection], state, rest)

  # Flex-bound: only projection is sound (imitation through a bound variable
  # would risk variable capture).
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :bv}}, state, rest),
    do: do_bindings([:projection], state, rest)

  # Anything else (constant-vs-bound head, mismatched constants, ...) fails.
  defp evaluate_pair(_left, _right, _state, _rest), do: :fail

  ##############################################################################
  # SUBSTITUTION ENGINE (matching variant — no flex-flex carry-over)
  ##############################################################################

  defp bind(var, right_term, state, rest_pairs) do
    if var in right_term.fvars do
      :fail
    else
      new_subst = Substitution.new(var, right_term.id)
      {:next, apply_substitution(new_subst, state, rest_pairs)}
    end
  end

  defp apply_substitution(new_subst, state, rest_pairs) do
    updated_substs = Semantics.add_subst!(state.substs, new_subst)

    updated_pairs =
      Enum.map(rest_pairs, fn {l_id, r_id} ->
        {Semantics.subst!(new_subst, l_id), Semantics.subst!(new_subst, r_id)}
      end)

    %{state | substs: updated_substs, pairs: updated_pairs}
  end

  defp do_bindings(binding_types, state, rest_pairs) do
    [{flex_id, rigid_id} | _] = state.pairs

    flex_head = TF.get_term!(flex_id).head
    rigid_head = TF.get_term!(rigid_id).head

    substs = Bindings.generic_binding(flex_head, rigid_head, binding_types)

    branches =
      Enum.map(substs, fn subst ->
        apply_substitution(subst, state, [{flex_id, rigid_id} | rest_pairs])
      end)

    {:branch, branches}
  end

  ##############################################################################
  # SOLUTION CLEAN-UP & COMMIT (mirrors ShotUn)
  ##############################################################################

  defp clean_solution(%UnifSolution{substitutions: substs}, initial_scope) do
    normalized =
      for subst <- substs, MapSet.member?(initial_scope, subst.fvar) do
        %{subst | term_id: Semantics.subst!(substs, subst.term_id)}
      end

    %UnifSolution{substitutions: normalized, flex_pairs: []}
  end

  defp commit_solution(%UnifSolution{substitutions: substs}) do
    committed =
      Enum.map(substs, fn subst ->
        %{subst | term_id: TF.commit_to_global!(subst.term_id)}
      end)

    %UnifSolution{substitutions: committed, flex_pairs: []}
  end
end
