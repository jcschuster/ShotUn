defmodule ShotUn do
  @moduledoc """
  Higher-order unification for the data structures and semantics of
  [ShotDs](https://hexdocs.pm/shot_ds/readme.html).

  Three algorithms are available:

    * `unify/3` (default) — depth-bounded *pre-unification* (Huet 1975):
      handles arbitrary higher-order problems but is a semi-decision
      procedure; flex-flex pairs are returned as constraints.
    * `pattern_unify/1` — *Miller pattern unification* (Miller 1991): a
      decidable, unitary fragment in which every flex variable is applied
      only to distinct bound variables. Returns at most one MGU.
    * `match/2` — *Huet second-order matching*: the right-hand side is
      ground, every variable in the problem has type of order ≤ 2.
      Returns the complete (lazy) stream of matchers without a depth
      bound.

  `unify/3` accepts a `:strategy` option (`:pre_unification`, `:auto`,
  `:pattern`, `:matching`). With `:auto`, the problem is inspected and
  routed to the most specific decidable algorithm it falls into:

    * if every pair is a pattern → `pattern_unify/1`,
    * otherwise if it satisfies the matching precondition → `match/2`,
    * otherwise pre-unification.

  See `ShotUn.Pattern`, `ShotUn.Matching` and `ShotUn.Fragment` for
  details on the individual algorithms and the fragment classifiers.
  """

  alias ShotDs.Data.{Substitution, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  alias ShotUn.{Bindings, Fragment, Internal, Matching, Pattern, UnifSolution}

  @typep term_pair :: {Term.term_id(), Term.term_id()}
  @typep search_state :: %{
           pairs: [term_pair()],
           subst: [Substitution.t()],
           flex: [term_pair()],
           depth: non_neg_integer()
         }
  @typep step_t ::
           :fail
           | {:solution, UnifSolution.t()}
           | {:branch, [search_state()]}
           | {:next, search_state()}

  @type strategy :: :pre_unification | :auto | :pattern | :matching

  @doc """
  Solves a higher-order unification problem.

  Accepts a single term pair `{l, r}` or a list of pairs. `depth` is
  the search-depth budget for the pre-unification fragment; it is
  ignored by the matching and pattern strategies. `opts` accepts:

    * `:strategy` — one of `:pre_unification` (default), `:auto`,
      `:pattern`, `:matching`. See module docs for dispatch rules.

  Returns a lazy `Stream` of `ShotUn.UnifSolution` structs. The
  `:pattern` strategy yields zero or one solution; the other strategies
  may yield more (or none).
  """
  @spec unify([term_pair()] | term_pair(), non_neg_integer(), keyword()) ::
          Enumerable.t(UnifSolution.t())
  def unify(term_pairs, depth \\ 10, opts \\ [])

  def unify({t1, t2} = pair, depth, opts) when is_integer(t1) and is_integer(t2),
    do: unify([pair], depth, opts)

  def unify(term_pairs, depth, opts) when is_list(term_pairs) do
    case Keyword.get(opts, :strategy, :pre_unification) do
      :pre_unification -> pre_unification(term_pairs, depth)
      :pattern -> pattern_stream(term_pairs)
      :matching -> Matching.match(term_pairs)
      :auto -> dispatch_auto(term_pairs, depth)
      other -> raise ArgumentError, "unknown strategy: #{inspect(other)}"
    end
  end

  @doc """
  Returns the (lazy) stream of all matchers σ such that σ(s) ≡_βη t for
  each pair `{s, t}`. Equivalent to `ShotUn.Matching.match/1`.
  """
  @spec match([term_pair()] | term_pair()) :: Enumerable.t(UnifSolution.t())
  defdelegate match(pairs), to: Matching

  @doc """
  Returns `{:ok, %UnifSolution{}}` (or `:error`) for a problem in
  Miller's pattern fragment. Equivalent to `ShotUn.Pattern.unify/1`.
  """
  @spec pattern_unify([term_pair()] | term_pair()) :: {:ok, UnifSolution.t()} | :error
  defdelegate pattern_unify(pairs), to: Pattern, as: :unify

  ##############################################################################
  # STRATEGY DISPATCH
  ##############################################################################

  defp dispatch_auto(pairs, depth) do
    cond do
      Fragment.pattern_problem?(pairs) -> pattern_stream(pairs)
      Fragment.matching_problem?(pairs) -> Matching.match(pairs)
      true -> pre_unification(pairs, depth)
    end
  end

  defp pattern_stream(pairs) do
    Stream.unfold(:start, fn
      :start ->
        case Pattern.unify(pairs) do
          {:ok, sol} -> {sol, :done}
          :error -> nil
        end

      :done ->
        nil
    end)
  end

  ##############################################################################
  # PRE-UNIFICATION (existing engine)
  ##############################################################################

  defp pre_unification(term_pairs, depth) do
    Stream.resource(
      fn ->
        TF.start_scratchpad()

        initial_scope =
          for {l_id, r_id} <- term_pairs,
              id <- [l_id, r_id],
              fvar <- TF.get_term!(id).fvars,
              into: MapSet.new(),
              do: fvar

        initial_state = %{pairs: term_pairs, substs: [], flex: [], depth: depth}

        {[initial_state], initial_scope}
      end,
      fn
        {[], _scope} = acc ->
          {:halt, acc}

        {[current | remaining], scope} = acc ->
          case explore_branch([current | remaining]) do
            nil ->
              {:halt, acc}

            {raw_solution, new_stack} ->
              cleaned_solution = clean_solution(raw_solution, scope)
              committed_solution = commit_solution(cleaned_solution)
              {[committed_solution], {new_stack, scope}}
          end
      end,
      fn _acc ->
        TF.stop_scratchpad()
      end
    )
  end

  defp clean_solution(%{substitutions: substs, flex_pairs: flex}, initial_scope) do
    normalized_substs =
      for subst <- substs, MapSet.member?(initial_scope, subst.fvar) do
        %{subst | term_id: Semantics.subst!(substs, subst.term_id)}
      end

    normalized_flex =
      Enum.map(flex, fn {l_id, r_id} ->
        {Semantics.subst!(substs, l_id), Semantics.subst!(substs, r_id)}
      end)

    %UnifSolution{substitutions: normalized_substs, flex_pairs: normalized_flex}
  end

  defp commit_solution(%UnifSolution{substitutions: substs, flex_pairs: flex}) do
    committed_substs =
      Enum.map(substs, fn subst ->
        %{subst | term_id: TF.commit_to_global!(subst.term_id)}
      end)

    committed_flex =
      Enum.map(flex, fn {l_id, r_id} ->
        {TF.commit_to_global!(l_id), TF.commit_to_global!(r_id)}
      end)

    %UnifSolution{substitutions: committed_substs, flex_pairs: committed_flex}
  end

  ##############################################################################
  # MAIN UNIFICATION LOGIC
  ##############################################################################

  @spec explore_branch([search_state()]) :: {UnifSolution.t(), [search_state()]} | nil
  defp explore_branch([]), do: nil

  defp explore_branch([current | remaining]) do
    case step(current) do
      :fail ->
        explore_branch(remaining)

      {:solution, solution} ->
        {solution, remaining}

      {:branch, new_branches} ->
        explore_branch(new_branches ++ remaining)

      {:next, updated_state} ->
        explore_branch([updated_state | remaining])
    end
  end

  @spec step(search_state()) :: step_t()
  defp step(%{depth: 0}), do: :fail

  defp step(%{pairs: [], substs: substs, flex: flex}),
    do: {:solution, %UnifSolution{substitutions: substs, flex_pairs: flex}}

  defp step(%{pairs: [{left_id, right_id} | rest]} = state) do
    # Trivial case
    if left_id == right_id do
      {:next, %{state | pairs: rest}}
    else
      left = TF.get_term!(left_id)
      right = TF.get_term!(right_id)

      evaluate_pair(left, right, state, rest)
    end
  end

  @spec evaluate_pair(Term.t(), Term.t(), search_state(), term_pair()) :: step_t()
  defp evaluate_pair(term_1, term_2, state, rest)

  # Case: incompatible types (we assume monotypes)
  defp evaluate_pair(%Term{type: t1}, %Term{type: t2}, _s, _r) when t1 != t2,
    do: :fail

  # Case: rigid-rigid (constants)
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

  # Case: rigid-rigid (bound variables)
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

  # Case: flex-flex
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs
    {:next, %{state | pairs: rest, flex: [{l_id, r_id} | state.flex]}}
  end

  # Case: bind left
  defp evaluate_pair(
         %Term{head: %{kind: :fv} = var, args: [], bvars: []},
         right,
         state,
         rest
       ),
       do: bind(var, right, state, rest)

  # Case: bind right
  defp evaluate_pair(
         left,
         %Term{head: %{kind: :fv} = var, args: [], bvars: []},
         state,
         rest
       ),
       do: bind(var, left, state, rest)

  # Case: flex-rigid
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :co}}, state, rest),
    do: do_bindings([:imitation, :projection], state, rest)

  # Case: rigid-flex
  defp evaluate_pair(%Term{head: %{kind: :co}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs

    do_bindings(
      [:imitation, :projection],
      %{state | pairs: [{r_id, l_id} | rest]},
      rest
    )
  end

  # Case: flex-bound
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :bv}}, state, rest),
    do: do_bindings([:projection], state, rest)

  # Case: Bound-flex
  defp evaluate_pair(%Term{head: %{kind: :bv}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs
    do_bindings([:projection], %{state | pairs: [{r_id, l_id} | rest]}, rest)
  end

  # Rest cases: incompatible rigid heads etc.
  defp evaluate_pair(_left, _right, _state, _rest), do: :fail

  ##############################################################################
  # FURTHER HELPERS
  ##############################################################################

  defp apply_substitution(new_subst, state, rest_pairs) do
    updated_substs = Semantics.add_subst!(state.substs, new_subst)

    updated_pairs =
      Enum.map(rest_pairs, fn {l_id, r_id} ->
        {Semantics.subst!(new_subst, l_id), Semantics.subst!(new_subst, r_id)}
      end)

    {remaining_flex, migrated_pairs} =
      Enum.reduce(state.flex, {[], []}, fn {l_id, r_id}, {flex_acc, pairs_acc} ->
        new_l = Semantics.subst!(new_subst, l_id)
        new_r = Semantics.subst!(new_subst, r_id)

        l_head_kind = TF.get_term!(new_l).head.kind
        r_head_kind = TF.get_term!(new_r).head.kind

        if l_head_kind == :fv and r_head_kind == :fv do
          {[{new_l, new_r} | flex_acc], pairs_acc}
        else
          {flex_acc, [{new_l, new_r} | pairs_acc]}
        end
      end)

    %{
      state
      | substs: updated_substs,
        pairs: migrated_pairs ++ updated_pairs,
        flex: remaining_flex
    }
  end

  defp bind(var, right_term, state, rest_pairs) do
    if var in right_term.fvars do
      # variable capture
      :fail
    else
      new_subst = Substitution.new(var, right_term.id)
      {:next, apply_substitution(new_subst, state, rest_pairs)}
    end
  end

  # Generates imitation/projection/prim-subst branches and returns them as a
  # list of new states
  defp do_bindings(binding_types, state, rest_pairs) do
    [{flex_id, rigid_id} | _] = state.pairs

    flex_head = TF.get_term!(flex_id).head
    rigid_head = TF.get_term!(rigid_id).head

    substs = Bindings.generic_binding(flex_head, rigid_head, binding_types)

    new_branches =
      Enum.map(substs, fn subst ->
        state
        |> then(&apply_substitution(subst, &1, [{flex_id, rigid_id} | rest_pairs]))
        |> Map.update!(:depth, &(&1 - 1))
      end)

    {:branch, new_branches}
  end
end
