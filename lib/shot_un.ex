defmodule ShotUn do
  @moduledoc """
  Higher-order unification for the data structures and semantics of
  [ShotDs](https://hexdocs.pm/shot_ds/readme.html).

  Three algorithms are available:

    * `unify/3` (default) — depth-bounded *pre-unification* (Huet 1975):
      handles arbitrary higher-order problems but is a semi-decision
      procedure; flex-flex pairs are returned as constraints.
    * `pattern_unify/2` — *Miller pattern unification* (Miller 1991): a
      decidable, unitary fragment in which every flex variable is applied
      only to distinct bound variables. Returns at most one MGU.
    * `match/2` — *Huet second-order matching*: the right-hand side is
      ground, every variable in the problem has type of order ≤ 2.
      Returns the complete (lazy) stream of matchers without a depth
      bound.

  `unify/3` accepts a `:strategy` option (`:pre_unification`, `:auto`,
  `:pattern`, `:matching`). With `:auto`, the problem is inspected and
  routed to the most specific decidable algorithm it falls into:

    * if every pair is a pattern → `pattern_unify/2`,
    * otherwise if it satisfies the matching precondition → `match/2`,
    * otherwise pre-unification.

  See `ShotUn.Pattern`, `ShotUn.Matching` and `ShotUn.Fragment` for
  details on the individual algorithms and the fragment classifiers.

  ## Visualisation

  Every public entry point accepts a `vis: true` option that wraps the
  result in a `{result, %ShotUn.Trace{}}` tuple. The trace is a tree of
  `ShotUn.Trace.Node` records covering only the paths from the initial
  state to a `:solution` leaf — failed branches and dead-end steps are
  pruned out before the tuple is returned. Render with
  `ShotUn.Trace.Mermaid.render/2`. When `vis: true` the search is
  materialised eagerly (the lazy `Stream` is consumed before the call
  returns) so that the trace is complete.
  """

  alias ShotDs.Data.{Substitution, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  alias ShotUn.{Bindings, Fragment, Internal, Matching, Pattern, Tracer, UnifSolution}

  @typep term_pair :: {Term.term_id(), Term.term_id()}
  @typep search_state :: %{
           pairs: [term_pair()],
           substs: [Substitution.t()],
           flex: [term_pair()],
           depth: non_neg_integer(),
           trace_id: non_neg_integer() | nil
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
    * `:vis` — when `true`, returns `{stream, %ShotUn.Trace{}}` instead
      of a bare stream. Defaults to `false`.

  Returns a lazy `Stream` of `ShotUn.UnifSolution` structs, or — under
  `vis: true` — a `{stream, trace}` tuple in which the stream contains
  the same solutions but is fully materialised before the call returns.
  """
  @spec unify([term_pair()] | term_pair(), non_neg_integer(), keyword()) ::
          Enumerable.t(UnifSolution.t())
          | {Enumerable.t(UnifSolution.t()), ShotUn.Trace.t()}
  def unify(term_pairs, depth \\ 10, opts \\ [])

  def unify({t1, t2} = pair, depth, opts) when is_integer(t1) and is_integer(t2),
    do: unify([pair], depth, opts)

  def unify(term_pairs, depth, opts) when is_list(term_pairs) do
    strategy = Keyword.get(opts, :strategy, :pre_unification)
    vis? = Keyword.get(opts, :vis, false)

    resolved =
      case strategy do
        :auto -> resolve_auto(term_pairs)
        other when other in [:pre_unification, :pattern, :matching] -> other
        other -> raise ArgumentError, "unknown strategy: #{inspect(other)}"
      end

    dispatch(resolved, term_pairs, depth, vis?)
  end

  @doc """
  Returns the (lazy) stream of all matchers σ such that σ(s) ≡_βη t for
  each pair `{s, t}`. With `vis: true`, returns `{stream, trace}`.
  Equivalent to `ShotUn.Matching.match/2`.
  """
  @spec match([term_pair()] | term_pair(), keyword()) ::
          Enumerable.t(UnifSolution.t())
          | {Enumerable.t(UnifSolution.t()), ShotUn.Trace.t()}
  def match(pairs, opts \\ []), do: Matching.match(pairs, opts)

  @doc """
  Returns `{:ok, %UnifSolution{}}` (or `:error`) for a problem in
  Miller's pattern fragment. With `vis: true`, returns
  `{result, trace}`. Equivalent to `ShotUn.Pattern.unify/2`.
  """
  @spec pattern_unify([term_pair()] | term_pair(), keyword()) ::
          {:ok, UnifSolution.t()}
          | :error
          | {{:ok, UnifSolution.t()} | :error, ShotUn.Trace.t()}
  def pattern_unify(pairs, opts \\ []), do: Pattern.unify(pairs, opts)

  ##############################################################################
  # STRATEGY DISPATCH
  ##############################################################################

  defp resolve_auto(pairs) do
    cond do
      Fragment.pattern_problem?(pairs) -> :pattern
      Fragment.matching_problem?(pairs) -> :matching
      true -> :pre_unification
    end
  end

  defp dispatch(:pre_unification, pairs, depth, false), do: pre_unification(pairs, depth)
  defp dispatch(:pre_unification, pairs, depth, true), do: pre_unification_with_vis(pairs, depth)
  defp dispatch(:pattern, pairs, _depth, false), do: pattern_stream(pairs)
  defp dispatch(:pattern, pairs, _depth, true), do: pattern_stream_with_vis(pairs)
  defp dispatch(:matching, pairs, _depth, false), do: Matching.match(pairs)
  defp dispatch(:matching, pairs, _depth, true), do: Matching.match(pairs, vis: true)

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

  defp pattern_stream_with_vis(pairs) do
    {result, trace} = Pattern.unify(pairs, vis: true)

    solutions =
      case result do
        {:ok, sol} -> [sol]
        :error -> []
      end

    {Stream.concat([solutions]), trace}
  end

  defp pre_unification_with_vis(pairs, depth) do
    Tracer.start()

    try do
      solutions = pre_unification(pairs, depth) |> Enum.to_list()
      trace = :pre_unification |> Tracer.collect() |> ShotUn.Trace.prune_to_solutions()
      {Stream.concat([solutions]), trace}
    after
      Tracer.stop()
    end
  end

  ##############################################################################
  # PRE-UNIFICATION ENGINE
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

        root_id =
          Tracer.record(nil, fn ->
            %{
              kind: :start,
              rule: :init,
              pairs: Tracer.format_pairs(term_pairs),
              substs: [],
              flex: [],
              depth: depth
            }
          end)

        initial_state = %{
          pairs: term_pairs,
          substs: [],
          flex: [],
          depth: depth,
          trace_id: root_id
        }

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
  defp step(%{depth: 0, trace_id: parent}) do
    _ = Tracer.record_fail(parent, :depth_exhausted)
    :fail
  end

  defp step(%{pairs: [], substs: substs, flex: flex, trace_id: parent}) do
    _ =
      Tracer.record(parent, fn ->
        %{
          kind: :solution,
          rule: :solved,
          substs: Tracer.format_substs(substs),
          flex: Tracer.format_pairs(flex)
        }
      end)

    {:solution, %UnifSolution{substitutions: substs, flex_pairs: flex}}
  end

  defp step(%{pairs: [{left_id, right_id} | rest]} = state) do
    if left_id == right_id do
      new_id =
        Tracer.record(state.trace_id, fn ->
          %{
            kind: :step,
            rule: :trivial,
            pairs: Tracer.format_pairs(rest),
            substs: Tracer.format_substs(state.substs),
            flex: Tracer.format_pairs(state.flex),
            depth: state.depth,
            note: Tracer.format_term(left_id)
          }
        end)

      {:next, %{state | pairs: rest, trace_id: new_id}}
    else
      left = TF.get_term!(left_id)
      right = TF.get_term!(right_id)

      evaluate_pair(left, right, state, rest)
    end
  end

  @spec evaluate_pair(Term.t(), Term.t(), search_state(), [term_pair()]) :: step_t()
  defp evaluate_pair(term_1, term_2, state, rest)

  # Case: incompatible types (we assume monotypes)
  defp evaluate_pair(%Term{type: t1}, %Term{type: t2}, state, _rest) when t1 != t2,
    do: fail(state, :type_mismatch, "#{inspect(t1)} vs #{inspect(t2)}")

  # Case: rigid-rigid (constants)
  defp evaluate_pair(
         %Term{head: %{kind: :co} = c} = left,
         %Term{head: %{kind: :co} = c} = right,
         state,
         rest
       ) do
    case Internal.decompose(left, right) do
      {:ok, new_pairs} ->
        record_step_next(:decompose_const, new_pairs ++ rest, state, to_string(c.name))

      :error ->
        fail(state, :no_decompose, "head=#{c.name}")
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
        {:ok, new_pairs} -> record_step_next(:decompose_bv, new_pairs ++ rest, state, nil)
        :error -> fail(state, :no_decompose)
      end
    else
      fail(state, :rigid_clash, "different bound-variable slots")
    end
  end

  # Case: flex-flex
  defp evaluate_pair(%Term{head: %{kind: :fv}}, %Term{head: %{kind: :fv}}, state, rest) do
    [{l_id, r_id} | _] = state.pairs
    new_flex = [{l_id, r_id} | state.flex]

    new_id =
      Tracer.record(state.trace_id, fn ->
        %{
          kind: :step,
          rule: :flex_flex,
          pairs: Tracer.format_pairs(rest),
          substs: Tracer.format_substs(state.substs),
          flex: Tracer.format_pairs(new_flex),
          depth: state.depth,
          note: "deferred " <> Tracer.format_term(l_id) <> " =? " <> Tracer.format_term(r_id)
        }
      end)

    {:next, %{state | pairs: rest, flex: new_flex, trace_id: new_id}}
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
  defp evaluate_pair(_left, _right, state, _rest), do: fail(state, :rigid_clash)

  ##############################################################################
  # FURTHER HELPERS
  ##############################################################################

  defp record_step_next(rule, next_pairs, state, note) do
    new_id =
      Tracer.record(state.trace_id, fn ->
        %{
          kind: :step,
          rule: rule,
          pairs: Tracer.format_pairs(next_pairs),
          substs: Tracer.format_substs(state.substs),
          flex: Tracer.format_pairs(state.flex),
          depth: state.depth,
          note: note
        }
      end)

    {:next, %{state | pairs: next_pairs, trace_id: new_id}}
  end

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
      fail(state, :occurs, "#{var.name} occurs in target")
    else
      new_subst = Substitution.new(var, right_term.id)
      new_state = apply_substitution(new_subst, state, rest_pairs)
      new_id = Tracer.record(state.trace_id, build_bind_attrs(new_state, new_subst))
      {:next, %{new_state | trace_id: new_id}}
    end
  end

  defp build_bind_attrs(new_state, new_subst) do
    fn ->
      %{
        kind: :step,
        rule: :bind,
        pairs: Tracer.format_pairs(new_state.pairs),
        substs: Tracer.format_substs(new_state.substs),
        flex: Tracer.format_pairs(new_state.flex),
        depth: new_state.depth,
        note: Tracer.format_subst(new_subst)
      }
    end
  end

  defp fail(state, rule) do
    _ = Tracer.record_fail(state.trace_id, rule)
    :fail
  end

  defp fail(state, rule, note) do
    _ = Tracer.record_fail(state.trace_id, rule, note)
    :fail
  end

  # Generates imitation/projection branches and returns them as a list of new
  # states, each carrying its own trace_id pointing at the recorded child.
  defp do_bindings(binding_types, state, rest_pairs) do
    [{flex_id, rigid_id} | _] = state.pairs

    flex_head = TF.get_term!(flex_id).head
    rigid_head = TF.get_term!(rigid_id).head

    substs = Bindings.generic_binding(flex_head, rigid_head, binding_types)

    case substs do
      [] ->
        fail(state, :dead_end, "no #{Enum.join(binding_types, "/")} candidate matches goal type")

      _ ->
        new_branches =
          Enum.map(substs, &build_binding_branch(&1, state, flex_id, rigid_id, rigid_head, rest_pairs))

        {:branch, new_branches}
    end
  end

  defp build_binding_branch(subst, state, flex_id, rigid_id, rigid_head, rest_pairs) do
    branch_state =
      state
      |> then(&apply_substitution(subst, &1, [{flex_id, rigid_id} | rest_pairs]))
      |> Map.update!(:depth, &(&1 - 1))

    new_id =
      Tracer.record(state.trace_id, build_branch_attrs(branch_state, subst, rigid_head))

    %{branch_state | trace_id: new_id}
  end

  defp build_branch_attrs(branch_state, subst, rigid_head) do
    fn ->
      %{
        kind: :step,
        rule: classify_binding(subst, rigid_head),
        pairs: Tracer.format_pairs(branch_state.pairs),
        substs: Tracer.format_substs(branch_state.substs),
        flex: Tracer.format_pairs(branch_state.flex),
        depth: branch_state.depth,
        note: Tracer.format_subst(subst)
      }
    end
  end

  defp classify_binding(subst, rigid_head) do
    case TF.get_term!(subst.term_id) do
      %Term{head: head} when head == rigid_head -> :imitation
      _ -> :projection
    end
  end
end
