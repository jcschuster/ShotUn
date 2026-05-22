defmodule ShotUn.Fragment do
  @moduledoc """
  Predicates that classify a unification problem into one of the decidable
  fragments handled by `ShotUn.Pattern` (Miller patterns) and
  `ShotUn.Matching` (Huet second-order matching), plus a helper for
  computing the order of a simple type.
  """

  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal

  @typep term_pair :: {Term.term_id(), Term.term_id()}

  @doc """
  Returns the order of a simple type.

  $$\\text{order}(\\beta) = 0 \\quad\\text{for base } \\beta$$
  $$\\text{order}(\\tau_1 \\to \\dots \\to \\tau_n \\to \\beta) =
    \\max_{i}(\\text{order}(\\tau_i) + 1)$$
  """
  @spec type_order(Type.t()) :: non_neg_integer()
  def type_order(%Type{args: []}), do: 0

  def type_order(%Type{args: args}) do
    args
    |> Enum.map(&(type_order(&1) + 1))
    |> Enum.max()
  end

  @doc """
  Returns `true` when the term has no free variables.
  """
  @spec ground?(Term.term_id()) :: boolean()
  def ground?(term_id) when is_integer(term_id) do
    Enum.empty?(TF.get_term!(term_id).fvars)
  end

  @doc """
  Returns `true` when every free variable, constant and bound variable
  appearing in the term has a type of order at most `max_order`.
  """
  @spec bounded_order?(Term.term_id(), non_neg_integer()) :: boolean()
  def bounded_order?(term_id, max_order) when is_integer(term_id) do
    {ok?, _cache} =
      TermTraversal.fold_term!(term_id, fn term, arg_results ->
        Enum.all?(arg_results) and
          type_order(term.type) <= max_order and
          Enum.all?(term.bvars, &(type_order(&1.type) <= max_order)) and
          Enum.all?(term.fvars, &(type_order(&1.type) <= max_order)) and
          Enum.all?(term.consts, &(type_order(&1.type) <= max_order))
      end)

    ok?
  end

  @doc """
  Returns `true` when the term is a higher-order pattern: every
  occurrence of a free variable is applied to a list of pairwise distinct
  bound-variable arguments.
  """
  @spec pattern?(Term.term_id()) :: boolean()
  def pattern?(term_id) when is_integer(term_id) do
    {ok?, _cache} = TermTraversal.fold_term!(term_id, &pattern_fold/2)
    ok?
  end

  defp pattern_fold(%Term{head: %Declaration{kind: :fv}, args: args}, arg_results) do
    Enum.all?(arg_results) and distinct_bvar_args?(args)
  end

  defp pattern_fold(_term, arg_results), do: Enum.all?(arg_results)

  defp distinct_bvar_args?(arg_ids) do
    indices = Enum.map(arg_ids, &outer_bvar_index/1)

    Enum.all?(indices, &(&1 != :not_bvar)) and length(Enum.uniq(indices)) == length(indices)
  end

  @doc """
  If the term is the eta-long primitive of a single bound variable whose
  binder lies in the surrounding context (i.e. above the term's own
  abstractions), returns the index of that binder relative to the
  surrounding context. Otherwise returns `:not_bvar`.
  """
  @spec outer_bvar_index(Term.term_id()) :: pos_integer() | :not_bvar
  def outer_bvar_index(term_id) when is_integer(term_id) do
    term = TF.get_term!(term_id)
    local = length(term.bvars)

    with {:ok, true} <- TF.primitive_term?(term_id),
         %Declaration{kind: :bv, name: name} <- term.head,
         true <- name > local do
      name - local
    else
      _ -> :not_bvar
    end
  end

  @doc """
  Returns `true` when every side of every pair is a higher-order pattern.
  """
  @spec pattern_problem?([term_pair()]) :: boolean()
  def pattern_problem?(pairs) when is_list(pairs) do
    Enum.all?(pairs, fn {l, r} -> pattern?(l) and pattern?(r) end)
  end

  @doc """
  Returns `true` when every right-hand side is ground and every type in
  the problem has order at most 2 (Huet's second-order fragment).
  """
  @spec matching_problem?([term_pair()]) :: boolean()
  def matching_problem?(pairs) when is_list(pairs) do
    Enum.all?(pairs, fn {l, r} ->
      ground?(r) and bounded_order?(l, 2) and bounded_order?(r, 2)
    end)
  end
end
