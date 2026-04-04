defmodule ShotUn.UnifSolution do
  @moduledoc """
  Represents a single solution to a unification problem.
  """

  alias ShotDs.Data.Substitution
  alias ShotDs.Data.Term

  defstruct substitutions: [], flex_pairs: []

  @typedoc """
  The type of a pre-unification solution.

  This includes a list of substitutions as well as unresolved flex-flex pairs
  which can be understood as future unification constraints.
  """
  @type t :: %__MODULE__{
          substitutions: [Substitution.t()],
          flex_pairs: [{Term.term_id(), Term.term_id()}]
        }
end

defimpl String.Chars, for: ShotUn.UnifSolution do
  import ShotDs.Util.Formatter

  def to_string(sol) do
    "substitutions: [" <>
      Enum.map_join(sol.substitutions, ", ", &format_substitution(&1, true)) <>
      "]; remaining flex-flex pairs: [" <>
      Enum.map_join(sol.flex_pairs, ", ", fn {a, b} ->
        "#{format_term!(a, true)} =? #{format_term!(b, true)}"
      end) <>
      "]"
  end
end
