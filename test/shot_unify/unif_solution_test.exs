defmodule ShotUnify.UnifSolutionTest do
  use ExUnit.Case

  import ShotDs.Hol.Definitions
  alias ShotDs.Data.Substitution
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUnify.UnifSolution

  setup do
    reset_term_pool()
    :ok
  end

  test "string conversion prints substitutions and flex-flex pairs" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())
    a = TF.make_const_term("a", type_i())

    substitution = Substitution.new(TF.get_term(x).head, a)

    solution = %UnifSolution{
      substitutions: [substitution],
      flex_pairs: [{x, y}]
    }

    result = Kernel.to_string(solution)

    assert result =~ "substitutions: ["
    assert result =~ "remaining flex-flex pairs: ["
    assert result =~ "=?"
  end

  defp reset_term_pool do
    case :ets.whereis(:term_pool) do
      :undefined ->
        :ok

      _ ->
        :ets.delete_all_objects(:term_pool)
        :ets.insert(:term_pool, {:id_counter, 0})
    end
  end
end
