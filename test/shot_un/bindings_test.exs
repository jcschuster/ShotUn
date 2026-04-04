defmodule ShotUn.BindingsTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions

  alias ShotDs.Data.{Declaration, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.Bindings

  test "generic_binding/3 returns one imitation and two projections for a binary flex head" do
    left_head = Declaration.new_free_var("F", type_iii())
    right_head = Declaration.new_const("f", type_iii())

    bindings = Bindings.generic_binding(left_head, right_head, [:imitation, :projection])

    assert length(bindings) == 3
    assert Enum.all?(bindings, &match?(%Substitution{fvar: ^left_head}, &1))
    assert Enum.count(bindings, &imitation?/1) == 1
    assert Enum.count(bindings, &projection?/1) == 2
  end

  test "generic_binding/3 filters out bindings when goals do not match" do
    left_head = Declaration.new_free_var("F", type_iii())
    right_head = Declaration.new_const("f", type_o())

    assert Bindings.generic_binding(left_head, right_head, [:projection]) == []
  end

  defp imitation?(%Substitution{term_id: term_id}) do
    TF.get_term!(term_id).head.kind == :co
  end

  defp projection?(%Substitution{term_id: term_id}) do
    term = TF.get_term!(term_id)
    term.head.kind == :bv and term.args == []
  end
end
