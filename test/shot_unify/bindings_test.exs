defmodule ShotUnify.BindingsTest do
  use ExUnit.Case

  alias ShotDs.Data.{Declaration, Substitution, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUnify.Bindings

  setup do
    reset_term_pool()
    :ok
  end

  setup_all do
    i = mk_type(:i, [])
    ii = mk_type(i, [i])
    o = mk_type(:o, [])
    io = mk_type(o, [i])
    ii_ii = mk_type(i, [ii, i])

    {:ok,
     %{
       i: i,
       ii: ii,
       ii_ii: ii_ii,
       o: o,
       io: io
     }}
  end

  test "arity_0", state do
    assert arity(state[:i]) == 0
    assert arity(state[:o]) == 0
  end

  test "arity_1", state do
    assert arity(state[:ii]) == 1
    assert arity(state[:io]) == 1
  end

  test "arity_2", state do
    assert arity(state[:ii_ii]) == 2
  end

  test "arity_3", state do
    assert arity(mk_type(state[:ii_ii], [state[:ii_ii]])) == 3
  end

  defp test_imitation_general(type_a, type_b, expected_a, expected_b) do
    v_x = mk_free_var("x", type_a)
    v_y = mk_const("y", type_b)

    [%Substitution{fvar: left, term_id: right_id} = s] =
      Bindings.generic_binding(v_x, v_y, [:imitation])

    right = TF.get_term(right_id)

    assert left == v_x
    assert get_head(right) == v_y
    assert length(get_bvars(right)) == expected_a
    assert length(get_args(right)) == expected_b
    assert get_head(right) == v_y
    {v_x, v_y, s}
  end

  defp test_projection_general(type_a, type_b, expected_results, expected_bvars \\ 0) do
    v_x = mk_free_var("x", type_a)
    v_y = mk_const("y", type_b)

    results = Bindings.generic_binding(v_x, v_y, [:projection])

    assert length(results) == expected_results

    Enum.map(results, fn %Substitution{fvar: left, term_id: right_id} ->
      right = TF.get_term(right_id)

      assert left == v_x
      assert length(get_bvars(right)) == expected_bvars
      assert bound_head_in_scope?(right)
    end)
  end

  test "imitation_binding_0_0", state do
    test_imitation_general(state[:i], state[:o], 0, 0)
  end

  test "imitation_binding_0_1", state do
    test_imitation_general(state[:i], state[:io], 0, 1)
  end

  test "imitation_binding_1_0", state do
    test_imitation_general(state[:ii], state[:o], 1, 0)
  end

  test "imitation_binding_1_1", state do
    test_imitation_general(state[:ii], state[:io], 1, 1)
  end

  test "imitation_binding_2_0", state do
    test_imitation_general(state[:ii_ii], state[:i], 2, 0)
  end

  test "imitation_binding_2_1", state do
    test_imitation_general(state[:ii_ii], state[:io], 2, 1)
  end

  test "imitation_binding_2_2", state do
    test_imitation_general(state[:ii_ii], state[:ii_ii], 2, 2)
  end

  test "imitation_binding_0_2", state do
    test_imitation_general(state[:i], state[:ii_ii], 0, 2)
  end

  test "imitation_binding_1_2", state do
    test_imitation_general(state[:io], state[:ii_ii], 1, 2)
  end

  test "projection_binding_i-o", state do
    test_projection_general(state[:i], state[:o], 0)
  end

  test "projection_binding_i-i", state do
    test_projection_general(state[:i], state[:i], 0)
  end

  test "projection_binding_i-io", state do
    test_projection_general(state[:i], state[:io], 0)
  end

  test "projection_binding_i-ii", state do
    test_projection_general(state[:i], state[:ii], 0)
  end

  test "projection_binding_ii-o", state do
    test_projection_general(state[:ii], state[:o], 0)
  end

  test "projection_binding_ii-i", state do
    test_projection_general(state[:ii], state[:i], 1, 1)
  end

  test "projection_binding_ii-io", state do
    test_projection_general(state[:ii], state[:io], 0)
  end

  test "projection_binding_ii-ii", state do
    test_projection_general(state[:ii], state[:ii], 1, 1)
  end

  test "projection_binding_ii_ii-i", state do
    test_projection_general(state[:ii_ii], state[:i], 2, 2)
  end

  test "projection_binding_ii_ii-io", state do
    test_projection_general(state[:ii_ii], state[:io], 0)
  end

  test "projection_binding_ii_ii-ii", state do
    test_projection_general(state[:ii_ii], state[:ii], 2, 2)
  end

  test "projection_binding_ii_ii-ii_ii", state do
    test_projection_general(state[:ii_ii], state[:ii_ii], 2, 2)
  end

  test "projection_binding_i-ii_ii", state do
    test_projection_general(state[:i], state[:ii_ii], 0)
  end

  test "projection_binding_io-ii_ii", state do
    test_projection_general(state[:io], state[:ii_ii], 1, 1)
  end

  defp mk_type(goal, args), do: Type.new(goal, args)

  defp mk_free_var(name, type), do: Declaration.new_free_var(name, type)

  defp mk_const(name, type), do: Declaration.new_const(name, type)

  defp arity(type), do: length(type.args)

  defp get_head(term), do: term.head

  defp get_bvars(term), do: term.bvars

  defp get_args(term), do: term.args

  # Bound-variable equality should be checked by scope slot, not raw struct equality.
  # Term construction may normalize names/types while preserving the represented binder slot.
  defp bound_head_in_scope?(term) do
    head = get_head(term)

    case head.kind do
      :bv ->
        head_slot = bound_slot(term, head)

        Enum.any?(get_bvars(term), fn bvar ->
          bound_slot(term, bvar) == head_slot
        end)

      _ ->
        false
    end
  end

  defp bound_slot(term, bound_var) do
    bvars = get_bvars(term)

    exact_index =
      Enum.find_index(bvars, fn bv ->
        bv.name == bound_var.name and bv.type == bound_var.type
      end)

    case exact_index do
      nil ->
        matching_by_type =
          bvars
          |> Enum.with_index()
          |> Enum.filter(fn {bv, _idx} -> bv.type == bound_var.type end)

        case matching_by_type do
          [{_bv, idx}] -> idx
          _ -> term.max_num - bound_var.name
        end

      _ ->
        exact_index
    end
  end

  # Keeps tests isolated and IDs deterministic when inspecting replacement terms.
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
