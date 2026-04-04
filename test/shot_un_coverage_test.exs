defmodule ShotUnCoverageTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.UnifSolution

  test "rejects impossible problems and depth exhaustion" do
    assert_no_solutions(
      {TF.make_free_var_term("X", type_i()), TF.make_free_var_term("Y", type_i())},
      0
    )

    assert_no_solutions({TF.make_const_term("a", type_i()), true_term()}, 3)
    assert_no_solutions({TF.make_const_term("a", type_i()), TF.make_const_term("b", type_i())}, 3)
  end

  test "returns empty solutions for empty and trivial problems" do
    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUn.unify([], 3))

    a = TF.make_const_term("a", type_i())

    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUn.unify({a, a}, 3))
  end

  test "enforces occurs-check for direct bindings" do
    x = TF.make_free_var_term("X", type_i())
    x_head = TF.get_term!(x).head

    right =
      TF.memoize(%Term{
        id: 0,
        head: Declaration.new_const("c", type_i()),
        args: [],
        bvars: [],
        type: type_i(),
        fvars: [x_head],
        max_num: 0
      })

    assert [] == Enum.to_list(ShotUn.unify({x, right}, 3))
  end

  test "migrates old flex pairs back into the work list after substitution" do
    x = TF.make_free_var_term("X", type_i())
    y = TF.make_free_var_term("Y", type_i())
    a = TF.make_const_term("a", type_i())

    solutions = Enum.to_list(ShotUn.unify([{x, y}, {x, a}], 5))

    assert Enum.any?(solutions, fn %UnifSolution{substitutions: substs, flex_pairs: []} ->
             Enum.any?(substs, &(&1.fvar.name == "X" and &1.term_id == a)) and
               Enum.any?(substs, &(&1.fvar.name == "Y" and &1.term_id == a))
           end)
  end

  test "decomposes compatible rigid bound heads and rejects mismatched arity" do
    t1 = mk_bv_term(1, 3, type_i())
    t2 = mk_bv_term(2, 4, type_i())

    assert [%UnifSolution{substitutions: [], flex_pairs: []}] =
             Enum.to_list(ShotUn.unify({t1, t2}, 3))

    a = TF.make_const_term("a", type_i())
    c = Declaration.new_const("h", Type.new(:i, [:i, :i]))

    t1 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    t2 =
      TF.memoize(%Term{
        id: 0,
        head: c,
        args: [a, a],
        bvars: [],
        type: type_i(),
        fvars: [],
        max_num: 0
      })

    assert_raise RuntimeError, ~r/ArgumentError: can only decompose terms/, fn ->
      Enum.to_list(ShotUn.unify({t1, t2}, 3))
    end
  end

  test "tuple and list input forms behave the same" do
    x = TF.make_free_var_term("X", type_i())
    a = TF.make_const_term("a", type_i())

    tuple_solutions = Enum.to_list(ShotUn.unify({x, a}, 3))
    list_solutions = Enum.to_list(ShotUn.unify([{x, a}], 3))

    assert Enum.map(tuple_solutions, &Kernel.to_string/1) ==
             Enum.map(list_solutions, &Kernel.to_string/1)
  end

  test "flex and bound pairs still branch" do
    x = TF.make_const_term("x", type_i())
    fx = mk_flex_appl_term("F", Type.new(:i, :i), x, type_i())
    c = TF.make_const_term("c", type_i())
    b = mk_bv_term(1, 1, type_i())

    assert [_ | _] = Enum.to_list(ShotUn.unify({fx, c}, 3))
    assert [_ | _] = Enum.to_list(ShotUn.unify({c, fx}, 3))
    assert is_list(Enum.to_list(ShotUn.unify({fx, b}, 3)))
    assert is_list(Enum.to_list(ShotUn.unify({b, fx}, 3)))
  end

  test "higher-order projection resolves transitive dependencies" do
    a = TF.make_const_term("a", type_i())
    g = TF.make_const_term("g", type_ii())
    f_var = TF.make_free_var_term("F", Type.new(:i, type_ii()))

    t1 = app(f_var, g)
    t2 = app(g, a)

    solutions = ShotUn.unify({t1, t2}) |> Enum.to_list()

    assert not Enum.empty?(solutions)

    valid_projection_found =
      Enum.any?(solutions, fn sol ->
        if length(sol.substitutions) != 1, do: false, else: true

        subst = hd(sol.substitutions)
        normalized_term = TF.get_term!(subst.term_id)

        Enum.empty?(normalized_term.fvars) and subst.fvar.name == "F"
      end)

    assert valid_projection_found
  end

  defp assert_no_solutions(problem, depth) do
    assert [] == Enum.to_list(ShotUn.unify(problem, depth))
  end

  defp mk_bv_term(name, max_num, type) do
    bv = Declaration.new_bound_var(name, type)

    TF.memoize(%Term{
      id: 0,
      head: bv,
      args: [],
      bvars: [],
      type: type,
      fvars: [],
      max_num: max_num
    })
  end

  defp mk_flex_appl_term(name, head_type, arg_id, result_type) do
    head = Declaration.new_free_var(name, head_type)
    arg_term = TF.get_term!(arg_id)

    TF.memoize(%Term{
      id: 0,
      head: head,
      args: [arg_id],
      bvars: [],
      type: result_type,
      fvars: Enum.uniq([head | arg_term.fvars]),
      max_num: arg_term.max_num
    })
  end
end
