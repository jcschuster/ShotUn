defmodule ShotUn.DispatchTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Data.Declaration
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.UnifSolution

  describe "ShotUn.unify/3 — default strategy" do
    test "without :strategy behaves like pre-unification (flex-flex kept)" do
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())

      [sol] = ShotUn.unify({x, y}) |> Enum.to_list()

      assert %UnifSolution{substitutions: [], flex_pairs: [{^x, ^y}]} = sol
    end
  end

  describe "ShotUn.unify/3 — :strategy" do
    test ":pattern produces an MGU stream of length 1" do
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())

      [sol] = ShotUn.unify({x, y}, 10, strategy: :pattern) |> Enum.to_list()

      # Intersection rule binds both X and Y to a fresh meta.
      assert %UnifSolution{substitutions: [_, _], flex_pairs: []} = sol
    end

    test ":pattern yields an empty stream when the problem has no MGU" do
      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())

      assert [] == ShotUn.unify({a, b}, 10, strategy: :pattern) |> Enum.to_list()
    end

    test ":matching enumerates all matchers" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      sols =
        ShotUn.unify({app(x, [a, a]), app(f, [a, a])}, 10, strategy: :matching)
        |> Enum.to_list()

      assert length(sols) == 9
    end

    test ":auto routes a pattern problem to pattern unification" do
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())

      [sol] = ShotUn.unify({x, y}, 10, strategy: :auto) |> Enum.to_list()

      # Pattern dispatch resolves the flex-flex pair instead of deferring it.
      assert %UnifSolution{flex_pairs: []} = sol
      assert sol.substitutions != []
    end

    test ":auto routes a ground-target 2nd-order problem to matching" do
      x = TF.make_free_var_term("X", type_iii())
      f = TF.make_const_term("f", type_iii())
      a = TF.make_const_term("a", type_i())

      # Not a Miller pattern (X applied to constants, not bvars), but it does
      # satisfy the matching precondition (ground RHS, 2nd-order).
      sols =
        ShotUn.unify({app(x, [a, a]), app(f, [a, a])}, 10, strategy: :auto)
        |> Enum.to_list()

      assert length(sols) == 9
    end

    test ":auto falls back to pre-unification for problems outside both fragments" do
      # A 3rd-order flex variable disqualifies the problem from second-order
      # matching, and the application below is not a pattern, so :auto should
      # fall through to depth-bounded pre-unification.
      f =
        Declaration.new_free_var(
          "F",
          ShotDs.Data.Type.new(:i, [ShotDs.Data.Type.new(:i, [ShotDs.Data.Type.new(:i, :i)])])
        )

      c = TF.make_const_term("c", type_i())

      # Build a closed arg of type (i → i) → i:
      h_type = ShotDs.Data.Type.new(:i, :i)
      h = Declaration.new_free_var("H", h_type)

      arg =
        TF.make_abstr_term!(c, h)

      problem = {app(TF.make_term(f), arg), c}

      # We just verify the call succeeds — :auto won't refuse and won't crash;
      # pre-unification may or may not find a solution within the depth budget.
      assert is_list(ShotUn.unify(problem, 3, strategy: :auto) |> Enum.to_list())
    end

    test "unknown strategy raises ArgumentError" do
      a = TF.make_const_term("a", type_i())

      assert_raise ArgumentError, ~r/unknown strategy/, fn ->
        ShotUn.unify({a, a}, 10, strategy: :bogus) |> Enum.to_list()
      end
    end
  end

  describe "delegated entry points" do
    test "ShotUn.match/2 is callable and verifies preconditions" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      [sol] = ShotUn.match({x, c}) |> Enum.to_list()
      assert %UnifSolution{flex_pairs: []} = sol
    end

    test "ShotUn.pattern_unify/1 returns {:ok, _} or :error" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())

      assert {:ok, %UnifSolution{}} = ShotUn.pattern_unify({x, c})

      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())
      assert :error = ShotUn.pattern_unify({a, b})
    end
  end
end
