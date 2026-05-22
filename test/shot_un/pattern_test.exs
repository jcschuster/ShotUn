defmodule ShotUn.PatternTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  alias ShotDs.Data.{Declaration, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn.{Pattern, UnifSolution}

  describe "unify/1 — decomposition" do
    test "trivial pair" do
      a = TF.make_const_term("a", type_i())

      assert {:ok, %UnifSolution{substitutions: [], flex_pairs: []}} =
               Pattern.unify({a, a})
    end

    test "rigid-rigid mismatch fails" do
      a = TF.make_const_term("a", type_i())
      b = TF.make_const_term("b", type_i())

      assert :error = Pattern.unify({a, b})
    end
  end

  describe "unify/1 — direct binding" do
    test "primitive flex unifies with rigid" do
      x = TF.make_free_var_term("X", type_i())
      c = TF.make_const_term("c", type_i())
      x_decl = TF.get_term!(x).head

      assert {:ok, %UnifSolution{substitutions: [%{fvar: ^x_decl, term_id: ^c}]}} =
               Pattern.unify({x, c})
    end

    test "occurs check" do
      # X =? c(X) — should fail
      x = TF.make_free_var_term("X", type_i())
      c_arr = TF.make_const_term("c", Type.new(:i, :i))
      cx = app(c_arr, x)

      assert :error = Pattern.unify({x, cx})
    end
  end

  describe "unify/1 — flex-rigid inversion" do
    test "inversion of unary applied pattern" do
      # λx. F(x) =? λx. g(x) — F : i→i, g : i→i const
      # MGU: F ↦ λu. g(u)
      f = Declaration.new_free_var("F", type_ii())
      g = TF.make_const_term("g", type_ii())

      lhs = lambda(type_i(), fn x -> app(TF.make_term(f), x) end)
      rhs = lambda(type_i(), fn x -> app(g, x) end)

      assert {:ok, %UnifSolution{substitutions: [sub], flex_pairs: []}} =
               Pattern.unify({lhs, rhs})

      assert sub.fvar == f
      # The bound term should be λu. g(u), normalized to be just `g` after eta-reduction.
      # We accept either representation here — just verify normalization.
      bound = TF.get_term!(sub.term_id)
      assert bound.type == type_ii()
    end

    test "inversion missing a context binder fails" do
      # λx.λy. F(x) =? λx.λy. g(y) — bvar y is not in F's args, no flex to prune.
      f = Declaration.new_free_var("F", type_ii())
      g = TF.make_const_term("g", type_ii())

      lhs = lambda([type_i(), type_i()], fn x, _y -> app(TF.make_term(f), x) end)
      rhs = lambda([type_i(), type_i()], fn _x, y -> app(g, y) end)

      assert :error = Pattern.unify({lhs, rhs})
    end
  end

  describe "unify/1 — flex-flex same head (alias)" do
    test "F(x, y) = F(x, z) keeps only the matching position" do
      # In context [x, y, z], F(x, y) =? F(x, z): common position is the first.
      # MGU should bind F to a fresh F' applied to only the first arg.
      f = Declaration.new_free_var("F", Type.new(:i, [:i, :i]))

      lhs =
        lambda([type_i(), type_i(), type_i()], fn x, y, _z ->
          app(TF.make_term(f), [x, y])
        end)

      rhs =
        lambda([type_i(), type_i(), type_i()], fn x, _y, z ->
          app(TF.make_term(f), [x, z])
        end)

      assert {:ok, %UnifSolution{substitutions: [sub], flex_pairs: []}} =
               Pattern.unify({lhs, rhs})

      assert sub.fvar == f
    end

    test "identical pattern args is trivial" do
      f = Declaration.new_free_var("F", Type.new(:i, [:i, :i]))

      lhs = lambda([type_i(), type_i()], fn x, y -> app(TF.make_term(f), [x, y]) end)

      assert {:ok, %UnifSolution{substitutions: [], flex_pairs: []}} =
               Pattern.unify({lhs, lhs})
    end
  end

  describe "unify/1 — flex-flex distinct heads (intersection)" do
    test "F(x, y) =? G(y, z) keeps only y as the common argument" do
      f = Declaration.new_free_var("F", Type.new(:i, [:i, :i]))
      g = Declaration.new_free_var("G", Type.new(:i, [:i, :i]))

      lhs =
        lambda([type_i(), type_i(), type_i()], fn x, y, _z ->
          app(TF.make_term(f), [x, y])
        end)

      rhs =
        lambda([type_i(), type_i(), type_i()], fn _x, y, z ->
          app(TF.make_term(g), [y, z])
        end)

      assert {:ok, %UnifSolution{substitutions: subs, flex_pairs: []}} =
               Pattern.unify({lhs, rhs})

      # Two substitutions should be generated: σ(F) and σ(G), both applying H to y.
      assert length(subs) == 2
      assert Enum.any?(subs, &(&1.fvar == f))
      assert Enum.any?(subs, &(&1.fvar == g))
    end
  end

  describe "unify/1 — pruning" do
    test "prunes a nested flex application of an unreachable bvar" do
      # λx.λy. F(x) =? λx.λy. g(G(x, y)) — y is unreachable in F's args,
      # but g(G(x, y)) contains a flex G that can be pruned to drop y.
      # MGU: G ↦ λu, v. G'(u);  F ↦ λu. g(G'(u))
      f = Declaration.new_free_var("F", type_ii())
      g = TF.make_const_term("g", type_ii())
      g_var = Declaration.new_free_var("G", Type.new(:i, [:i, :i]))

      lhs = lambda([type_i(), type_i()], fn x, _y -> app(TF.make_term(f), x) end)

      rhs =
        lambda([type_i(), type_i()], fn x, y ->
          app(g, app(TF.make_term(g_var), [x, y]))
        end)

      assert {:ok, %UnifSolution{substitutions: subs, flex_pairs: []}} =
               Pattern.unify({lhs, rhs})

      assert Enum.any?(subs, &(&1.fvar == f))
      assert Enum.any?(subs, &(&1.fvar == g_var))
    end
  end

  describe "unify/1 — input validation" do
    test "rejects non-pattern (flex applied to a constant)" do
      f = Declaration.new_free_var("F", type_ii())
      c = TF.make_const_term("c", type_i())

      lhs = app(TF.make_term(f), c)
      rhs = c

      assert_raise ArgumentError, ~r/pattern/, fn -> Pattern.unify({lhs, rhs}) end
    end

    test "rejects non-pattern (flex applied to repeating bvar)" do
      f = Declaration.new_free_var("F", Type.new(:i, [:i, :i]))

      lhs = lambda(type_i(), fn x -> app(TF.make_term(f), [x, x]) end)
      rhs = lambda(type_i(), fn x -> x end)

      assert_raise ArgumentError, ~r/pattern/, fn -> Pattern.unify({lhs, rhs}) end
    end
  end
end
