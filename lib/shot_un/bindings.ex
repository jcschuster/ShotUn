defmodule ShotUn.Bindings do
  @moduledoc false
  alias ShotDs.Data.{Type, Declaration, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF

  @doc """
  Generates imitation and/or projection substitutions for a flex-rigid pair.
  Returns a list of subsitutions.
  """
  @spec generic_binding(Declaration.free_var_t(), Declaration.t(), [:imitation | :projection]) ::
          [Substitution.t()]
  def generic_binding(left_head, right_head, binding_types) do
    left_args = left_head.type.args

    x_vars = Enum.map(left_args, &Declaration.fresh_var(&1))
    x_term_ids = Enum.map(x_vars, &TF.make_term/1)

    for var <- build_head_candidates(right_head, x_vars, binding_types),
        var.type.goal == right_head.type.goal do
      binding = build_binding_term(var, left_args, x_vars, x_term_ids)
      Substitution.new(left_head, binding)
    end
  end

  defp build_head_candidates(right_head, x_vars, binding_types) do
    imitation = if :imitation in binding_types, do: [right_head], else: []
    projection = if :projection in binding_types, do: x_vars, else: []
    imitation ++ projection
  end

  defp build_binding_term(head, left_args, x_vars, x_term_ids) do
    h_vars =
      Enum.map(head.type.args, fn arg_type ->
        h_type = Type.new(arg_type.goal, left_args ++ arg_type.args)
        TF.make_fresh_var_term(h_type)
      end)

    applied_h_ids = Enum.map(h_vars, &TF.fold_apply!(&1, x_term_ids))

    matrix_id = TF.fold_apply!(TF.make_term(head), applied_h_ids)

    List.foldr(x_vars, matrix_id, &TF.make_abstr_term!(&2, &1))
  end
end
