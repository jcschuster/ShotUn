defmodule ShotUnify.Bindings do
  alias ShotDs.Data.{Type, Declaration, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF

  @doc """
  Generates imitation and/or projection substitutions for a flex-rigid pair.
  Returns a list of subsitutions.
  """
  @spec generic_binding(Declaration.free_var_t(), Declaration.t(), [:imitation | :projection]) ::
          [Substitution.t()]
  def generic_binding(left_head, right_head, binding_types) do
    left_type = left_head.type
    left_inputs = left_type.args

    left_arity = length(left_type.args)

    x_vars =
      if left_arity == 0 do
        []
      else
        0..(left_arity - 1)
        |> Enum.map(fn n -> Declaration.fresh_var(Enum.at(left_inputs, n)) end)
      end

    x_vars_terms = Enum.map(x_vars, &TF.make_term/1)

    vars_to_use =
      case {:imitation in binding_types, :projection in binding_types} do
        {true, true} -> [right_head | x_vars]
        {true, false} -> [right_head]
        {false, true} -> x_vars
        _ -> []
      end
      |> Enum.filter(fn var ->
        var.type.goal == right_head.type.goal
      end)

    bindings_right_side =
      Enum.map(vars_to_use, fn var ->
        generic_binding_inner(var, left_inputs, x_vars, x_vars_terms)
      end)

    results =
      Enum.map(bindings_right_side, fn binding ->
        Substitution.new(left_head, binding)
      end)

    results
  end

  defp generic_binding_inner(inner_var, left_inputs, x_vars, x_vars_terms) do
    to_use_type = inner_var.type
    to_use_inputs = to_use_type.args
    to_use_arity = length(to_use_type.args)

    h_vars =
      if to_use_arity == 0 do
        []
      else
        0..(to_use_arity - 1)
        |> Enum.map(fn n ->
          h_type = %Type{
            goal: Enum.at(to_use_inputs, n).goal,
            args: left_inputs ++ Enum.at(to_use_inputs, n).args
          }

          TF.make_term(Declaration.fresh_var(h_type))
        end)
      end

    # Apply x_vars to all h_vars
    applied_h_vars = apply_list_to_list(h_vars, x_vars_terms)

    # Apply applied_h_vars to inner_var
    final_stack = apply_list(TF.make_term(inner_var), applied_h_vars)

    # Add Abstractions
    final_binding =
      Enum.reduce(Enum.reverse(x_vars), final_stack, fn x, acc ->
        TF.make_abstr_term(acc, x)
      end)

    final_binding
  end

  defp apply_list_to_list(start_vars, to_apply) do
    if Enum.empty?(to_apply) do
      start_vars
    else
      Enum.map(start_vars, fn h ->
        apply_list(h, to_apply)
      end)
    end
  end

  defp apply_list(start_var, to_apply) do
    Enum.reduce(to_apply, start_var, fn x, acc -> TF.make_appl_term(acc, x) end)
  end
end
