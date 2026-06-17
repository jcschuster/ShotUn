defmodule ShotUn.Trace.Node do
  @moduledoc """
  A single node in a `ShotUn.Trace` decision tree.

  Each node represents the state reached after applying `rule` to its
  parent's state. The root has `kind: :start`, `rule: :init` and no
  parent; leaves are either `:solution` or `:fail`. All term-bearing
  fields are pre-formatted strings captured while the term-factory
  scratchpad was alive, so the tree remains meaningful after the
  algorithm tears down its scratchpad.
  """

  @type kind :: :start | :step | :solution | :fail

  defstruct id: nil,
            parent_id: nil,
            kind: nil,
            rule: nil,
            pairs: [],
            substs: [],
            flex: [],
            depth: nil,
            note: nil,
            children: []

  @type t :: %__MODULE__{
          id: non_neg_integer(),
          parent_id: non_neg_integer() | nil,
          kind: kind(),
          rule: atom() | nil,
          pairs: [{String.t(), String.t()}],
          substs: [String.t()],
          flex: [{String.t(), String.t()}],
          depth: non_neg_integer() | nil,
          note: String.t() | nil,
          children: [t()]
        }
end

defmodule ShotUn.Trace do
  @moduledoc """
  Decision-tree trace produced by `ShotUn.unify/3`, `ShotUn.match/2` and
  `ShotUn.pattern_unify/2` when invoked with `vis: true`. Each node
  records the rule applied, the resulting work-list, the accumulated
  substitutions and the deferred flex-flex pairs (pre-formatted as
  strings). Render the tree with `ShotUn.Trace.Mermaid.render/2`.

  The traces returned by the public entry points are pre-pruned to the
  paths from the root to a `:solution` leaf — failed branches and
  dead-end intermediate steps are dropped. Use `prune_to_solutions/1`
  directly if you have an unpruned trace from a lower-level call.
  """

  alias ShotUn.Trace.Node

  @type algorithm :: :pre_unification | :matching | :pattern

  defstruct algorithm: :pre_unification, root: nil

  @type t :: %__MODULE__{algorithm: algorithm(), root: Node.t() | nil}

  @doc """
  Returns a trace that retains only the nodes lying on a path from the
  root to a `:solution` leaf. The root node is always preserved (even if
  no solution was reached) so the diagram still shows the initial state.
  """
  @spec prune_to_solutions(t()) :: t()
  def prune_to_solutions(%__MODULE__{root: nil} = trace), do: trace

  def prune_to_solutions(%__MODULE__{root: root} = trace) do
    %{trace | root: prune_node_keep_root(root)}
  end

  defp prune_node_keep_root(%Node{children: children} = node) do
    pruned =
      children
      |> Enum.map(&prune_subtree/1)
      |> Enum.reject(&is_nil/1)

    %{node | children: pruned}
  end

  defp prune_subtree(%Node{kind: :solution} = node), do: node

  defp prune_subtree(%Node{kind: :fail}), do: nil

  defp prune_subtree(%Node{children: children} = node) do
    pruned =
      children
      |> Enum.map(&prune_subtree/1)
      |> Enum.reject(&is_nil/1)

    case pruned do
      [] -> nil
      kept -> %{node | children: kept}
    end
  end
end
