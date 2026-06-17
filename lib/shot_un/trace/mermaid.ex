defmodule ShotUn.Trace.Mermaid do
  @moduledoc """
  Renders a `ShotUn.Trace` as a Mermaid `graph TD` diagram.

  Edge styling mirrors `ShotTx.Proof.to_mermaid/2`: branching choice
  points (multiple children) use solid arrows (`==>`); linear
  continuations use dotted arrows (`-.->`). Node colours encode the
  node kind — start (blue), step (gray), solution (green), fail
  (orange).

  ## Options

    * `:show_state` — include the work-list (and accumulated σ for
      solution leaves) in each node's label. Defaults to `true`.
    * `:max_pair_chars` — truncate each side of a pair to this many
      characters. Defaults to `40`.
  """

  alias ShotUn.Trace
  alias ShotUn.Trace.Node

  @header """
  %%{init: {'theme': 'base', 'themeVariables': { 'lineColor': '#999999', 'edgeLabelBackground': '#ffffff', 'fontFamily': 'sans-serif'}}}%%
  graph TD;
    classDef start fill:#e3f2fd,stroke:#1565c0,stroke-width:2px,color:#0d47a1,rx:8px,ry:8px;
    classDef step fill:#eeeeee,stroke:#999999,stroke-width:2px,color:#333333,rx:8px,ry:8px;
    classDef solution fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px,color:#1b5e20,rx:8px,ry:8px;
    classDef fail fill:#fff3e0,stroke:#cc5500,stroke-width:2px,color:#000000,rx:8px,ry:8px;
  """

  @spec render(Trace.t(), keyword()) :: String.t()
  def render(trace, opts \\ [])

  def render(%Trace{root: nil}, _opts), do: ""

  def render(%Trace{root: root}, opts) do
    show_state? = Keyword.get(opts, :show_state, true)
    max_chars = Keyword.get(opts, :max_pair_chars, 40)

    {nodes, edges} = collect(root, [], [], show_state?, max_chars)

    node_lines =
      Enum.map_join(nodes, "\n", fn {id, label, class} ->
        "  N#{id}[\"#{label}\"]:::#{class};"
      end)

    edge_lines =
      Enum.map_join(edges, "\n", fn
        {from, to, :branch} -> "  N#{from} ==> N#{to};"
        {from, to, :linear} -> "  N#{from} -.-> N#{to};"
      end)

    @header <> node_lines <> "\n" <> edge_lines <> "\n"
  end

  ##############################################################################
  # TREE WALK
  ##############################################################################

  defp collect(%Node{} = node, nodes, edges, show_state?, max_chars) do
    self_entry = {node.id, label_for(node, show_state?, max_chars), class_for(node)}
    nodes = nodes ++ [self_entry]
    edge_kind = if length(node.children) > 1, do: :branch, else: :linear

    Enum.reduce(node.children, {nodes, edges}, fn child, {ns, es} ->
      child_edge = {node.id, child.id, edge_kind}
      collect(child, ns, es ++ [child_edge], show_state?, max_chars)
    end)
  end

  defp class_for(%Node{kind: :start}), do: "start"
  defp class_for(%Node{kind: :solution}), do: "solution"
  defp class_for(%Node{kind: :fail}), do: "fail"
  defp class_for(%Node{kind: :step}), do: "step"

  ##############################################################################
  # LABEL BUILDERS
  ##############################################################################

  defp label_for(%Node{kind: :start} = n, show?, max_chars) do
    head = "(#{n.id}) init"
    body = if show?, do: pairs_block(n.pairs, max_chars), else: ""
    join(head, body)
  end

  defp label_for(%Node{kind: :solution} = n, show?, _max_chars) do
    head = "(#{n.id}) ★ solution"

    body =
      if show? do
        sub_part = substs_block(n.substs)
        flex_part = if n.flex == [], do: "", else: "<br/>flex: " <> escape(pairs_inline(n.flex))
        sub_part <> flex_part
      else
        ""
      end

    join(head, body)
  end

  defp label_for(%Node{kind: :fail} = n, _show?, _max_chars) do
    note = if n.note, do: ": " <> escape(n.note), else: ""
    "(#{n.id}) ⊥ #{rule_name(n.rule)}#{note}"
  end

  defp label_for(%Node{kind: :step} = n, show?, max_chars) do
    head = "(#{n.id}) #{rule_name(n.rule)}"
    head_with_note = if n.note, do: head <> "<br/><i>" <> escape(n.note) <> "</i>", else: head
    body = if show?, do: pairs_block(n.pairs, max_chars), else: ""
    join(head_with_note, body)
  end

  defp join(head, ""), do: head
  defp join(head, body), do: head <> "<br/>" <> body

  defp pairs_block([], _), do: "<i>(no pending pairs)</i>"

  defp pairs_block(pairs, max_chars) do
    Enum.map_join(pairs, "<br/>", fn {l, r} ->
      "● " <> truncate(escape(l), max_chars) <> " =? " <> truncate(escape(r), max_chars)
    end)
  end

  defp pairs_inline(pairs) do
    Enum.map_join(pairs, "; ", fn {l, r} -> l <> " =? " <> r end)
  end

  defp substs_block([]), do: "<i>(empty σ)</i>"

  defp substs_block(substs) do
    Enum.map_join(substs, "<br/>", &("● " <> escape(&1)))
  end

  defp truncate(s, max) when byte_size(s) <= max, do: s
  defp truncate(s, max), do: binary_part(s, 0, max) <> "…"

  defp escape(text) do
    text
    |> to_string()
    |> String.replace("\"", "&quot;")
    |> String.replace("\n", " ")
  end

  defp rule_name(nil), do: "?"
  defp rule_name(:init), do: "init"
  defp rule_name(:trivial), do: "trivial"
  defp rule_name(:decompose_const), do: "decompose (const)"
  defp rule_name(:decompose_bv), do: "decompose (bv)"
  defp rule_name(:bind), do: "bind"
  defp rule_name(:flex_flex), do: "flex-flex defer"
  defp rule_name(:imitation), do: "imitation"
  defp rule_name(:projection), do: "projection"
  defp rule_name(:invert), do: "invert"
  defp rule_name(:alias), do: "alias"
  defp rule_name(:intersection), do: "intersection"
  defp rule_name(:type_mismatch), do: "type mismatch"
  defp rule_name(:rigid_clash), do: "rigid clash"
  defp rule_name(:occurs), do: "occurs check"
  defp rule_name(:no_decompose), do: "decompose fail"
  defp rule_name(:depth_exhausted), do: "depth exhausted"
  defp rule_name(:invert_fail), do: "inversion fail"
  defp rule_name(:not_pattern), do: "not a pattern"
  defp rule_name(:dead_end), do: "dead end"
  defp rule_name(:solved), do: "solved"
  defp rule_name(other), do: to_string(other)
end
