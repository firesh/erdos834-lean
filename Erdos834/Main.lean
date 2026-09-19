import Erdos834.NonColorable
import Erdos834.Certificate

/-!
# Erdős–Lovász problem #834: the answer

Li (arXiv:2512.24850, 2025) answered the chromatic reading of the Erdős–Lovász question
affirmatively.  The witness is the `3`-uniform hypergraph `H` of `Erdos834.Construction`: it has
`9` vertices and `22` edges, every degree is at least `7` (vertex `0` has degree `10`, the others
`7`), and it is critically `3`-chromatic — it is `3`-colourable but not `2`-colourable, and
deleting any single edge or vertex makes it `2`-colourable.
-/

namespace Erdos834

/-- **Erdős–Lovász problem #834** (chromatic interpretation): there is a `3`-uniform hypergraph on
`9` vertices with all degrees at least `7` that is critically `3`-chromatic. -/
theorem erdos_834 : Erdos834Statement :=
  ⟨H, H_uniform, min_deg, ⟨threeColoring, colorable_three⟩, not_colorable_two, edge_critical,
    vertex_critical⟩

end Erdos834
