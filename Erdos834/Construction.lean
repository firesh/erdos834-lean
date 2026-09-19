import Erdos834.Statement

/-!
# Li's `9`-vertex example

The hypergraph `H` below is the explicit `3`-uniform hypergraph with `9` vertices and `22` edges
given by Ruiliang Li (*On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*,
arXiv:2512.24850, 2025, Section 4).  Vertex `0` is the paper's vertex `1`; the ten edges through
`0` are its first row, and the remaining twelve edges live on the other eight vertices.

This file records the numerical facts about `H`: it is `3`-uniform, all degrees are at least `7`
(vertex `0` has degree `10`, the other eight vertices have degree `7`), it has a proper
`3`-colouring, and it is edge- and vertex-critical — the latter two via the explicit certificates
of Li's Tables 1 and 2.
-/

namespace Erdos834

set_option maxRecDepth 100000

/-- The edge on the three given vertices. -/
def E (a b c : Fin 9) : Finset (Fin 9) := {a, b, c}

/-- Li's `3`-uniform hypergraph on `9` vertices. -/
def H : Finset (Finset (Fin 9)) :=
  { E 0 1 2, E 0 1 8, E 0 2 7, E 0 3 5, E 0 3 7, E 0 3 8, E 0 4 6, E 0 4 7, E 0 4 8,
    E 0 5 6, E 1 2 5, E 1 2 6, E 1 3 8, E 1 4 8, E 1 5 6, E 2 3 7, E 2 4 7, E 2 5 6,
    E 3 5 7, E 3 5 8, E 4 6 7, E 4 6 8 }

theorem H_card : H.card = 22 := by decide

theorem H_uniform : ∀ e ∈ H, e.card = 3 := by decide

theorem deg_zero : deg H 0 = 10 := by decide

theorem deg_ne_zero {v : Fin 9} (hv : v ≠ 0) : deg H v = 7 := by
  revert v
  decide

theorem min_deg : ∀ v : Fin 9, 7 ≤ deg H v := by decide

end Erdos834
