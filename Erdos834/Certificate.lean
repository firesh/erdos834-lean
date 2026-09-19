import Erdos834.Construction

/-!
# Colouring certificates

`H` is `3`-chromatic but deleting any edge or vertex makes it `2`-colourable.  Following Li
(arXiv:2512.24850, Appendix B), this is certified by explicit colourings:

* for every edge `e`, Table 1 lists a `2`-colouring of the vertex set in which `e` is the unique
  monochromatic edge — equivalently a proper `2`-colouring of `H - e` (Lemma 2.2 of the paper);
* for every vertex `v`, Table 2 lists a proper `2`-colouring of `H - v`.

A colouring is described by its "blue" set `B`: vertices of `B` receive colour `1` and the
remaining vertices colour `0`.
-/

namespace Erdos834

set_option maxRecDepth 1000000

/-- The edge certificates of Li's Table 1: each edge `e` is paired with a blue set `B` such that `e`
is the unique monochromatic edge under the colouring with blue set `B`. -/
def edgeCerts : List (Finset (Fin 9) × Finset (Fin 9)) :=
  [ (E 0 1 2, {5, 6, 7, 8}), (E 0 1 8, {2, 3, 4, 5}), (E 0 2 7, {1, 3, 4, 5}),
    (E 0 3 5, {1, 6, 7, 8}), (E 0 3 7, {2, 4, 5, 8}), (E 0 3 8, {1, 4, 5, 7}),
    (E 0 4 6, {1, 5, 7, 8}), (E 0 4 7, {2, 3, 6, 8}), (E 0 4 8, {1, 3, 6, 7}),
    (E 0 5 6, {1, 2, 3, 4}), (E 1 2 5, {0, 6, 7, 8}), (E 1 2 6, {0, 5, 7, 8}),
    (E 1 3 8, {0, 2, 4, 5}), (E 1 4 8, {0, 2, 3, 6}), (E 1 5 6, {0, 2, 3, 4}),
    (E 2 3 7, {0, 1, 4, 5}), (E 2 4 7, {0, 1, 3, 6}), (E 2 5 6, {0, 1, 3, 4}),
    (E 3 5 7, {0, 2, 6, 8}), (E 3 5 8, {0, 1, 6, 7}), (E 4 6 7, {0, 2, 5, 8}),
    (E 4 6 8, {0, 1, 5, 7})]

/-- The vertex certificates of Li's Table 2: each vertex `v` is paired with a blue set
`B ⊆ V \ {v}` giving a proper `2`-colouring of `H - v`. -/
def vertexCerts : List (Fin 9 × Finset (Fin 9)) :=
  [ (0, {1, 2, 3, 4}), (1, {0, 2, 3, 4}), (2, {0, 1, 3, 4}), (3, {0, 1, 4, 5}),
    (4, {0, 1, 3, 6}), (5, {0, 1, 3, 4}), (6, {0, 1, 3, 4}), (7, {0, 1, 3, 6}),
    (8, {0, 1, 5, 7})]

/-- The `2`-colouring with the given blue set: blue vertices have colour `1`, all others `0`. -/
def blueColoring (B : Finset (Fin 9)) : Fin 9 → Fin 2 := fun v => if v ∈ B then 1 else 0

/-- The `3`-colouring of `H` exhibited by Li (Lemma 4.4): the paper's
`ψ(1) = ψ(2) = ψ(4) = ψ(5) = 1`, `ψ(3) = ψ(6) = ψ(8) = ψ(9) = 2`, `ψ(7) = 3`. -/
def threeColoring : Fin 9 → Fin 3 :=
  fun v => if v ∈ ({0, 1, 3, 4} : Finset (Fin 9)) then 0
    else if v ∈ ({2, 5, 7, 8} : Finset (Fin 9)) then 1 else 2

/-- `H` has a proper `3`-colouring, so its chromatic number is at most `3`. -/
theorem colorable_three : IsColoring H threeColoring := by decide

/-- Certificates of edge-criticality: for every edge `e`, the table's blue set makes `e` the unique
monochromatic edge. -/
theorem edgeCerts_spec :
    ∀ p ∈ edgeCerts, p.1 ∈ H ∧ ∀ f ∈ H, f ≠ p.1 → ¬ Mono (blueColoring p.2) f := by decide

/-- Certificates of vertex-criticality: for every vertex `v`, the table's blue set (which avoids
`v`) is a proper `2`-colouring of the edges not containing `v`. -/
theorem vertexCerts_spec :
    ∀ p ∈ vertexCerts, p.1 ∉ p.2 ∧ ∀ f ∈ H, p.1 ∉ f → ¬ Mono (blueColoring p.2) f := by decide

/-- The certificate table covers every edge of `H`. -/
theorem edgeCerts_cover : ∀ e ∈ H, ∃ p ∈ edgeCerts, p.1 = e := by decide

/-- The certificate table covers every vertex. -/
theorem vertexCerts_cover : ∀ v : Fin 9, ∃ p ∈ vertexCerts, p.1 = v := by decide

/-- Deleting any edge of `H` leaves a `2`-colourable hypergraph. -/
theorem edge_critical : ∀ e ∈ H, Colorable (H.erase e) 2 := by
  intro e he
  obtain ⟨p, hp, hpe⟩ := edgeCerts_cover e he
  subst hpe
  exact ⟨blueColoring p.2, fun f hf => (edgeCerts_spec p hp).2 f (Finset.mem_of_mem_erase hf)
    (Finset.ne_of_mem_erase hf)⟩

/-- Deleting any vertex of `H` leaves a `2`-colourable hypergraph. -/
theorem vertex_critical : ∀ v : Fin 9, Colorable (H.filter fun f => v ∉ f) 2 := by
  intro v
  obtain ⟨p, hp, hpv⟩ := vertexCerts_cover v
  subst hpv
  exact ⟨blueColoring p.2, fun f hf =>
    (vertexCerts_spec p hp).2 f (Finset.mem_of_mem_filter f hf) (Finset.mem_filter.1 hf).2⟩

end Erdos834
