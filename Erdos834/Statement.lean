import Mathlib

/-!
# Erdős–Lovász problem #834 (chromatic interpretation)

A (weak) vertex-colouring of a hypergraph assigns colours to vertices so that no edge is
monochromatic.  Erdős and Lovász asked whether there is a `3`-critical `3`-uniform hypergraph in
which every vertex has degree at least `7`; the term "3-critical" is ambiguous, and this file
concerns the *chromatic* reading: the chromatic number is `3`, and deleting any single edge or any
single vertex makes the hypergraph `2`-colourable.

Li (2025) answered this affirmatively with an explicit `3`-uniform hypergraph on `9` vertices with
minimum degree `7` that is critically `3`-chromatic in the above sense.
-/

namespace Erdos834

variable {α β : Type*} [DecidableEq α]

/-- The edge `e` is monochromatic under the colouring `c`. -/
abbrev Mono (c : α → β) (e : Finset α) : Prop := ∀ x ∈ e, ∀ y ∈ e, c x = c y

/-- `c` is a proper (weak) colouring of the hypergraph `H`: no edge of `H` is monochromatic. -/
abbrev IsColoring (H : Finset (Finset α)) (c : α → β) : Prop := ∀ e ∈ H, ¬ Mono c e

/-- The hypergraph `H` admits a proper colouring with `k` colours. -/
abbrev Colorable (H : Finset (Finset α)) (k : ℕ) : Prop := ∃ c : α → Fin k, IsColoring H c

/-- The degree of a vertex of a hypergraph: the number of edges containing it. -/
abbrev deg (H : Finset (Finset α)) (v : α) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- **Erdős–Lovász problem #834**, chromatic interpretation: there is a `3`-uniform hypergraph on
`9` vertices, all of whose degrees are at least `7`, that is critically `3`-chromatic — its
chromatic number is `3`, and deleting any edge or any vertex makes it `2`-colourable. -/
def Erdos834Statement : Prop :=
  ∃ H : Finset (Finset (Fin 9)),
    (∀ e ∈ H, e.card = 3) ∧
      (∀ v : Fin 9, 7 ≤ deg H v) ∧
      Colorable H 3 ∧ ¬ Colorable H 2 ∧
      (∀ e ∈ H, Colorable (H.erase e) 2) ∧
      (∀ v : Fin 9, Colorable (H.filter (fun e => v ∉ e)) 2)

end Erdos834
