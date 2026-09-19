import Erdos834.Statement
import Erdos834.Bollobas

/-!
# The transversal interpretation of Erdős–Lovász #834

Li (arXiv:2512.24850, 2025) also settles the *transversal* reading of the problem: a `3`-uniform
hypergraph that is `τ`-critical of order `3` has at most `10` edges (`edge_count_le_ten`, his
Theorem 3.2), so some covered vertex has degree at most `6` (his Corollary 3.4).  In particular no
such hypergraph has minimum degree at least `7` — the opposite answer to the chromatic reading
formalized in the rest of this repository.  The bound is sharp: the complete `3`-uniform hypergraph
on five vertices has `10` edges, is `τ`-critical of order `3`, and is `6`-regular.
-/

namespace Erdos834

open Finset

section Sharpness

/-- The complete `3`-uniform hypergraph on five vertices. -/
def K5 : Finset (Finset (Fin 5)) := (Finset.univ : Finset (Fin 5)).powersetCard 3

theorem K5_card : K5.card = 10 := by decide

theorem K5_uniform : ∀ e ∈ K5, e.card = 3 := by decide

theorem K5_min_degree : ∀ v : Fin 5, (K5.filter fun e => v ∈ e).card = 6 := by decide

/-- `K5` has transversal number `3`. -/
theorem K5_tauLe : TauLe K5 3 := by
  refine ⟨{0, 1, 2}, by decide, ?_⟩
  intro e he
  rw [K5, Finset.mem_powersetCard] at he
  obtain ⟨hsub, hcard⟩ := he
  by_contra hemp
  have h1 : e ⊆ ({3, 4} : Finset (Fin 5)) := by
    intro x hx
    by_contra hx34
    have hx012 : x ∈ ({0, 1, 2} : Finset (Fin 5)) := by
      fin_cases x <;> simp_all
    exact hemp ⟨x, Finset.mem_inter.2 ⟨hx012, hx⟩⟩
  have hle := Finset.card_le_card h1
  rw [hcard] at hle
  exact absurd hle (by decide)

/-- No two vertices meet every edge of `K5`, so its transversal number is exactly `3`. -/
theorem K5_tauGe : TauGe K5 3 := by
  intro T hT htrans
  have hcompl : 3 ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.2 (Finset.subset_univ T),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e, hesub, hecard⟩ := Finset.exists_subset_card_eq hcompl
  have he : e ∈ K5 := by
    rw [K5, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ e, hecard⟩
  have hemp : T ∩ e = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxT, hxe⟩ := Finset.mem_inter.1 hx
    exact (Finset.mem_sdiff.1 (hesub hxe)).2 hxT
  have := htrans e he
  rw [hemp] at this
  exact Finset.not_nonempty_empty this

/-- Deleting an edge of `K5` leaves a hypergraph with transversal number `2`. -/
theorem K5_critical : ∀ e ∈ K5, TauLe (K5.erase e) 2 := by
  intro e he
  have heK : e ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3 := by rwa [K5] at he
  have he3 : e.card = 3 := (Finset.mem_powersetCard.1 heK).2
  refine ⟨Finset.univ \ e, ?_, ?_⟩
  · rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ e), Finset.card_univ,
      Fintype.card_fin]
    omega
  · intro f hf
    rw [Finset.mem_erase] at hf
    obtain ⟨hfe, hfK⟩ := hf
    obtain ⟨hfsub, hfcard⟩ := Finset.mem_powersetCard.1 hfK
    by_contra hemp
    have hsub : f ⊆ e := by
      intro x hxf
      by_contra hxe
      have hx' : x ∈ Finset.univ \ e := Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hxe⟩
      exact hemp ⟨x, Finset.mem_inter.2 ⟨hx', hxf⟩⟩
    exact hfe (Finset.eq_of_subset_of_card_le hsub (by rw [hfcard, he3]))

/-- **The extremal example**: the complete `3`-uniform hypergraph on five vertices is
`τ`-critical of order `3` and is `6`-regular, so the bound of `edge_count_le_ten` is attained. -/
theorem K5_tau_critical : TauLe K5 3 ∧ TauGe K5 3 ∧ (∀ e ∈ K5, TauLe (K5.erase e) 2) ∧
    K5.card = 10 ∧ ∀ v : Fin 5, (K5.filter fun e => v ∈ e).card = 6 :=
  ⟨K5_tauLe, K5_tauGe, K5_critical, K5_card, K5_min_degree⟩

end Sharpness

section Statement

/-- **Erdős–Lovász #834, transversal interpretation.**  A `3`-uniform hypergraph that is
`τ`-critical of order `3` — that is, `τ(H) = 3` and deleting any edge lowers the transversal number
to `2` — has a vertex of degree at most `6`.  Hence no such hypergraph has minimum degree at least
`7`: under this reading the answer to the Erdős–Lovász question is *no*. -/
theorem no_tau_critical_min_degree_seven {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (h3 : ∀ e ∈ H, e.card = 3) (_htaule : TauLe H 3) (htauge : TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, deg H x ≤ 6 :=
  exists_deg_le_six_of_finite H h3 htauge hcrit

/-- The same statement with the paper's hypotheses spelled out. -/
theorem no_tau_critical_min_degree_seven' {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (h3 : ∀ e ∈ H, e.card = 3) (htau : TauLe H 3 ∧ TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, deg H x ≤ 6 :=
  exists_deg_le_six_of_finite H h3 htau.2 hcrit

end Statement

end Erdos834
