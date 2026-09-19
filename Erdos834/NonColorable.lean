import Erdos834.Construction

/-!
# `H` is not `2`-colourable

This is Li's Lemma 4.3 (arXiv:2512.24850), the mathematical heart of the construction.  Suppose
`c` is a proper `2`-colouring of `H`; after swapping the two colours we may assume that vertex `0`
has colour `0`.

Let `Z` be the set of vertices `≠ 0` of colour `0` and `A` the set of vertices `≠ 0` of colour `1`.

* `|Z| ≤ 3`: every `4`-subset of the nonzero vertices contains a pair `{x, y}` with `{0, x, y} ∈ H`
  (the paper's graph `G` has independence number `3`), and such a pair together with vertex `0`
  would be a monochromatic edge of colour `0`.
* Hence `|A| ≥ 8 - 3 = 5`, and every `5`-subset of the nonzero vertices contains an edge of `H`
  avoiding vertex `0`; that edge is monochromatic of colour `1`, a contradiction.
-/

namespace Erdos834

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- Every `4`-subset of the nonzero vertices contains a pair `{x, y}` with `{0, x, y} ∈ H`. -/
theorem four_subset :
    ∀ S ∈ (Finset.univ : Finset (Fin 9)).powerset, S.card = 4 → (0 : Fin 9) ∉ S →
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ E 0 x y ∈ H := by decide

/-- Every `5`-subset of the nonzero vertices contains an edge of `H` avoiding vertex `0`. -/
theorem five_subset :
    ∀ S ∈ (Finset.univ : Finset (Fin 9)).powerset, S.card = 5 → (0 : Fin 9) ∉ S →
      ∃ e ∈ H, (0 : Fin 9) ∉ e ∧ e ⊆ S := by decide

/-- In `Fin 2` there are only the two colours. -/
lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

/-- In `Fin 2` a nonzero colour is `1`. -/
lemma fin2_eq_one_of_ne_zero {x : Fin 2} (h : x ≠ 0) : x = 1 :=
  (fin2_eq_zero_or_one x).resolve_left h

/-- Swapping the two colours preserves properness. -/
lemma isColoring_add_one {c : Fin 9 → Fin 2} (hc : IsColoring H c) :
    IsColoring H fun v => c v + 1 := by
  intro e he hm
  exact hc e he fun x hx y hy => add_right_cancel (hm x hx y hy)

/-- **Li's Lemma 4.3.**  There is no proper `2`-colouring of `H` in which vertex `0` gets colour
`0`. -/
theorem not_isColoring_of_zero (c : Fin 9 → Fin 2) (hc0 : c 0 = 0) : ¬ IsColoring H c := by
  intro hc
  -- the vertices other than `0`, split by colour
  let Z : Finset (Fin 9) := (Finset.univ.erase 0).filter fun v => c v = 0
  let A : Finset (Fin 9) := (Finset.univ.erase 0).filter fun v => c v ≠ 0
  have hmemZ : ∀ v, v ∈ Z ↔ v ≠ 0 ∧ c v = 0 := by
    intro v
    simp only [Z, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  have hmemA : ∀ v, v ∈ A ↔ v ≠ 0 ∧ c v ≠ 0 := by
    intro v
    simp only [A, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  -- `Z` and `A` partition the eight vertices other than `0`
  have hZA : Z.card + A.card = 8 := by
    have hunion : (Z ∪ A : Finset (Fin 9)) = Finset.univ.erase 0 := by
      ext v
      by_cases hv : v = 0
      · simp [hmemZ, hmemA, hv]
      · by_cases hcv : c v = 0
        · simp [hmemZ, hmemA, hv, hcv]
        · simp [hmemZ, hmemA, hv, hcv]
    have hdisj : Disjoint Z A := by
      rw [Finset.disjoint_left]
      intro v hv
      rw [hmemZ] at hv
      rw [hmemA]
      exact fun h => h.2 hv.2
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
  -- Step 1: at most three vertices other than `0` have colour `0`
  have hZle : Z.card ≤ 3 := by
    by_contra hcon
    have h4 : 4 ≤ Z.card := by omega
    obtain ⟨S, hSZ, hScard⟩ := Finset.exists_subset_card_eq h4
    have hS0 : (0 : Fin 9) ∉ S := fun h0 => (hmemZ 0).1 (hSZ h0) |>.1 rfl
    obtain ⟨x, hxS, y, hyS, hxy, hxyH⟩ :=
      four_subset S (Finset.mem_powerset.2 (Finset.subset_univ S)) hScard hS0
    have hcx : c x = 0 := (hmemZ x).1 (hSZ hxS) |>.2
    have hcy : c y = 0 := (hmemZ y).1 (hSZ hyS) |>.2
    refine hc (E 0 x y) hxyH fun a ha b hb => ?_
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp [hc0, hcx, hcy]
  -- Step 2: at least five vertices other than `0` have colour `1`
  have hAge : 5 ≤ A.card := by omega
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hAge
  have hS0 : (0 : Fin 9) ∉ S := fun h0 => (hmemA 0).1 (hSA h0) |>.1 rfl
  obtain ⟨e, heH, _h0e, heS⟩ :=
    five_subset S (Finset.mem_powerset.2 (Finset.subset_univ S)) hScard hS0
  refine hc e heH fun a ha b hb => ?_
  have ha1 : c a = 1 := fin2_eq_one_of_ne_zero ((hmemA a).1 (hSA (heS ha))).2
  have hb1 : c b = 1 := fin2_eq_one_of_ne_zero ((hmemA b).1 (hSA (heS hb))).2
  simp [ha1, hb1]

/-- **Li's Lemma 4.3.**  The `3`-graph `H` is not `2`-colourable. -/
theorem not_colorable_two : ¬ Colorable H 2 := by
  rintro ⟨c, hc⟩
  rcases fin2_eq_zero_or_one (c 0) with h0 | h1
  · exact not_isColoring_of_zero c h0 hc
  · refine not_isColoring_of_zero (fun v => c v + 1) ?_ (isColoring_add_one hc)
    simp [h1]

end Erdos834
