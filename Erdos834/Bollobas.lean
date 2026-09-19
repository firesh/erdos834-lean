import Mathlib

/-!
# Bollobás's set-pairs inequality

The main counting tool for the transversal interpretation of Erdős–Lovász #834 is Bollobás's
set-pairs inequality (Li, arXiv:2512.24850, Lemma 3.1):

if `(A i, B i)` are pairs of finite sets with `A i ∩ B i = ∅` and `A i ∩ B j ≠ ∅` for `i ≠ j`, then
`∑ i, (Nat.choose (#(A i) + #(B i)) #(A i) : ℚ)⁻¹ ≤ 1`.

The proof follows the paper: for a uniformly random permutation of the ground set, the events
"every element of `A i` precedes every element of `B i`" are pairwise disjoint, and the `i`-th event
has probability `1 / C(#(A i) + #(B i), #(A i))`.

This file formalizes the counting step: the number of permutations of `Fin n` in which all of `A`
precedes all of `B` is `n! · #A! · #B! / #(A ∪ B)!`.  It is obtained from an explicit injection
(`assemble`) whose domain is the product of the `#A!` orderings of `A`, the `#B!` orderings of `B`,
the `C(n, #(A ∪ B))` choices of the position set `P` of `A ∪ B`, and the `(n - #(A ∪ B))!` bijections
of the complement of `P` onto the complement of `A ∪ B`.
-/

namespace Erdos834

open Finset

variable {n : ℕ}

/-- The permutations of `Fin n` in which every element of `A` precedes every element of `B`. -/
def beforeSet (A B : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ x ∈ A, ∀ y ∈ B, σ.symm x < σ.symm y

@[simp]
lemma mem_beforeSet {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ beforeSet A B ↔ ∀ x ∈ A, ∀ y ∈ B, σ.symm x < σ.symm y := by
  simp [beforeSet]

section Basic

variable {α : Type*} [DecidableEq α]

/-- `↥A ⊕ ↥B ≃ ↥(A ∪ B)` for disjoint finsets `A`, `B`. -/
def sumUnionEquiv {A B : Finset α} (h : Disjoint A B) : ↥A ⊕ ↥B ≃ ↥(A ∪ B) where
  toFun x := match x with
    | Sum.inl a => ⟨a.1, Finset.mem_union_left B a.2⟩
    | Sum.inr b => ⟨b.1, Finset.mem_union_right A b.2⟩
  invFun x := if hx : (x : α) ∈ A then Sum.inl ⟨x.1, hx⟩ else Sum.inr ⟨x.1, by
    rcases Finset.mem_union.1 x.2 with h' | h'
    · exact absurd h' hx
    · exact h'⟩
  left_inv x := by
    rcases x with a | b
    · simp only [a.2, ↓reduceDIte]
    · have hb : ¬((b : α) ∈ A) := Finset.disjoint_right.1 h b.2
      simp only [hb, ↓reduceDIte]
  right_inv x := by
    by_cases hx : (x : α) ∈ A
    · simp only [hx, ↓reduceDIte]
    · simp only [hx, ↓reduceDIte]

@[simp]
lemma sumUnionEquiv_inl {A B : Finset α} (h : Disjoint A B) (a : ↥A) :
    (sumUnionEquiv h (Sum.inl a) : α) = a := rfl

@[simp]
lemma sumUnionEquiv_inr {A B : Finset α} (h : Disjoint A B) (b : ↥B) :
    (sumUnionEquiv h (Sum.inr b) : α) = b := rfl

/-- The `A`-first ordering of `A ∪ B` determined by an ordering of `A` and one of `B`. -/
def firstEquiv {A B : Finset α} (h : Disjoint A B) (u : Fin A.card ≃ ↥A)
    (v : Fin B.card ≃ ↥B) : Fin (A.card + B.card) ≃ ↥(A ∪ B) :=
  (finSumFinEquiv (m := A.card) (n := B.card)).symm.trans
    ((Equiv.sumCongr u v).trans (sumUnionEquiv h))

@[simp]
lemma firstEquiv_castAdd {A B : Finset α} (h : Disjoint A B) (u : Fin A.card ≃ ↥A)
    (v : Fin B.card ≃ ↥B) (i : Fin A.card) :
    (firstEquiv h u v (Fin.castAdd B.card i) : α) = (u i : α) := by
  simp [firstEquiv]

@[simp]
lemma firstEquiv_natAdd {A B : Finset α} (h : Disjoint A B) (u : Fin A.card ≃ ↥A)
    (v : Fin B.card ≃ ↥B) (j : Fin B.card) :
    (firstEquiv h u v (Fin.natAdd A.card j) : α) = (v j : α) := by
  simp [firstEquiv]

/-- Applying a `subtypeCongr` permutation to an element of the first subtype. -/
lemma subtypeCongr_apply_left {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) (a : {x // p x}) :
    (Equiv.subtypeCongr e f a : α) = (e a : α) := by
  simp [Equiv.subtypeCongr]

/-- Applying a `subtypeCongr` permutation to an element of the second subtype. -/
lemma subtypeCongr_apply_right {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) (a : {x // ¬p x}) :
    (Equiv.subtypeCongr e f a : α) = (f a : α) := by
  simp [Equiv.subtypeCongr]

end Basic

section Assemble

variable {A B : Finset (Fin n)} (h : Disjoint A B) (u : Fin A.card ≃ ↥A)
  (v : Fin B.card ≃ ↥B) (P : Finset (Fin n)) (hP : P.card = A.card + B.card)
  (g : {x : Fin n // x ∉ P} ≃ {x : Fin n // x ∉ A ∪ B})

/-- Assemble a permutation from an `A`-first ordering of `A ∪ B`, placed on the position set `P`,
together with a bijection of the complementary positions onto the complementary points. -/
noncomputable def assemble : Equiv.Perm (Fin n) :=
  Equiv.subtypeCongr (p := fun x : Fin n => x ∈ P) (q := fun x : Fin n => x ∈ A ∪ B)
    (((Finset.orderIsoOfFin P hP).toEquiv).symm.trans (firstEquiv h u v)) g

/-- The assembled permutation sends the `i`-th smallest position of `P` to the `i`-th point of the
`A`-first ordering of `A ∪ B`. -/
@[simp]
lemma assemble_apply_orderIso (i : Fin (A.card + B.card)) :
    assemble h u v P hP g ((Finset.orderIsoOfFin P hP) i : Fin n) =
      (firstEquiv h u v i : Fin n) := by
  have hmem : ((Finset.orderIsoOfFin P hP) i : Fin n) ∈ P := ((Finset.orderIsoOfFin P hP) i).2
  rw [show ((Finset.orderIsoOfFin P hP) i : Fin n)
      = ((⟨((Finset.orderIsoOfFin P hP) i : Fin n), hmem⟩ : ↥P) : Fin n) from rfl,
    assemble, subtypeCongr_apply_left, Equiv.trans_apply]
  exact congrArg (fun a => ((firstEquiv h u v a : ↥(A ∪ B)) : Fin n))
    ((Finset.orderIsoOfFin P hP).symm_apply_apply i)

/-- On the complement of `P`, the assembled permutation is the given bijection `g`. -/
@[simp]
lemma assemble_apply_compl (x : Fin n) (hx : x ∉ P) :
    assemble h u v P hP g x = (g ⟨x, hx⟩ : Fin n) := by
  exact subtypeCongr_apply_right (p := fun x : Fin n => x ∈ P)
    (q := fun x : Fin n => x ∈ A ∪ B)
    (((Finset.orderIsoOfFin P hP).toEquiv).symm.trans (firstEquiv h u v)) g ⟨x, hx⟩

/-- The image of the position set `P` is `A ∪ B`. -/
lemma assemble_image_P : assemble h u v P hP g '' P = A ∪ B := by
  have hsurj : ∀ y : ↥(A ∪ B), ∃ i : Fin (A.card + B.card), (firstEquiv h u v i : Fin n) = y :=
    fun y => ⟨(firstEquiv h u v).symm y, by simp⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∃ i : Fin (A.card + B.card), (Finset.orderIsoOfFin P hP) i = ⟨y, hy⟩ :=
      ⟨(Finset.orderIsoOfFin P hP).symm ⟨y, hy⟩, by simp⟩
    obtain ⟨i, hi⟩ := hy'
    have hy'' : y = ((Finset.orderIsoOfFin P hP) i : Fin n) := (congrArg Subtype.val hi).symm
    rw [hy'', assemble_apply_orderIso]
    exact (firstEquiv h u v i).2
  · intro hx
    obtain ⟨i, hi⟩ := hsurj ⟨x, hx⟩
    exact ⟨(Finset.orderIsoOfFin P hP) i, ((Finset.orderIsoOfFin P hP) i).2,
      by rw [assemble_apply_orderIso]; exact hi⟩

/-- The preimage of `A ∪ B` under the assembled permutation is the position set `P`. -/
lemma assemble_symm_image : Finset.image (assemble h u v P hP g).symm (A ∪ B) = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨i, hi⟩ : ∃ i : Fin (A.card + B.card), (firstEquiv h u v i : Fin n) = y :=
      ⟨(firstEquiv h u v).symm ⟨y, hy⟩, by simp⟩
    have h1 : (assemble h u v P hP g).symm ((firstEquiv h u v i : Fin n))
        = ((Finset.orderIsoOfFin P hP) i : Fin n) := by
      rw [Equiv.symm_apply_eq, assemble_apply_orderIso]
    rw [← hi, h1]
    exact ((Finset.orderIsoOfFin P hP) i).2
  · intro hx
    obtain ⟨i, hi⟩ : ∃ i : Fin (A.card + B.card), (Finset.orderIsoOfFin P hP) i = ⟨x, hx⟩ :=
      ⟨(Finset.orderIsoOfFin P hP).symm ⟨x, hx⟩, by simp⟩
    refine Finset.mem_image.2 ⟨(assemble h u v P hP g) x, ?_, by simp⟩
    rw [show x = ((Finset.orderIsoOfFin P hP) i : Fin n) from (congrArg Subtype.val hi).symm,
      assemble_apply_orderIso]
    exact (firstEquiv h u v i).2

/-- The assembled permutation is in `beforeSet A B`. -/
lemma assemble_mem_beforeSet : assemble h u v P hP g ∈ beforeSet A B := by
  rw [mem_beforeSet]
  intro x hx y hy
  have hxa : x ∈ A ∪ B := Finset.mem_union_left B hx
  have hyb : y ∈ A ∪ B := Finset.mem_union_right A hy
  have hix : (assemble h u v P hP g).symm x
      = (Finset.orderIsoOfFin P hP) (finSumFinEquiv (m := A.card) (n := B.card) (Sum.inl (u.symm ⟨x, hx⟩))) := by
    rw [Equiv.symm_apply_eq, assemble_apply_orderIso]
    rw [finSumFinEquiv_apply_left, firstEquiv_castAdd]
    simp
  have hiy : (assemble h u v P hP g).symm y
      = (Finset.orderIsoOfFin P hP) (finSumFinEquiv (m := A.card) (n := B.card) (Sum.inr (v.symm ⟨y, hy⟩))) := by
    rw [Equiv.symm_apply_eq, assemble_apply_orderIso]
    rw [finSumFinEquiv_apply_right, firstEquiv_natAdd]
    simp
  rw [hix, hiy, Subtype.coe_lt_coe]
  refine (OrderIso.lt_iff_lt (Finset.orderIsoOfFin P hP)).mpr ?_
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Assemble

section Counting

variable {A B : Finset (Fin n)}

/-- The possible position sets of `A ∪ B`: the `#A + #B`-subsets of `Fin n`. -/
def posSets (A B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard (A.card + B.card)

/-- The configurations assembled into permutations: an ordering of `A`, an ordering of `B`, a
position set for `A ∪ B`, and a bijection from the complementary positions to the complementary
points. -/
abbrev Cfg (A B : Finset (Fin n)) :=
  (Fin A.card ≃ ↥A) × (Fin B.card ≃ ↥B) ×
    (Σ P : {P : Finset (Fin n) // P ∈ posSets A B},
      {x : Fin n // x ∉ (P : Finset (Fin n))} ≃ {x : Fin n // x ∉ A ∪ B})

/-- The permutation assembled from a configuration. -/
noncomputable def toPerm (h : Disjoint A B) (d : Cfg A B) : Equiv.Perm (Fin n) :=
  assemble h d.1 d.2.1 d.2.2.1 (Finset.mem_powersetCard.1 d.2.2.1.2).2 d.2.2.2

lemma toPerm_mem_beforeSet (h : Disjoint A B) (d : Cfg A B) :
    toPerm h d ∈ beforeSet A B :=
  assemble_mem_beforeSet h d.1 d.2.1 d.2.2.1 _ d.2.2.2

/-- `toPerm` is injective: a permutation determines its position set, the orderings of `A` and `B`
and the bijection on the complement. -/
theorem toPerm_injective (h : Disjoint A B) : Function.Injective (toPerm h) := by
  rintro ⟨u, v, ⟨⟨P, hPmem⟩, g⟩⟩ ⟨u', v', ⟨⟨P', hPmem'⟩, g'⟩⟩ hdd'
  simp only [toPerm] at hdd'
  -- the position set is the preimage of `A ∪ B`
  have hPP' : P = P' := by
    have h1 := assemble_symm_image h u v P (Finset.mem_powersetCard.1 hPmem).2 g
    have h2 := assemble_symm_image h u' v' P' (Finset.mem_powersetCard.1 hPmem').2 g'
    rw [← h1, ← h2, hdd']
  subst hPP'
  -- the orderings of `A` and `B` are read off from the image of the position set
  have hu : u = u' := by
    refine Equiv.ext fun i => Subtype.ext ?_
    have h1 := assemble_apply_orderIso h u v P (Finset.mem_powersetCard.1 hPmem).2 g (Fin.castAdd B.card i)
    have h2 := assemble_apply_orderIso h u' v' P (Finset.mem_powersetCard.1 hPmem).2 g' (Fin.castAdd B.card i)
    rw [firstEquiv_castAdd] at h1 h2
    calc (u i : Fin n)
        = (assemble h u v P (Finset.mem_powersetCard.1 hPmem).2 g) ((Finset.orderIsoOfFin P (Finset.mem_powersetCard.1 hPmem).2) (Fin.castAdd B.card i)) := h1.symm
      _ = (assemble h u' v' P (Finset.mem_powersetCard.1 hPmem).2 g') ((Finset.orderIsoOfFin P (Finset.mem_powersetCard.1 hPmem).2) (Fin.castAdd B.card i)) := by
          rw [hdd']
      _ = (u' i : Fin n) := h2
  have hv : v = v' := by
    refine Equiv.ext fun i => Subtype.ext ?_
    have h1 := assemble_apply_orderIso h u v P (Finset.mem_powersetCard.1 hPmem).2 g (Fin.natAdd A.card i)
    have h2 := assemble_apply_orderIso h u' v' P (Finset.mem_powersetCard.1 hPmem).2 g' (Fin.natAdd A.card i)
    rw [firstEquiv_natAdd] at h1 h2
    calc (v i : Fin n)
        = (assemble h u v P (Finset.mem_powersetCard.1 hPmem).2 g) ((Finset.orderIsoOfFin P (Finset.mem_powersetCard.1 hPmem).2) (Fin.natAdd A.card i)) := h1.symm
      _ = (assemble h u' v' P (Finset.mem_powersetCard.1 hPmem).2 g') ((Finset.orderIsoOfFin P (Finset.mem_powersetCard.1 hPmem).2) (Fin.natAdd A.card i)) := by
          rw [hdd']
      _ = (v' i : Fin n) := h2
  subst hu
  subst hv
  -- the bijection on the complement is the restriction of the permutation
  have hg : g = g' := by
    refine Equiv.ext fun x => Subtype.ext ?_
    have h1 := assemble_apply_compl h u v P (Finset.mem_powersetCard.1 hPmem).2 g (x : Fin n) x.2
    have h2 := assemble_apply_compl h u v P (Finset.mem_powersetCard.1 hPmem).2 g' (x : Fin n) x.2
    rw [← h1, ← h2, hdd']
  subst hg
  rfl


/-- The number of points outside a finset. -/
lemma card_compl_subtype (P : Finset (Fin n)) :
    Fintype.card {x : Fin n // x ∉ P} = n - P.card := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin n => x ∉ P) = Pᶜ := by ext x; simp
  rw [this, Finset.card_compl, Fintype.card_fin]

/-- The number of configurations. -/
lemma card_Cfg (h : Disjoint A B) : Fintype.card (Cfg A B) =
    A.card.factorial * B.card.factorial * (n.choose (A.card + B.card)) *
      (n - (A.card + B.card)).factorial := by
  have hA : Fintype.card (Fin A.card ≃ ↥A) = A.card.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [Fintype.card_coe])),
      Fintype.card_fin]
  have hB : Fintype.card (Fin B.card ≃ ↥B) = B.card.factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [Fintype.card_coe])),
      Fintype.card_fin]
  have hP : Fintype.card {P : Finset (Fin n) // P ∈ posSets A B} =
      n.choose (A.card + B.card) := by
    rw [Fintype.card_subtype]
    have h1 : (Finset.univ.filter fun P : Finset (Fin n) => P ∈ posSets A B) = posSets A B := by
      ext P
      simp
    rw [h1, posSets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hsigma : Fintype.card (Σ P : {P : Finset (Fin n) // P ∈ posSets A B},
      {x : Fin n // x ∉ (P : Finset (Fin n))} ≃ {x : Fin n // x ∉ A ∪ B}) =
      (n.choose (A.card + B.card)) * (n - (A.card + B.card)).factorial := by
    rw [Fintype.card_sigma]
    have hterm : ∀ P : {P : Finset (Fin n) // P ∈ posSets A B},
        Fintype.card ({x : Fin n // x ∉ (P : Finset (Fin n))} ≃ {x : Fin n // x ∉ A ∪ B}) =
          (n - (A.card + B.card)).factorial := by
      intro P
      have h1 : Fintype.card {x : Fin n // x ∉ (P : Finset (Fin n))} =
          n - (A.card + B.card) := by
        rw [card_compl_subtype, (Finset.mem_powersetCard.1 P.2).2]
      have h2 : Fintype.card {x : Fin n // x ∉ A ∪ B} = n - (A.card + B.card) := by
        rw [card_compl_subtype, Finset.card_union_of_disjoint h]
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by rw [h1, h2])), h1]
    rw [Finset.sum_congr rfl fun P _ => hterm P, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hP]
    simp only [Nat.cast_id]
  rw [Fintype.card_prod, Fintype.card_prod, hA, hB, hsigma]
  ring

/-- **The counting bound.** The number of permutations of `Fin n` in which every element of `A`
precedes every element of `B` is at least `n! · #A! · #B! / #(A ∪ B)!`. -/
theorem card_beforeSet (h : Disjoint A B) :
    n.factorial * A.card.factorial * B.card.factorial ≤
      (beforeSet A B).card * (A.card + B.card).factorial := by
  have hs : A.card + B.card ≤ n := by
    have h1 : (A ∪ B).card ≤ n := by
      simpa using Finset.card_le_univ (A ∪ B)
    rwa [Finset.card_union_of_disjoint h] at h1
  have hcard : Fintype.card (Cfg A B) ≤ (beforeSet A B).card := by
    have hinj := Fintype.card_le_of_injective
      (fun d : Cfg A B =>
        (⟨toPerm h d, toPerm_mem_beforeSet h d⟩ : {σ : Equiv.Perm (Fin n) // σ ∈ beforeSet A B}))
      (fun d d' hdd => toPerm_injective h (Subtype.ext_iff.1 hdd))
    rwa [Fintype.card_coe] at hinj
  rw [card_Cfg h] at hcard
  have hchoose : n.choose (A.card + B.card) * (A.card + B.card).factorial *
      (n - (A.card + B.card)).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hs
  calc n.factorial * A.card.factorial * B.card.factorial
      = A.card.factorial * B.card.factorial * (n.choose (A.card + B.card)) *
          (n - (A.card + B.card)).factorial * (A.card + B.card).factorial := by
        rw [← hchoose]; ring
    _ ≤ (beforeSet A B).card * (A.card + B.card).factorial :=
        Nat.mul_le_mul_right _ hcard

/-- The counting bound for a `3`-set against a `2`-set: at least a tenth of the permutations put
all of `A` before all of `B`. -/
theorem card_beforeSet_three_two (h : Disjoint A B) (hA : A.card = 3) (hB : B.card = 2) :
    n.factorial ≤ 10 * (beforeSet A B).card := by
  have hmain := card_beforeSet h
  have h1 : A.card.factorial = 6 := by rw [hA]; norm_num
  have h2 : B.card.factorial = 2 := by rw [hB]; norm_num
  have h3 : (A.card + B.card).factorial = 120 := by rw [hA, hB]; norm_num
  rw [h1, h2, h3] at hmain
  have hmain' : n.factorial * 12 ≤ (beforeSet A B).card * 120 := by
    calc n.factorial * 12 = n.factorial * 6 * 2 := by ring
      _ ≤ (beforeSet A B).card * 120 := hmain
  refine Nat.le_of_mul_le_mul_right ?_ (by norm_num : 0 < 12)
  calc n.factorial * 12 ≤ (beforeSet A B).card * 120 := hmain'
    _ = ((beforeSet A B).card * 10) * 12 := by ring
    _ = (10 * (beforeSet A B).card) * 12 := by ring

end Counting


section SetPairs

/-- The "before" sets of two cross-intersecting pairs are disjoint. -/
lemma beforeSet_disjoint {A B A' B' : Finset (Fin n)}
    (hAB' : (A ∩ B').Nonempty) (hA'B : (A' ∩ B).Nonempty) :
    Disjoint (beforeSet A B) (beforeSet A' B') := by
  rw [Finset.disjoint_left]
  intro σ h1 h2
  rw [mem_beforeSet] at h1 h2
  obtain ⟨x, hx⟩ := hAB'
  obtain ⟨hxA, hxB'⟩ := Finset.mem_inter.1 hx
  obtain ⟨y, hy⟩ := hA'B
  obtain ⟨hyA', hyB⟩ := Finset.mem_inter.1 hy
  exact lt_asymm (h1 x hxA y hyB) (h2 y hyA' x hxB')

/-- **Bollobás's set-pairs inequality for a `3`-set against a `2`-set**: a family of disjoint pairs
`A i`, `B i` of sizes `3` and `2` whose `A`-parts meet all the other `B`-parts has at most `10`
members. -/
theorem setPairs_three_two {ι : Type*} [Fintype ι] (A B : ι → Finset (Fin n))
    (hA3 : ∀ i, (A i).card = 3) (hB2 : ∀ i, (B i).card = 2)
    (hdisj : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → ((A i) ∩ (B j)).Nonempty) :
    Fintype.card ι ≤ 10 := by
  have hpd : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => beforeSet (A i) (B i)) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i _ j _ hne
    by_contra hij
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
    exact Finset.disjoint_left.1
      (beforeSet_disjoint (hcross i j hij) (hcross j i (Ne.symm hij))) hx1 hx2
  have hsum : ∑ i : ι, (beforeSet (A i) (B i)).card ≤ n.factorial := by
    rw [← Finset.card_biUnion hpd]
    calc (Finset.univ.biUnion fun i => beforeSet (A i) (B i)).card
        ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
          Finset.card_le_card fun x _ => Finset.mem_univ x
      _ = n.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have h10 : ∀ i, n.factorial ≤ 10 * (beforeSet (A i) (B i)).card :=
    fun i => card_beforeSet_three_two (hdisj i) (hA3 i) (hB2 i)
  have hmain : Fintype.card ι * n.factorial ≤ 10 * n.factorial := by
    calc Fintype.card ι * n.factorial = ∑ _i : ι, n.factorial := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      _ ≤ ∑ i : ι, 10 * (beforeSet (A i) (B i)).card := Finset.sum_le_sum fun i _ => h10 i
      _ = 10 * ∑ i : ι, (beforeSet (A i) (B i)).card := by rw [Finset.mul_sum]
      _ ≤ 10 * n.factorial := Nat.mul_le_mul_left _ hsum
  exact Nat.le_of_mul_le_mul_right hmain (Nat.factorial_pos n)

end SetPairs

section Hypergraph

/-- A set meeting every edge of a hypergraph. -/
abbrev IsTransversal {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ e ∈ H, (T ∩ e).Nonempty

/-- Some set of size at most `k` meets every edge, i.e. `τ(H) ≤ k`. -/
abbrev TauLe {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ T : Finset α, T.card ≤ k ∧ IsTransversal H T

/-- No set of size less than `k` meets every edge, i.e. `τ(H) ≥ k`. -/
abbrev TauGe {α : Type*} [DecidableEq α] (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ T : Finset α, T.card < k → ¬ IsTransversal H T

variable {H : Finset (Finset (Fin n))}

/-- If `H` is `3`-uniform with `τ(H) = 3` and `τ(H - e) ≤ 2` for every edge `e`, then for each edge
some `2`-set meets every other edge and is disjoint from `e` (Li, Section 3.2). -/
lemma exists_pair (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) (he : e ∈ H) :
    ∃ B : Finset (Fin n), B.card = 2 ∧ Disjoint B e ∧ IsTransversal (H.erase e) B := by
  obtain ⟨B, hBcard, hBtrans⟩ := hcrit e he
  have hne : e.Nonempty := by
    rw [← Finset.card_pos, h3 e he]
    norm_num
  have hge2 : 2 ≤ B.card := by
    by_contra hcon
    have hcon' : B.card < 2 := not_le.1 hcon
    have hcases : B.card = 0 ∨ B.card = 1 := by omega
    rcases hcases with h0 | h1
    · -- `B = ∅`, so the only edge is `e`
      have hBempty : B = ∅ := Finset.card_eq_zero.1 h0
      have hHsub : H ⊆ {e} := by
        intro f hf
        by_contra hfe
        have hmem : f ∈ H.erase e := Finset.mem_erase.2 ⟨fun h => hfe (Finset.mem_singleton.2 h), hf⟩
        obtain ⟨x, hx⟩ := hBtrans f hmem
        rw [hBempty] at hx
        exact Finset.notMem_empty x (Finset.mem_inter.1 hx).1
      obtain ⟨x, hxe⟩ := hne
      have htrans : IsTransversal H {x} := by
        intro f hf
        have hfe : f = e := Finset.mem_singleton.1 (hHsub hf)
        exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_singleton_self x, by rw [hfe]; exact hxe⟩⟩
      exact htau {x} (by rw [Finset.card_singleton]; norm_num) htrans
    · -- `B = {x}`
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
      by_cases hxe : x ∈ e
      · have htrans : IsTransversal H {x} := by
          intro f hf
          by_cases hfe : f = e
          · exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_singleton_self x, by rw [hfe]; exact hxe⟩⟩
          · have hmem : f ∈ H.erase e := Finset.mem_erase.2 ⟨hfe, hf⟩
            obtain ⟨y, hy⟩ := hBtrans f hmem
            obtain ⟨hy1, hy2⟩ := Finset.mem_inter.1 hy
            rw [Finset.mem_singleton] at hy1
            rw [hy1] at hy2
            exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_singleton_self x, hy2⟩⟩
        exact htau {x} (by rw [Finset.card_singleton]; norm_num) htrans
      · obtain ⟨y, hye⟩ := hne
        have hxy : x ≠ y := fun h => hxe (h ▸ hye)
        have htrans : IsTransversal H {x, y} := by
          intro f hf
          by_cases hfe : f = e
          · exact ⟨y, Finset.mem_inter.2
              ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self y),
               by rw [hfe]; exact hye⟩⟩
          · have hmem : f ∈ H.erase e := Finset.mem_erase.2 ⟨hfe, hf⟩
            obtain ⟨z, hz⟩ := hBtrans f hmem
            obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
            rw [Finset.mem_singleton] at hz1
            rw [hz1] at hz2
            exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_insert_self x {y}, hz2⟩⟩
        have hcard : ({x, y} : Finset (Fin n)).card = 2 := by
          rw [Finset.card_insert_of_notMem, Finset.card_singleton]
          simp [hxy]
        exact htau {x, y} (by rw [hcard]; norm_num) htrans
  have hdisj : Disjoint B e := by
    rw [Finset.disjoint_left]
    intro x hxB hxe
    have htrans : IsTransversal H B := by
      intro f hf
      by_cases hfe : f = e
      · exact ⟨x, Finset.mem_inter.2 ⟨hxB, by rw [hfe]; exact hxe⟩⟩
      · exact hBtrans f (Finset.mem_erase.2 ⟨hfe, hf⟩)
    exact htau B (by omega) htrans
  exact ⟨B, by omega, hdisj, hBtrans⟩

/-- **Li's Theorem 3.2.**  A `3`-uniform hypergraph with `τ(H) = 3` and `τ(H - e) ≤ 2` for every
edge `e` has at most `10` edges. -/
theorem edge_count_le_ten (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) : H.card ≤ 10 := by
  classical
  choose B hBcard hBdisj hBtrans using fun i : {e // e ∈ H} => exists_pair h3 htau hcrit i.2
  have hmain := setPairs_three_two (n := n) (ι := {e // e ∈ H}) (fun i => i.1) B
    (fun i => h3 i.1 i.2) hBcard (fun i => (hBdisj i).symm)
    (fun i j hij => by
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hmem : i.1 ∈ H.erase j.1 := Finset.mem_erase.2 ⟨hne, i.2⟩
      obtain ⟨x, hx⟩ := hBtrans j i.1 hmem
      exact ⟨x, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).2, (Finset.mem_inter.1 hx).1⟩⟩)
  rwa [Fintype.card_coe] at hmain

end Hypergraph

section Corollary

variable {H : Finset (Finset (Fin n))}

/-- The vertices covered by the edges of `H`. -/
def cover {α : Type*} [DecidableEq α] (H : Finset (Finset α)) : Finset α := H.biUnion id

lemma mem_cover {α : Type*} [DecidableEq α] {H : Finset (Finset α)} {x : α} :
    x ∈ cover H ↔ ∃ e ∈ H, x ∈ e := by
  simp [cover]

/-- Double counting: for a `3`-uniform hypergraph the degrees over the covered vertices sum to `3`
times the number of edges. -/
lemma sum_deg (h3 : ∀ e ∈ H, e.card = 3) :
    ∑ x ∈ cover H, (H.filter fun e => x ∈ e).card = 3 * H.card := by
  have hinner : ∀ e ∈ H, ∑ x ∈ cover H, (if x ∈ e then (1 : ℕ) else 0) = 3 := by
    intro e he
    have hfilter : (cover H).filter (fun x => x ∈ e) = e := by
      ext x
      rw [Finset.mem_filter, mem_cover]
      exact ⟨fun h => h.2, fun hx => ⟨⟨e, he, hx⟩, hx⟩⟩
    rw [← Finset.card_filter, hfilter, h3 e he]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring

/-- If `τ(H) = 3` then `H` covers at least five vertices. -/
lemma five_le_card_cover (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3) :
    5 ≤ (cover H).card := by
  by_contra hcon
  have hV : (cover H).card ≤ 4 := by omega
  have hHne : H.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact htau ∅ (by norm_num)
      (by intro f hf; rw [h] at hf; exact absurd hf (Finset.notMem_empty f))
  obtain ⟨e, he⟩ := hHne
  have hcov : 2 ≤ (cover H).card := by
    have h1 : e.card ≤ (cover H).card :=
      Finset.card_le_card fun z hz => mem_cover.2 ⟨e, he, hz⟩
    rw [h3 e he] at h1
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcov
  have htrans : IsTransversal H T := by
    intro f hf
    by_contra hemp
    have hsub : T ⊆ cover H \ f := by
      intro x hx
      rw [Finset.mem_sdiff]
      exact ⟨hTsub hx, fun hxf => hemp ⟨x, Finset.mem_inter.2 ⟨hx, hxf⟩⟩⟩
    have hle : (cover H \ f).card ≤ 1 := by
      have hfsub : f ⊆ cover H := fun z hz => mem_cover.2 ⟨f, hf, hz⟩
      have h1 : (cover H \ f).card = (cover H).card - f.card := by
        rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.2 hfsub]
      rw [h1, h3 f hf]
      omega
    have := Finset.card_le_card hsub
    omega
  exact htau T (by omega) htrans

/-- **Li's Corollary 3.4.**  A `3`-uniform hypergraph with `τ(H) = 3` and `τ(H - e) ≤ 2` for every
edge has a vertex of degree at most `6`. -/
theorem exists_deg_le_six (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, (H.filter fun e => x ∈ e).card ≤ 6 := by
  by_contra hcon
  have h7 : ∀ x ∈ cover H, 7 ≤ (H.filter fun e => x ∈ e).card := by
    intro x hx
    by_contra hlt
    exact hcon ⟨x, hx, by omega⟩
  have hsum := sum_deg h3
  have hV := five_le_card_cover h3 htau
  have hcard := edge_count_le_ten h3 htau hcrit
  have hle : 7 * (cover H).card ≤ ∑ x ∈ cover H, (H.filter fun e => x ∈ e).card := by
    simpa [nsmul_eq_mul, mul_comm] using Finset.card_nsmul_le_sum (cover H)
      (fun x => (H.filter fun e => x ∈ e).card) 7 h7
  omega

end Corollary

section Transport

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Relabel a hypergraph along an equivalence of vertex types. -/
def relabel (e : α ≃ β) (H : Finset (Finset α)) : Finset (Finset β) :=
  H.image (Finset.image e)

omit [DecidableEq α] in
lemma mem_relabel {e : α ≃ β} {H : Finset (Finset α)} {f : Finset β} :
    f ∈ relabel e H ↔ ∃ g ∈ H, f = g.image e := by
  simp [relabel, eq_comm]

omit [DecidableEq α] in
/-- The relabelled copy of an edge. -/
lemma mem_relabel_image {e : α ≃ β} {H : Finset (Finset α)} {g : Finset α} (hg : g ∈ H) :
    g.image e ∈ relabel e H :=
  mem_relabel.2 ⟨g, hg, rfl⟩

omit [DecidableEq α] in
/-- `Finset.image` along an injective map is injective. -/
lemma image_injective {e : α ≃ β} : Function.Injective (Finset.image e) := by
  intro g g' h
  ext x
  constructor
  · intro hx
    have hmem : e x ∈ g'.image e := by
      rw [← h]
      exact Finset.mem_image.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hmem
    rwa [e.injective hyx] at hy
  · intro hx
    have hmem : e x ∈ g.image e := by
      rw [h]
      exact Finset.mem_image.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hmem
    rwa [e.injective hyx] at hy

omit [DecidableEq α] in
lemma relabel_card {e : α ≃ β} {H : Finset (Finset α)} : (relabel e H).card = H.card := by
  rw [relabel, Finset.card_image_of_injective]
  exact image_injective

omit [DecidableEq α] in
lemma relabel_uniform {e : α ≃ β} {H : Finset (Finset α)} {k : ℕ}
    (h : ∀ g ∈ H, g.card = k) : ∀ f ∈ relabel e H, f.card = k := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := mem_relabel.1 hf
  rw [Finset.card_image_of_injective _ e.injective]
  exact h g hg

/-- A transversal of the relabelled hypergraph pulls back to one of the original. -/
lemma relabel_transversal {e : α ≃ β} {H : Finset (Finset α)}
    (h : IsTransversal (relabel e H) ((T : Finset α).image e)) : IsTransversal H T := by
  intro g hg
  obtain ⟨x, hx⟩ := h (g.image e) (mem_relabel_image hg)
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
  obtain ⟨z, hzg, rfl⟩ := Finset.mem_image.1 hx2
  obtain ⟨y, hyT, hy⟩ := Finset.mem_image.1 hx1
  exact ⟨y, Finset.mem_inter.2 ⟨hyT, by rw [e.injective hy]; exact hzg⟩⟩

/-- A transversal of the original pushes forward to one of the relabelled hypergraph. -/
lemma relabel_transversal' {e : α ≃ β} {H : Finset (Finset α)} {T : Finset α}
    (h : IsTransversal H T) : IsTransversal (relabel e H) (T.image e) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := mem_relabel.1 hf
  obtain ⟨x, hx⟩ := h g hg
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
  exact ⟨e x, Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨x, hx1, rfl⟩,
    Finset.mem_image.2 ⟨x, hx2, rfl⟩⟩⟩

lemma relabel_tauGe {e : α ≃ β} {H : Finset (Finset α)} {k : ℕ} (h : TauGe H k) :
    TauGe (relabel e H) k := by
  intro T hT htrans
  refine h (T.image e.symm) ?_ ?_
  · rw [Finset.card_image_of_injective _ e.symm.injective]
    exact hT
  · intro g hg
    obtain ⟨x, hx⟩ := htrans (g.image e) (mem_relabel_image hg)
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
    obtain ⟨z, hzg, rfl⟩ := Finset.mem_image.1 hx2
    exact ⟨z, Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨e z, hx1, by simp⟩, hzg⟩⟩

lemma relabel_tauLe {e : α ≃ β} {H : Finset (Finset α)} {k : ℕ} (h : TauLe H k) :
    TauLe (relabel e H) k := by
  obtain ⟨T, hT, htrans⟩ := h
  exact ⟨T.image e, by rw [Finset.card_image_of_injective _ e.injective]; exact hT,
    relabel_transversal' htrans⟩

lemma relabel_erase {e : α ≃ β} {H : Finset (Finset α)} {f : Finset α} :
    (relabel e H).erase (f.image e) = relabel e (H.erase f) := by
  ext g
  rw [Finset.mem_erase, mem_relabel, mem_relabel]
  constructor
  · rintro ⟨hne, g₀, hg₀, hgg₀⟩
    refine ⟨g₀, Finset.mem_erase.2 ⟨?_, hg₀⟩, hgg₀⟩
    intro hg₀f
    exact hne (by rw [hgg₀, hg₀f])
  · rintro ⟨g₀, hg₀, hgg₀⟩
    refine ⟨?_, g₀, (Finset.mem_erase.1 hg₀).2, hgg₀⟩
    intro h
    exact (Finset.mem_erase.1 hg₀).1 (image_injective (by rw [← hgg₀, h]))

lemma relabel_deg {e : α ≃ β} {H : Finset (Finset α)} (x : α) :
    ((relabel e H).filter fun f => e x ∈ f).card = (H.filter fun g => x ∈ g).card := by
  have h : (relabel e H).filter (fun f => e x ∈ f) =
      (H.filter fun g => x ∈ g).image (Finset.image e) := by
    ext f
    rw [Finset.mem_filter, mem_relabel, Finset.mem_image]
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, hx⟩
      exact ⟨g, Finset.mem_filter.2 ⟨hg, by simpa using hx⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (Finset.mem_filter.1 hg).1, rfl⟩, by simpa using (Finset.mem_filter.1 hg).2⟩
  rw [h, Finset.card_image_of_injective]
  exact image_injective

lemma relabel_cover {e : α ≃ β} {H : Finset (Finset α)} :
    cover (relabel e H) = (cover H).image e := by
  ext y
  constructor
  · intro hy
    obtain ⟨f, hf, hyf⟩ := mem_cover.1 hy
    obtain ⟨g, hg, rfl⟩ := mem_relabel.1 hf
    obtain ⟨x, hxg, rfl⟩ := Finset.mem_image.1 hyf
    exact Finset.mem_image.2 ⟨x, mem_cover.2 ⟨g, hg, hxg⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨g, hg, hxg⟩ := mem_cover.1 hx
    exact mem_cover.2 ⟨g.image e, mem_relabel_image hg, Finset.mem_image.2 ⟨x, hxg, rfl⟩⟩

/-- **Li's Corollary 3.4** for an arbitrary finite vertex type: a `3`-uniform hypergraph with
`τ(H) = 3` and `τ(H - e) ≤ 2` for every edge has a vertex of degree at most `6`. -/
theorem exists_deg_le_six_of_finite [Fintype α] (H : Finset (Finset α)) (h3 : ∀ e ∈ H, e.card = 3)
    (htau : TauGe H 3) (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, (H.filter fun e => x ∈ e).card ≤ 6 := by
  classical
  obtain ⟨x, hx, hdeg⟩ := exists_deg_le_six (n := Fintype.card α)
    (H := relabel (Fintype.equivFin α) H) (relabel_uniform h3) (relabel_tauGe htau)
    (fun f hf => by
      obtain ⟨g, hg, rfl⟩ := mem_relabel.1 hf
      rw [relabel_erase (e := Fintype.equivFin α)]
      exact relabel_tauLe (hcrit g hg))
  rw [relabel_cover] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  exact ⟨y, hy, by rw [← relabel_deg (e := Fintype.equivFin α) y]; exact hdeg⟩

end Transport
end Erdos834
