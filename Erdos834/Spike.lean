import Mathlib

namespace Erdos834
open Finset

/-- `↥A ⊕ ↥B ≃ ↥(A ∪ B)` for disjoint finsets. -/
def sumUnionEquiv {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) :
    ↥A ⊕ ↥B ≃ ↥(A ∪ B) where
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
    · have hx' : ¬((x : α) ∈ A) := hx
      simp only [hx', ↓reduceDIte]

example {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) (a : ↥A) :
    (sumUnionEquiv h (Sum.inl a) : α) = a := rfl

end Erdos834
