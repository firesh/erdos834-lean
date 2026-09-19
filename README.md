# Erdős Problem 834 in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib formalization of both readings of
[Erdős Problem #834](https://www.erdosproblems.com/834) (Erdős and Lovász, 1974):

> Is there a 3-critical 3-uniform hypergraph in which every vertex has degree at least 7?

The problem does not specify what "3-critical" means, and two inequivalent readings are in use:

* **chromatic interpretation** — a hypergraph is critically 3-chromatic if its chromatic number is
  3 while deleting any single edge or vertex makes it 2-colourable (weak colourings: no edge may be
  monochromatic);
* **transversal interpretation** — τ(H) = 3 while τ(H − e) ≤ 2 for every edge e.

Both are settled by R. Li, *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*,
[arXiv:2512.24850](https://arxiv.org/abs/2512.24850) (2025), with opposite answers, and both answers
are formalized here.

**Chromatic interpretation: yes.** Li exhibits an explicit 3-uniform hypergraph on 9 vertices with
22 edges, all degrees at least 7 (vertex `0` has degree 10, the other eight vertices have degree 7),
which is critically 3-chromatic (`Erdos834.erdos_834`).

**Transversal interpretation: no.** A 3-uniform hypergraph that is τ-critical of order 3 has at
most 10 edges, so some covered vertex has degree at most 6 — the minimum degree is never 7
(`Erdos834.no_tau_critical_min_degree_seven`). The bound is sharp: the complete 3-uniform
hypergraph on 5 vertices has 10 edges, is τ-critical of order 3, and is 6-regular
(`Erdos834.K5_tau_critical`).

## Main theorems

```lean
-- Erdos834/Statement.lean
abbrev Mono (c : α → β) (e : Finset α) : Prop := ∀ x ∈ e, ∀ y ∈ e, c x = c y
abbrev IsColoring (H : Finset (Finset α)) (c : α → β) : Prop := ∀ e ∈ H, ¬ Mono c e
abbrev Colorable (H : Finset (Finset α)) (k : ℕ) : Prop := ∃ c : α → Fin k, IsColoring H c
abbrev deg (H : Finset (Finset α)) (v : α) : ℕ := (H.filter fun e => v ∈ e).card

def Erdos834Statement : Prop :=            -- chromatic interpretation
  ∃ H : Finset (Finset (Fin 9)),
    (∀ e ∈ H, e.card = 3) ∧ (∀ v : Fin 9, 7 ≤ deg H v) ∧
    Colorable H 3 ∧ ¬ Colorable H 2 ∧
    (∀ e ∈ H, Colorable (H.erase e) 2) ∧
    (∀ v : Fin 9, Colorable (H.filter fun e => v ∉ e) 2)

-- Erdos834/Bollobas.lean
abbrev IsTransversal (H : Finset (Finset α)) (T : Finset α) : Prop := ∀ e ∈ H, (T ∩ e).Nonempty
abbrev TauLe (H : Finset (Finset α)) (k : ℕ) : Prop := ∃ T, T.card ≤ k ∧ IsTransversal H T
abbrev TauGe (H : Finset (Finset α)) (k : ℕ) : Prop := ∀ T, T.card < k → ¬ IsTransversal H T

-- Erdos834/Main.lean
theorem Erdos834.erdos_834 : Erdos834Statement

-- Erdos834/Bollobas.lean
theorem Erdos834.edge_count_le_ten (H : Finset (Finset (Fin n)))
    (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3) (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    H.card ≤ 10
theorem Erdos834.exists_deg_le_six_of_finite [Fintype α] (H : Finset (Finset α))
    (h3 : ∀ e ∈ H, e.card = 3) (htau : TauGe H 3) (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, (H.filter fun e => x ∈ e).card ≤ 6

-- Erdos834/Transversal.lean
theorem Erdos834.no_tau_critical_min_degree_seven [Fintype α] (H : Finset (Finset α))
    (h3 : ∀ e ∈ H, e.card = 3) (htaule : TauLe H 3) (htauge : TauGe H 3)
    (hcrit : ∀ e ∈ H, TauLe (H.erase e) 2) :
    ∃ x ∈ cover H, deg H x ≤ 6
theorem Erdos834.K5_tau_critical :
    TauLe K5 3 ∧ TauGe K5 3 ∧ (∀ e ∈ K5, TauLe (K5.erase e) 2) ∧
      K5.card = 10 ∧ ∀ v : Fin 5, (K5.filter fun e => v ∈ e).card = 6
```

```
$ lake env lean AxiomCheck.lean
'Erdos834.erdos_834' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.not_colorable_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.edge_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.vertex_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.colorable_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.edge_count_le_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.exists_deg_le_six_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.no_tau_critical_min_degree_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.K5_tau_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository contains no `sorry`, `admit`, `native_decide` or added axioms.

## Proof outline: the chromatic interpretation

**Uniformity and degrees** (`Construction.lean`).  A direct computation on the 22 listed edges: each
has exactly three vertices, vertex `0` lies in ten of them and each of the other eight vertices in
exactly seven, so the minimum degree is `7`.

**3-colourability** (`Certificate.lean`).  The paper's colouring
`ψ(1) = ψ(2) = ψ(4) = ψ(5) = 1`, `ψ(3) = ψ(6) = ψ(8) = ψ(9) = 2`, `ψ(7) = 3` is recorded as
`threeColoring` and checked to leave no monochromatic edge.

**Not 2-colourable** (`NonColorable.lean`, Li's Lemma 4.3).  Suppose `c` is a proper 2-colouring.
Swapping the two colours if necessary, `c 0 = 0`.  Split the other eight vertices into
`Z = {v ≠ 0 : c v = 0}` and `A = {v ≠ 0 : c v = 1}`.

* Every 4-subset of the nonzero vertices contains a pair `{x, y}` with `{0, x, y} ∈ H`
  (this is the statement that the paper's graph `G`, whose edges are the pairs `{x, y}` with
  `{1, x, y} ∈ E(H)`, has independence number 3).  Hence `|Z| ≤ 3`: two elements of `Z` lying on
  an edge through vertex `0` would make that edge entirely of colour `0`.
* Therefore `|A| = 8 − |Z| ≥ 5`, and every 5-subset of the nonzero vertices contains an edge of `H`
  avoiding vertex `0`; all of its vertices lie in `A`, so it is monochromatic.  Contradiction.

Both finite ingredients are stated as `four_subset` and `five_subset` and verified by exhaustive
kernel-checked enumeration of the 512 subsets (`decide`).

**Edge- and vertex-criticality** (`Certificate.lean`).  Li certifies these by explicit colourings
(his Tables 1 and 2): for every edge `e`, a 2-colouring in which `e` is the unique monochromatic
edge — equivalently a proper 2-colouring of `H − e` (his Lemma 2.2) — and for every vertex `v`, a
proper 2-colouring of `H − v`.  Both tables are transcribed (`edgeCerts`, `vertexCerts`) and the
claim that each listed colouring does what it should is again checked by exhaustive enumeration; a
final finite check shows that the tables cover all 22 edges and all 9 vertices.

## Proof outline: the transversal interpretation

**Counting permutations** (`Bollobas.lean`).  For disjoint `A`, `B ⊆ Fin n`, let `beforeSet A B` be
the set of permutations in which every element of `A` precedes every element of `B`.  The number of
these is `n! · #A! · #B! / #(A ∪ B)!`: the file builds an explicit injection into `beforeSet A B`
from the product of the `#A!` orderings of `A`, the `#B!` orderings of `B`, the `C(n, #(A ∪ B))`
choices of the position set `P` of `A ∪ B`, and the `(n − #(A ∪ B))!` bijections from the
complementary positions onto the complementary points (`toPerm`, with injectivity from the fact
that a permutation determines its position set and the two orderings).  Counting the domain with
`Fintype.card_equiv`, `Finset.card_powersetCard` and `Nat.choose_mul_factorial_mul_factorial` gives
`card_beforeSet`, and hence `n! ≤ 10 · #(beforeSet A B)` when `#A = 3` and `#B = 2`.

**Bollobás's set-pairs inequality** (`setPairs_three_two`).  If `(A i, B i)` are disjoint pairs of
sizes `3` and `2` with `A i ∩ B j ≠ ∅` for `i ≠ j`, then the events "`A i` precedes `B i`" are
pairwise disjoint subsets of the `n!` permutations (the paper's argument: `x ∈ A i ∩ B j` and
`y ∈ A j ∩ B i` give opposite orderings of `x` and `y`), so summing the counting bound gives
`Fintype.card ι ≤ 10`.

**The edge bound and its corollary** (`edge_count_le_ten`, `exists_deg_le_six`).  For a 3-uniform
hypergraph with `τ(H) ≥ 3` and `τ(H − e) ≤ 2` for every edge `e`, each edge `e` has an associated
2-set `B e` that is disjoint from `e` and meets every other edge: this follows from the two
hypotheses by the short argument of the paper's Theorem 3.2 (a transversal of `H − e` of size ≤ 1
would give a transversal of `H` of size ≤ 2).  Applying the set-pairs bound to `(e, B e)` yields
`H.card ≤ 10`, and double counting `∑ deg = 3 · H.card` over the at least five covered vertices
(there is no 2-set transversal) gives a vertex of degree at most `10 · 3 / 5 = 6`.

**Sharpness** (`Transversal.lean`).  The complete 3-uniform hypergraph `K5` on five vertices has 10
edges, every 2-set misses the complementary 3-subset (so `τ(K5) = 3`), the complement of an edge
meets every other edge (so `τ(K5 − e) ≤ 2`), and every vertex lies in `C(4,2) = 6` edges.

**Arbitrary vertex types.**  The results are first proved for hypergraphs on `Fin n` and then
transported along `Fintype.equivFin α` to hypergraphs on an arbitrary finite type (`relabel` and
its preservation lemmas), so the final statements carry no ordering or labelling assumption.

## Attribution

* **Mathematics.** Both results are due to **Ruiliang Li**, *On an Erdős–Lovász problem: 3-critical
  3-graphs of minimum degree 7*, [arXiv:2512.24850](https://arxiv.org/abs/2512.24850) (2025): the
  chromatic construction is his Theorem 1.2 (Theorem 4.1 with Lemmas 4.2–4.4 and Propositions
  4.5–4.6), and the transversal bound is his Theorem 1.1 (Bollobás's set-pairs inequality, Lemma
  3.1, with Theorem 3.2, Corollary 3.4 and Proposition 3.5).  The problem is due to Erdős and
  Lovász (1974), as recorded on [erdosproblems.com/834](https://www.erdosproblems.com/834).
* **Formalization.** Written by the owner of this repository (GitHub account `firesh`).  AI
  assistance was used in developing the formalization.

## Build

Requires the toolchain in `lean-toolchain` (Lean `v4.34.0-rc1`) and the Mathlib revision pinned in
`lake-manifest.json`.

```sh
lake exe cache get      # optional: download the Mathlib build cache
lake build
lake env lean AxiomCheck.lean
```

## Files

| File | Content |
| --- | --- |
| `Erdos834/Statement.lean` | Colourings, degrees, the chromatic statement `Erdos834Statement` |
| `Erdos834/Construction.lean` | The hypergraph `H`, uniformity, degrees |
| `Erdos834/Certificate.lean` | 3-colouring, edge and vertex certificates, criticality |
| `Erdos834/NonColorable.lean` | Li's Lemma 4.3: `H` is not 2-colourable |
| `Erdos834/Main.lean` | `erdos_834` (chromatic interpretation) |
| `Erdos834/Bollobas.lean` | The permutation count, Bollobás's inequality for (3, 2), `edge_count_le_ten`, `exists_deg_le_six`, and the transport to arbitrary finite types |
| `Erdos834/Transversal.lean` | The sharp example `K5` and `no_tau_critical_min_degree_seven` |
