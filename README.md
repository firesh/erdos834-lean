# Erdős Problem 834 in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib formalization of the chromatic interpretation of
[Erdős Problem #834](https://www.erdosproblems.com/834) (Erdős and Lovász, 1974):

> Is there a 3-critical 3-uniform hypergraph in which every vertex has degree at least 7?

The problem does not specify what "3-critical" means, and two inequivalent readings are in use:

* **chromatic interpretation** — a hypergraph is critically 3-chromatic if its chromatic number is
  3 while deleting any single edge or vertex makes it 2-colourable (weak colourings: no edge may be
  monochromatic);
* **transversal interpretation** — τ(H) = 3 while τ(H − e) = 2 for every edge e.

**Answer (chromatic interpretation): yes.** R. Li (*On an Erdős–Lovász problem: 3-critical
3-graphs of minimum degree 7*, [arXiv:2512.24850](https://arxiv.org/abs/2512.24850), 2025) exhibits
an explicit 3-uniform hypergraph on 9 vertices with 22 edges, all degrees at least 7 (vertex `0` has
degree 10, the other eight vertices have degree 7), which is critically 3-chromatic. This repository
formalizes that construction and its criticality.

Under the transversal interpretation Li proves the opposite answer (no such hypergraph exists: a
τ-critical 3-graph of order 3 has at most 10 edges, so its minimum degree is at most 6); that part
of the paper is *not* formalized here, and the problem recorded in the prize catalogue asks the
chromatic question.

## Main theorem

```lean
-- Erdos834/Statement.lean
abbrev Mono (c : α → β) (e : Finset α) : Prop := ∀ x ∈ e, ∀ y ∈ e, c x = c y
abbrev IsColoring (H : Finset (Finset α)) (c : α → β) : Prop := ∀ e ∈ H, ¬ Mono c e
abbrev Colorable (H : Finset (Finset α)) (k : ℕ) : Prop := ∃ c : α → Fin k, IsColoring H c
abbrev deg (H : Finset (Finset α)) (v : α) : ℕ := (H.filter fun e => v ∈ e).card

def Erdos834Statement : Prop :=
  ∃ H : Finset (Finset (Fin 9)),
    (∀ e ∈ H, e.card = 3) ∧ (∀ v : Fin 9, 7 ≤ deg H v) ∧
    Colorable H 3 ∧ ¬ Colorable H 2 ∧
    (∀ e ∈ H, Colorable (H.erase e) 2) ∧
    (∀ v : Fin 9, Colorable (H.filter fun e => v ∉ e) 2)

-- Erdos834/Main.lean
theorem Erdos834.erdos_834 : Erdos834Statement
```

The witness is the hypergraph `Erdos834.H` of `Erdos834/Construction.lean`:

```lean
def E (a b c : Fin 9) : Finset (Fin 9) := {a, b, c}

def H : Finset (Finset (Fin 9)) :=
  { E 0 1 2, E 0 1 8, E 0 2 7, E 0 3 5, E 0 3 7, E 0 3 8, E 0 4 6, E 0 4 7, E 0 4 8,
    E 0 5 6, E 1 2 5, E 1 2 6, E 1 3 8, E 1 4 8, E 1 5 6, E 2 3 7, E 2 4 7, E 2 5 6,
    E 3 5 7, E 3 5 8, E 4 6 7, E 4 6 8 }
```

(the paper labels the vertices `1, …, 9`; here they are `0, …, 8`)

```
$ lake env lean AxiomCheck.lean
'Erdos834.erdos_834' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.not_colorable_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.edge_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.vertex_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos834.colorable_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository contains no `sorry`, `admit`, `native_decide` or added axioms.

## Proof outline

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

## Attribution

* **Mathematics.** The construction and its criticality are due to **Ruiliang Li**, *On an
  Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*,
  [arXiv:2512.24850](https://arxiv.org/abs/2512.24850) (2025).  The problem is due to Erdős and
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
| `Erdos834/Statement.lean` | Colourings, degrees, the statement `Erdos834Statement` |
| `Erdos834/Construction.lean` | The hypergraph `H`, uniformity, degrees |
| `Erdos834/Certificate.lean` | 3-colouring, edge and vertex certificates, criticality |
| `Erdos834/NonColorable.lean` | Li's Lemma 4.3: `H` is not 2-colourable |
| `Erdos834/Main.lean` | `erdos_834` |
