/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.Coxeter

/-!
# The `Y`-diagrams of the sporadic presentations

The Coxeter presentations that milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md` records for
the sporadic groups are `Y`-diagram presentations: the Coxeter relators of a `Y_{p,q,r}` diagram
together with one further relator, the *spider relator*. This file pins the diagrams that milestone
names — `Y₄₄₃` for the Monster, `Y₄₃₃` for the Baby Monster, and `Y₄₄₄`, from which the counts are
cross-checked — with their node numbering, their spider relator, and their relator counts.

The counts are the check, and they are checked against published data rather than only against
themselves. J. N. Bray's presentation pages record `Y₄₄₃` as a 12-generator, 79-relator
presentation of `M × 2` and `Y₄₄₄` as a 13-generator, 92-relator presentation of `(M × M) : 2`.
Here `TauCeti.length_y443Relators` and `TauCeti.length_coxeterRelators_y444` reproduce `79 = 78 + 1`
and `92 = 91 + 1`, the extra relator in each case being the spider relator; the roadmap's `80` for
the Monster is that `79` plus the relator `Z = 1` for the central involution. Two independent
published counts agreeing with one formula is what fixes the encoding convention, namely that the
diagonal entries `mᵢᵢ = 1` contribute the involution relators and each off-diagonal unordered pair
contributes exactly one relator.

## Main definitions

* `TauCeti.ySpiderRelator`: the spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y`-diagram.
* `TauCeti.y443CoxeterMatrix`, `TauCeti.y443SpiderRelator`, and `TauCeti.y443Relators`: the `Y₄₄₃`
  diagram, its spider relator, and the relator list they make up.

## Main results

* `TauCeti.length_y443Relators`, `TauCeti.length_coxeterRelators_y444`, and
  `TauCeti.length_coxeterRelators_y433`: the relator counts of the three diagrams.
* `TauCeti.y443SpiderRelator_eq`: the spider word spelled out against the pinned node numbering.
* `TauCeti.y443RelatorsMulEquiv`: the group presented by `TauCeti.y443Relators` is the Coxeter
  group of the diagram with the spider relation imposed on top.

## References

The node numbering, the arm labels `a, bᵢ, cᵢ, dᵢ, eᵢ`, the spider word, and the relator counts `79`
and `92` follow J. N. Bray's
[presentation pages](https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html). The theorems
that these diagrams present the groups in question are Norton's (1990) and Ivanov's (1999) and are
not formalized here: no presentation of a named group is asserted in this file.
-/

public section

namespace TauCeti

/-- The spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y_{p,q,r}` diagram, where `a` is the
central node and `bᵢ, cᵢ` are the first two nodes of the `i`-th arm. Each arm needs two nodes for
these to be arm nodes, which is what the hypotheses record. -/
def ySpiderRelator (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) (k : ℕ) :
    Relator (Fin (p + q + r + 1)) :=
  .pow (Relator.ofGenerators ⟨0, by omega⟩
    [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩,
      ⟨p + 1, by omega⟩, ⟨p + 2, by omega⟩, ⟨0, by omega⟩,
      ⟨p + q + 1, by omega⟩, ⟨p + q + 2, by omega⟩]) k

/-- The spider relator spelled out: the `k`-th power of the word whose letters are, in order, the
centre, the first two nodes of the first arm, the centre, the first two nodes of the second arm,
the centre, and the first two nodes of the third arm. -/
theorem ySpiderRelator_eq (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) (k : ℕ) :
    ySpiderRelator p q r hp hq hr k =
      .pow (Relator.ofGenerators ⟨0, by omega⟩
        [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩,
          ⟨p + 1, by omega⟩, ⟨p + 2, by omega⟩, ⟨0, by omega⟩,
          ⟨p + q + 1, by omega⟩, ⟨p + q + 2, by omega⟩]) k := by
  rw [ySpiderRelator]

/-! ### The `Y₄₄₃` diagram

The twelve nodes are numbered `a = 0`, `b₁ c₁ d₁ e₁ = 1 2 3 4`, `b₂ c₂ d₂ e₂ = 5 6 7 8`, and
`b₃ c₃ d₃ = 9 10 11`, so that Bray's diagram

```text
e₁ -- d₁ -- c₁ -- b₁ -- a -- b₂ -- c₂ -- d₂ -- e₂
                        |
                        b₃ -- c₃ -- d₃
```

is `4 -- 3 -- 2 -- 1 -- 0 -- 5 -- 6 -- 7 -- 8` with the arm `0 -- 9 -- 10 -- 11`. -/

/-- The Coxeter matrix of the `Y₄₄₃` diagram, on twelve nodes. -/
abbrev y443CoxeterMatrix : CoxeterMatrix (Fin 12) := yCoxeterMatrix 4 4 3

/-- The spider relator of the `Y₄₄₃` diagram, `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ 10`. -/
def y443SpiderRelator : Relator (Fin 12) :=
  ySpiderRelator 4 4 3 (by omega) (by omega) (by omega) 10

/-- The spider relator of `Y₄₄₃` spelled out against the node numbering above. -/
theorem y443SpiderRelator_eq :
    y443SpiderRelator = .pow (Relator.ofGenerators 0 [1, 2, 0, 5, 6, 0, 9, 10]) 10 := by
  rw [y443SpiderRelator, ySpiderRelator]
  rfl

/-- The relators of the `Y₄₄₃` presentation: the Coxeter relators of the diagram followed by the
spider relator. -/
def y443Relators : List (Relator (Fin 12)) :=
  coxeterRelators y443CoxeterMatrix ++ [y443SpiderRelator]

/-- The `Y₄₄₃` relator list spelled out, for a consumer that needs to decompose it. -/
theorem y443Relators_eq :
    y443Relators = coxeterRelators y443CoxeterMatrix ++ [y443SpiderRelator] := by
  rw [y443Relators]

/-- The `Y₄₄₃` diagram has `78` Coxeter relators, so the presentation has `79`. This is the count
Bray records for the group `M × 2` that `Y₄₄₃` presents; a presentation of the Monster itself adds
one further relator, `Z = 1` for the central involution, for `80`. -/
theorem length_y443Relators : y443Relators.length = 79 := by
  rw [y443Relators, List.length_append, length_coxeterRelators]
  rfl

/-- The group presented by the `Y₄₄₃` relator list is the Coxeter group of the diagram with the
spider relation imposed on top. -/
def y443RelatorsMulEquiv :
    PresentedGroup (Relator.relatorSet y443Relators) ≃*
      PresentedGroup (y443CoxeterMatrix.relationsSet ∪ Relator.relatorSet [y443SpiderRelator]) :=
  mulEquivPresentedGroupCoxeterAppend y443CoxeterMatrix [y443SpiderRelator]

/-- The `Y₄₄₄` diagram, on thirteen nodes, has `91` Coxeter relators. Adding its spider relator
gives the `92` relators Bray records for its presentation of `(M × M) : 2`. -/
theorem length_coxeterRelators_y444 :
    (coxeterRelators (yCoxeterMatrix 4 4 4)).length = 91 := by
  rw [length_coxeterRelators]
  rfl

/-- The `Y₄₃₃` diagram, on eleven nodes, has `66` Coxeter relators. -/
theorem length_coxeterRelators_y433 :
    (coxeterRelators (yCoxeterMatrix 4 3 3)).length = 66 := by
  rw [length_coxeterRelators]
  rfl

/-! ### Executable checks on the pinned `Y₄₄₃` numbering

Each entry of the Coxeter matrix is `3` on an edge of the diagram and `2` off it, so these examples
read the diagram back out of the definition. The `Y`-diagram entries are unfolded through the
characteristic lemmas `TauCeti.yCoxeterMatrix_apply`, `TauCeti.YAdjacent_iff`, and
`TauCeti.yParent_eq` before the arithmetic is decided. -/

/-- The centre is joined to the first node of each of the three arms. -/
example : y443CoxeterMatrix 0 1 = 3 ∧ y443CoxeterMatrix 0 5 = 3 ∧ y443CoxeterMatrix 0 9 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

/-- The first arm is the chain `0 -- 1 -- 2 -- 3 -- 4`. -/
example : y443CoxeterMatrix 1 2 = 3 ∧ y443CoxeterMatrix 2 3 = 3 ∧ y443CoxeterMatrix 3 4 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

/-- The second arm is the chain `0 -- 5 -- 6 -- 7 -- 8`. -/
example : y443CoxeterMatrix 5 6 = 3 ∧ y443CoxeterMatrix 6 7 = 3 ∧ y443CoxeterMatrix 7 8 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

/-- The third arm is the chain `0 -- 9 -- 10 -- 11`, of length three rather than four. -/
example : y443CoxeterMatrix 9 10 = 3 ∧ y443CoxeterMatrix 10 11 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

/-- Distinct arms meet only at the centre, and no arm doubles back to it. -/
example : y443CoxeterMatrix 1 5 = 2 ∧ y443CoxeterMatrix 1 9 = 2 ∧ y443CoxeterMatrix 5 9 = 2 ∧
    y443CoxeterMatrix 0 2 = 2 ∧ y443CoxeterMatrix 0 4 = 2 ∧ y443CoxeterMatrix 4 8 = 2 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

/-- The last node of the second arm is `8`, so `Y₄₄₃` has no node `12`: the arm ends rather than
continuing into the third arm. -/
example : y443CoxeterMatrix 8 9 = 2 := by
  simp only [yCoxeterMatrix_apply, YAdjacent_iff, yParent_eq]
  decide

end TauCeti
