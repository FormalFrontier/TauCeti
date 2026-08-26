/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Brauer diagrams and their edges

A **Brauer diagram** on `k` strands is a perfect matching of the `2k` boundary points of a
rectangle, `k` on the bottom and `k` on the top. Encoding the boundary as `Fin k ⊕ Fin k`, with
`Sum.inl` the bottom row and `Sum.inr` the top row, a perfect matching is exactly a
fixed-point-free involution, and that is the definition taken here.

Each arc of a diagram is of one of three kinds. A **through-strand** joins a bottom point to a
top point; a **cap** is a horizontal arc joining two bottom points; a **cup** is a horizontal arc
joining two top points. The three predicates `isThrough`, `isCap`, `isCup` are stated at a single
boundary point rather than at an arc, so that they are directly usable as predicates on
`Fin k ⊕ Fin k`; each says something about the point and its partner, and every boundary point
satisfies exactly one of them.

This file builds that combinatorial substrate and proves the two structural facts about it that
do not need the algebra: the diagrams with no horizontal arc are exactly the `k!` permutation
diagrams `ofPerm σ`, and every diagram has as many caps as cups. The second is the reason a
Brauer diagram has a well-defined number of through-strands on each side; it is the bookkeeping
that the loop rule of the Brauer algebra rests on.

The permutation diagram map here is at the level of diagrams; the algebra-level inclusion
`ℂ[Sₖ] ↪ B_k(δ)` that the roadmap calls `permToBrauer` factors through it once the Brauer algebra
itself is built.

This is the diagram combinatorics of Layer 9 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
whose `## Ordering` paragraph makes that layer's diagram combinatorics an independent lane.
The relations satisfied by the two-strand diagrams acting on a tensor square are in
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators.lean`.

## Main definitions

* `TauCeti.brauerDiagram k` is the type of Brauer diagrams on `k` strands.
* `TauCeti.brauerDiagram.isThrough`, `TauCeti.brauerDiagram.isCap` and
  `TauCeti.brauerDiagram.isCup` are the three edge types at a boundary point.
* `TauCeti.brauerDiagram.ofPerm` is the permutation diagram of a permutation of `Fin k`.
* `TauCeti.brauerDiagram.throughEquiv` is the bijection from the bottom through-points to the top
  through-points given by following the strands.
* `TauCeti.brauerDiagram.permEquivThrough` identifies the permutations of `Fin k` with the
  diagrams all of whose arcs are through-strands.

## Main results

* `TauCeti.brauerDiagram.isThrough_or_isCap_or_isCup` and
  `TauCeti.brauerDiagram.not_isThrough_inl_iff`: the edge type of a boundary point is determined
  and exhaustive.
* `TauCeti.brauerDiagram.card_forall_isThrough`: there are `k !` diagrams with no horizontal arc.
* `TauCeti.brauerDiagram.card_isCap_eq_card_isCup`: a Brauer diagram has as many caps as cups.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937]
* [R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*][goodman-wallach2009]
-/

public section

open scoped Nat

namespace TauCeti

/-- A **Brauer diagram** on `k` strands: a perfect matching of the `2k` boundary points
`Fin k ⊕ Fin k` (`Sum.inl` the bottom row, `Sum.inr` the top row), encoded as a fixed-point-free
involution of the boundary. The matchings with no horizontal arc are the permutation diagrams
`brauerDiagram.ofPerm`; the rest carry caps and cups. -/
abbrev brauerDiagram (k : ℕ) : Type :=
  {f : Fin k ⊕ Fin k → Fin k ⊕ Fin k // Function.Involutive f ∧ ∀ x, f x ≠ x}

namespace brauerDiagram

variable {k : ℕ}

/-- The matching of a Brauer diagram is an involution. -/
theorem involutive (D : brauerDiagram k) : Function.Involutive D.1 := D.2.1

/-- Following an arc of a Brauer diagram twice returns to where it started. -/
@[simp]
theorem apply_apply (D : brauerDiagram k) (x : Fin k ⊕ Fin k) : D.1 (D.1 x) = x := D.involutive x

/-- A Brauer diagram has no fixed point: every boundary point is matched to a different one. -/
theorem apply_ne (D : brauerDiagram k) (x : Fin k ⊕ Fin k) : D.1 x ≠ x := D.2.2 x

/-- The boundary point `x` lies on a **through-strand** of `D`: it is matched to a point on the
opposite side of the diagram. -/
def isThrough (D : brauerDiagram k) (x : Fin k ⊕ Fin k) : Prop :=
  x.isLeft ≠ (D.1 x).isLeft

/-- The boundary point `x` lies on a **cap** of `D`: a horizontal arc joining two bottom
points. -/
def isCap (D : brauerDiagram k) (x : Fin k ⊕ Fin k) : Prop :=
  x.isLeft = true ∧ (D.1 x).isLeft = true

/-- The boundary point `x` lies on a **cup** of `D`: a horizontal arc joining two top points. -/
def isCup (D : brauerDiagram k) (x : Fin k ⊕ Fin k) : Prop :=
  x.isLeft = false ∧ (D.1 x).isLeft = false

/-- Every boundary point lies on a through-strand, a cap, or a cup. -/
theorem isThrough_or_isCap_or_isCup (D : brauerDiagram k) (x : Fin k ⊕ Fin k) :
    D.isThrough x ∨ D.isCap x ∨ D.isCup x := by
  by_cases h : x.isLeft = (D.1 x).isLeft
  · cases hx : x.isLeft
    · exact Or.inr (Or.inr ⟨hx, by rw [← h, hx]⟩)
    · exact Or.inr (Or.inl ⟨hx, by rw [← h, hx]⟩)
  · exact Or.inl h

/-- A cap and a cup never meet: they live on opposite sides of the diagram. -/
theorem not_isCap_of_isCup (D : brauerDiagram k) {x : Fin k ⊕ Fin k} (h : D.isCup x) :
    ¬ D.isCap x := fun h' => Bool.false_ne_true (h.1.symm.trans h'.1)

/-- A capped point does not lie on a through-strand. -/
theorem not_isThrough_of_isCap (D : brauerDiagram k) {x : Fin k ⊕ Fin k} (h : D.isCap x) :
    ¬ D.isThrough x := fun h' => h' (h.1.trans h.2.symm)

/-- A cupped point does not lie on a through-strand. -/
theorem not_isThrough_of_isCup (D : brauerDiagram k) {x : Fin k ⊕ Fin k} (h : D.isCup x) :
    ¬ D.isThrough x := fun h' => h' (h.1.trans h.2.symm)

/-- Both endpoints of an arc have the same edge type: through-strands are preserved by the
matching. -/
@[simp]
theorem isThrough_apply (D : brauerDiagram k) (x : Fin k ⊕ Fin k) :
    D.isThrough (D.1 x) ↔ D.isThrough x := by
  simp only [isThrough, apply_apply, ne_eq, ne_comm]

/-- Both endpoints of an arc have the same edge type: caps are preserved by the matching. -/
@[simp]
theorem isCap_apply (D : brauerDiagram k) (x : Fin k ⊕ Fin k) :
    D.isCap (D.1 x) ↔ D.isCap x := by
  simp only [isCap, apply_apply, and_comm]

/-- Both endpoints of an arc have the same edge type: cups are preserved by the matching. -/
@[simp]
theorem isCup_apply (D : brauerDiagram k) (x : Fin k ⊕ Fin k) :
    D.isCup (D.1 x) ↔ D.isCup x := by
  simp only [isCup, apply_apply, and_comm]

/-- A bottom point that is not on a through-strand is capped. -/
theorem not_isThrough_inl_iff (D : brauerDiagram k) (i : Fin k) :
    ¬ D.isThrough (Sum.inl i) ↔ D.isCap (Sum.inl i) := by
  simp [isThrough, isCap]

/-- A top point that is not on a through-strand is cupped. -/
theorem not_isThrough_inr_iff (D : brauerDiagram k) (j : Fin k) :
    ¬ D.isThrough (Sum.inr j) ↔ D.isCup (Sum.inr j) := by
  simp [isThrough, isCup]

/-- A top point is never capped. -/
theorem not_isCap_inr (D : brauerDiagram k) (j : Fin k) : ¬ D.isCap (Sum.inr j) := by
  simp [isCap]

/-- A bottom point is never cupped. -/
theorem not_isCup_inl (D : brauerDiagram k) (i : Fin k) : ¬ D.isCup (Sum.inl i) := by
  simp [isCup]

/-- A bottom point on a through-strand is matched to a top point. -/
theorem exists_apply_inl (D : brauerDiagram k) {i : Fin k} (h : D.isThrough (Sum.inl i)) :
    ∃ j, D.1 (Sum.inl i) = Sum.inr j := by
  rcases hx : D.1 (Sum.inl i) with a | b
  · exact absurd h (by simp [isThrough, hx])
  · exact ⟨b, rfl⟩

/-- A top point on a through-strand is matched to a bottom point. -/
theorem exists_apply_inr (D : brauerDiagram k) {j : Fin k} (h : D.isThrough (Sum.inr j)) :
    ∃ i, D.1 (Sum.inr j) = Sum.inl i := by
  rcases hx : D.1 (Sum.inr j) with a | b
  · exact ⟨a, rfl⟩
  · exact absurd h (by simp [isThrough, hx])

/-- Following the through-strand out of a bottom point lands on a top point that is itself on a
through-strand. -/
theorem isThrough_inr_elim (D : brauerDiagram k) {i : Fin k} (h : D.isThrough (Sum.inl i)) :
    D.isThrough (Sum.inr (Sum.elim id id (D.1 (Sum.inl i)))) := by
  obtain ⟨j, hj⟩ := D.exists_apply_inl h
  have hj' : D.isThrough (Sum.inr j) := hj ▸ (D.isThrough_apply (Sum.inl i)).mpr h
  simpa [hj] using hj'

/-- Following the through-strand out of a top point lands on a bottom point that is itself on a
through-strand. -/
theorem isThrough_inl_elim (D : brauerDiagram k) {j : Fin k} (h : D.isThrough (Sum.inr j)) :
    D.isThrough (Sum.inl (Sum.elim id id (D.1 (Sum.inr j)))) := by
  obtain ⟨i, hi⟩ := D.exists_apply_inr h
  have hi' : D.isThrough (Sum.inl i) := hi ▸ (D.isThrough_apply (Sum.inr j)).mpr h
  simpa [hi] using hi'

/-- **Following the strands** bijects the bottom points of `D` that lie on through-strands with
the top points that do. Consequently the number of caps and the number of cups of `D` agree; see
`brauerDiagram.card_isCap_eq_card_isCup`. -/
def throughEquiv (D : brauerDiagram k) :
    {i : Fin k // D.isThrough (Sum.inl i)} ≃ {j : Fin k // D.isThrough (Sum.inr j)} where
  toFun i := ⟨Sum.elim id id (D.1 (Sum.inl i.1)), D.isThrough_inr_elim i.2⟩
  invFun j := ⟨Sum.elim id id (D.1 (Sum.inr j.1)), D.isThrough_inl_elim j.2⟩
  left_inv i := Subtype.ext (by
    obtain ⟨j, hj⟩ := D.exists_apply_inl i.2
    have h2 : D.1 (Sum.inr j) = Sum.inl i.1 := by rw [← hj, D.apply_apply]
    simp [hj, h2])
  right_inv j := Subtype.ext (by
    obtain ⟨i, hi⟩ := D.exists_apply_inr j.2
    have h2 : D.1 (Sum.inl i) = Sum.inr j.1 := by rw [← hi, D.apply_apply]
    simp [hi, h2])

/-- The **permutation diagram** of `σ`: the matching joining the bottom point `i` to the top
point `σ i`. Its arcs are all through-strands, and by
`brauerDiagram.permEquivThrough` these are all such diagrams. -/
def ofPerm (σ : Equiv.Perm (Fin k)) : brauerDiagram k :=
  ⟨Sum.elim (fun i => Sum.inr (σ i)) (fun j => Sum.inl (σ.symm j)), by
    refine ⟨fun x => ?_, fun x => ?_⟩ <;> rcases x with i | j <;> simp⟩

@[simp]
theorem ofPerm_val_inl (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (ofPerm σ).1 (Sum.inl i) = Sum.inr (σ i) := (rfl)

@[simp]
theorem ofPerm_val_inr (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    (ofPerm σ).1 (Sum.inr j) = Sum.inl (σ.symm j) := (rfl)

/-- A permutation diagram has no horizontal arc. -/
theorem isThrough_ofPerm (σ : Equiv.Perm (Fin k)) (x : Fin k ⊕ Fin k) :
    (ofPerm σ).isThrough x := by
  rcases x with i | j <;> simp [isThrough]

/-- Distinct permutations give distinct diagrams. -/
theorem ofPerm_injective : Function.Injective (ofPerm (k := k)) := fun σ τ h =>
  Equiv.ext fun i => by
    simpa using congrArg (fun D : brauerDiagram k => D.1 (Sum.inl i)) h

/-- The permutation underlying a diagram all of whose arcs are through-strands: it sends the
bottom point `i` to the label of the top point that `i` is matched to. -/
def throughPerm (D : brauerDiagram k) (hD : ∀ x, D.isThrough x) : Equiv.Perm (Fin k) :=
  (Equiv.subtypeUnivEquiv fun i => hD (Sum.inl i)).symm.trans
    (D.throughEquiv.trans (Equiv.subtypeUnivEquiv fun j => hD (Sum.inr j)))

@[simp]
theorem throughPerm_apply (D : brauerDiagram k) (hD : ∀ x, D.isThrough x) (i : Fin k) :
    D.throughPerm hD i = Sum.elim id id (D.1 (Sum.inl i)) := (rfl)

@[simp]
theorem throughPerm_symm_apply (D : brauerDiagram k) (hD : ∀ x, D.isThrough x) (j : Fin k) :
    (D.throughPerm hD).symm j = Sum.elim id id (D.1 (Sum.inr j)) := (rfl)

/-- A diagram with no horizontal arc is the permutation diagram of its underlying
permutation. -/
@[simp]
theorem ofPerm_throughPerm (D : brauerDiagram k) (hD : ∀ x, D.isThrough x) :
    ofPerm (D.throughPerm hD) = D := by
  refine Subtype.ext (funext fun x => ?_)
  rcases x with i | j
  · obtain ⟨j, hj⟩ := D.exists_apply_inl (hD (Sum.inl i))
    simp [hj]
  · obtain ⟨i, hi⟩ := D.exists_apply_inr (hD (Sum.inr j))
    simp [hi]

/-- **The permutation diagrams are exactly the diagrams with no horizontal arc.** -/
def permEquivThrough (k : ℕ) :
    Equiv.Perm (Fin k) ≃ {D : brauerDiagram k // ∀ x, D.isThrough x} where
  toFun σ := ⟨ofPerm σ, isThrough_ofPerm σ⟩
  invFun D := D.1.throughPerm D.2
  left_inv _ := ofPerm_injective (ofPerm_throughPerm _ _)
  right_inv D := Subtype.ext (ofPerm_throughPerm D.1 D.2)

/-- There are `k !` Brauer diagrams on `k` strands with no horizontal arc. -/
theorem card_forall_isThrough (k : ℕ) :
    Nat.card {D : brauerDiagram k // ∀ x, D.isThrough x} = k ! := by
  rw [← Nat.card_congr (permEquivThrough k), Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

/-- Every bottom point is either on a through-strand or capped, so the two counts add to `k`. -/
theorem card_isThrough_add_card_isCap (D : brauerDiagram k) :
    Nat.card {i : Fin k // D.isThrough (Sum.inl i)}
      + Nat.card {i : Fin k // D.isCap (Sum.inl i)} = k := by
  classical
  have e : {i : Fin k // D.isThrough (Sum.inl i)} ⊕ {i : Fin k // D.isCap (Sum.inl i)} ≃ Fin k :=
    (Equiv.sumCongr (Equiv.refl _)
        (Equiv.subtypeEquivRight fun i => (D.not_isThrough_inl_iff i).symm)).trans
      (Equiv.sumCompl fun i : Fin k => D.isThrough (Sum.inl i))
  have h := Nat.card_congr e
  rwa [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at h

/-- Every top point is either on a through-strand or cupped, so the two counts add to `k`. -/
theorem card_isThrough_add_card_isCup (D : brauerDiagram k) :
    Nat.card {j : Fin k // D.isThrough (Sum.inr j)}
      + Nat.card {j : Fin k // D.isCup (Sum.inr j)} = k := by
  classical
  have e : {j : Fin k // D.isThrough (Sum.inr j)} ⊕ {j : Fin k // D.isCup (Sum.inr j)} ≃ Fin k :=
    (Equiv.sumCongr (Equiv.refl _)
        (Equiv.subtypeEquivRight fun j => (D.not_isThrough_inr_iff j).symm)).trans
      (Equiv.sumCompl fun j : Fin k => D.isThrough (Sum.inr j))
  have h := Nat.card_congr e
  rwa [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at h

/-- **A Brauer diagram has as many caps as cups.** The through-strands match the uncapped bottom
points with the uncupped top points, and both rows have `k` points. -/
theorem card_isCap_eq_card_isCup (D : brauerDiagram k) :
    Nat.card {i : Fin k // D.isCap (Sum.inl i)}
      = Nat.card {j : Fin k // D.isCup (Sum.inr j)} := by
  have h₁ := D.card_isThrough_add_card_isCap
  have h₂ := D.card_isThrough_add_card_isCup
  have h₃ : Nat.card {i : Fin k // D.isThrough (Sum.inl i)}
      = Nat.card {j : Fin k // D.isThrough (Sum.inr j)} := Nat.card_congr D.throughEquiv
  omega

end brauerDiagram

end TauCeti
