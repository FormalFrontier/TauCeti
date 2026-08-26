/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Reorienting a quiver

A `Bool`-valued labelling `σ` of the arrows of a quiver `Q` specifies a change of orientation: this
file builds the quiver `TauCeti.Reorient Q σ`, whose arrows are those of `Q` with the ones labelled
`true` turned around.

The two doubled quivers `Quiver.Symmetrify (Reorient Q σ)` and `Quiver.Symmetrify Q` carry exactly
the same arrows, distributed differently between an arrow and its formal reverse. That is the
content of `TauCeti.reorientSymmetrify` and `TauCeti.reorientSymmetrifyInv`, mutually inverse
prefunctors which are the identity on vertices and commute with reversal. They are the
identification along which a construction on doubled quivers -- the additive preprojective algebra
-- is compared across a change of orientation.

## Main definitions

* `TauCeti.Reorient`: the quiver `Q` with the arrows labelled `true` by `σ` turned around.
* `TauCeti.reorientHomEquiv`: the identification of a hom set of `Reorient Q σ` with the two
  subtypes of hom sets of `Q` it is built from, together with `TauCeti.reorientHom_induction_on` the
  general elimination interface for a reoriented arrow.
* `TauCeti.reorientSymmetrify` and `TauCeti.reorientSymmetrifyInv`: the two prefunctors between
  the doubled quivers.

## Main results

* `TauCeti.reorientSymmetrify_comp_reorientSymmetrifyInv` and
  `TauCeti.reorientSymmetrifyInv_comp_reorientSymmetrify`: the two prefunctors are inverse, so the
  two doubled quivers are isomorphic.
* `TauCeti.reorientSymmetrify_map_reverse`: the comparison commutes with arrow reversal.

## Implementation notes

`Reorient Q σ` is a semireducible type synonym for `Q`, following `Quiver.Symmetrify`: were it
reducible, instance search would unfold it and replace the reoriented quiver structure by that of
`Q`. Its arrows `i ⟶ j` are the disjoint union of the arrows `i ⟶ j` of `Q` which `σ` leaves alone
and the arrows `j ⟶ i` of `Q` which `σ` turns around, so a hom set of the doubled quiver
`Symmetrify (Reorient Q σ)` splits into four pieces. Sorting an arrow of `Symmetrify Q` into those
four pieces is what `TauCeti.reorientSymmetrifyInv` does, and it is why that prefunctor, unlike its
inverse, is defined by a case distinction on the value of `σ`.

Turning around a *single* arrow is the special case where `σ` is supported on one arrow; allowing
an arbitrary `σ` performs an arbitrary composite of such flips in one step.

## References

This file supplies the doubled-quiver identification which the orientation-independence clause of
Layer 4 of `TauCetiRoadmap/ZigzagPreprojective/README.md` needs; see Crawley-Boevey, *Quiver
algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable (Q : Type u) [Quiver.{v + 1} Q]

/-- The quiver obtained from `Q` by turning around exactly the arrows on which the labelling `σ`
takes the value `true`: an arrow `i ⟶ j` of `Reorient Q σ` is either an arrow `i ⟶ j` of `Q` which
`σ` leaves alone, or an arrow `j ⟶ i` of `Q` which `σ` turns around. -/
@[expose]
def Reorient (_σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) : Type u := Q

variable {Q}

instance reorientQuiver (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) : Quiver.{v + 1} (Reorient Q σ) :=
  ⟨fun i j : Q => {a : i ⟶ j // ¬ σ a} ⊕ {a : j ⟶ i // σ a}⟩

instance instFiniteReorient (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) [Finite Q] :
    Finite (Reorient Q σ) :=
  inferInstanceAs (Finite Q)

instance instFintypeReorient (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) [Fintype Q] :
    Fintype (Reorient Q σ) :=
  inferInstanceAs (Fintype Q)

/-- A hom set of a reorientation is a disjoint union of two subtypes of hom sets of `Q`, hence
finite. The vertices are taken in `Q`; `TauCeti.instFintypeReorientHom` is the instance form, whose
vertices are taken in `Reorient Q σ` so that instance search can use it. -/
@[instance_reducible]
def reorientHomFintype (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q) :
    Fintype (@Quiver.Hom (Reorient Q σ) _ i j) :=
  inferInstanceAs (Fintype ({a : i ⟶ j // ¬ σ a} ⊕ {a : j ⟶ i // σ a}))

instance instFintypeReorientHom (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)
    [∀ i j : Q, Fintype (i ⟶ j)] (i j : Reorient Q σ) :
    Fintype (i ⟶ j) :=
  reorientHomFintype σ i j

/-! ### Vertices and arrows -/

variable (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- The vertex of `Reorient Q σ` underlying a vertex of `Q`. The two vertex types are
definitionally equal, so this is the identity; naming it keeps the two quiver structures apart. -/
abbrev reorientVertex (v : Q) : Reorient Q σ := v

/-- The arrow of `Reorient Q σ` carried by an arrow of `Q` which `σ` leaves alone. -/
def reorientKeep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) : reorientVertex σ i ⟶ reorientVertex σ j :=
  Sum.inl ⟨a, h⟩

/-- The arrow of `Reorient Q σ` carried by an arrow of `Q` which `σ` turns around: it runs from
the head of the original arrow to its tail. -/
def reorientFlip {i j : Q} (a : j ⟶ i) (h : σ a) : reorientVertex σ i ⟶ reorientVertex σ j :=
  Sum.inr ⟨a, h⟩

/-- **Every arrow of a reorientation is one of the two kinds**: the arrows `i ⟶ j` of
`Reorient Q σ` are the arrows `i ⟶ j` of `Q` which `σ` leaves alone together with the arrows
`j ⟶ i` of `Q` which `σ` turns around. This equivalence is the general elimination interface for a
reoriented hom set, so no consumer needs to unfold `TauCeti.reorientQuiver`;
`TauCeti.reorientHom_induction_on` is its tactic form. -/
def reorientHomEquiv (i j : Q) :
    (reorientVertex σ i ⟶ reorientVertex σ j) ≃ {a : i ⟶ j // ¬ σ a} ⊕ {a : j ⟶ i // σ a} :=
  Equiv.refl _

/-- The elimination equivalence sends an arrow `σ` leaves alone to the left summand. -/
@[simp]
theorem reorientHomEquiv_reorientKeep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) :
    reorientHomEquiv σ i j (reorientKeep σ a h) = Sum.inl ⟨a, h⟩ :=
  (rfl)

/-- The elimination equivalence sends an arrow `σ` turns around to the right summand. -/
@[simp]
theorem reorientHomEquiv_reorientFlip {i j : Q} (a : j ⟶ i) (h : σ a) :
    reorientHomEquiv σ i j (reorientFlip σ a h) = Sum.inr ⟨a, h⟩ :=
  (rfl)

/-- The left summand of the elimination equivalence is an arrow `σ` leaves alone. -/
@[simp]
theorem reorientHomEquiv_symm_inl {i j : Q} (x : {a : i ⟶ j // ¬ σ a}) :
    (reorientHomEquiv σ i j).symm (Sum.inl x) = reorientKeep σ x.1 x.2 :=
  (rfl)

/-- The right summand of the elimination equivalence is an arrow `σ` turns around. -/
@[simp]
theorem reorientHomEquiv_symm_inr {i j : Q} (y : {a : j ⟶ i // σ a}) :
    (reorientHomEquiv σ i j).symm (Sum.inr y) = reorientFlip σ y.1 y.2 :=
  (rfl)

/-- **Case analysis on an arrow of a reorientation**: it is either an arrow of `Q` which `σ` leaves
alone or an arrow of `Q` which `σ` turns around. This is the tactic form of
`TauCeti.reorientHomEquiv`. -/
@[elab_as_elim]
theorem reorientHom_induction_on {i j : Q}
    {motive : (reorientVertex σ i ⟶ reorientVertex σ j) → Prop}
    (b : reorientVertex σ i ⟶ reorientVertex σ j)
    (keep : ∀ (a : i ⟶ j) (h : ¬ σ a), motive (reorientKeep σ a h))
    (flip : ∀ (a : j ⟶ i) (h : σ a), motive (reorientFlip σ a h)) : motive b := by
  obtain ⟨a, h⟩ | ⟨a, h⟩ := b
  exacts [keep a h, flip a h]

/-- A sum over the vertices of a reorientation is a sum over the vertices of `Q`. -/
theorem sum_reorientVertex {M : Type*} [AddCommMonoid M] [Fintype Q] (f : Reorient Q σ → M) :
    ∑ v : Reorient Q σ, f v = ∑ v : Q, f (reorientVertex σ v) :=
  rfl

/-- A sum over a hom set of a reorientation splits into the arrows `σ` leaves alone and the arrows
`σ` turns around. -/
theorem sum_reorientHom {M : Type*} [AddCommMonoid M] [∀ i j : Q, Fintype (i ⟶ j)] (i j : Q)
    (f : (reorientVertex σ i ⟶ reorientVertex σ j) → M) :
    ∑ α : (reorientVertex σ i ⟶ reorientVertex σ j), f α
      = (∑ x : {a : i ⟶ j // ¬ σ a}, f (reorientKeep σ x.1 x.2))
        + ∑ y : {a : j ⟶ i // σ a}, f (reorientFlip σ y.1 y.2) :=
  Fintype.sum_sum_type _

/-! ### The doubled quivers of two orientations agree -/

/-- The comparison prefunctor from the doubled reoriented quiver to the doubled quiver. It is the
identity on vertices; on arrows it forgets which of the four pieces of a hom set of
`Symmetrify (Reorient Q σ)` an arrow came from and remembers only whether it runs forwards or
backwards in `Q`. The body is exposed because the dependent source and target types of its public
arrow-map equations contain the object map. -/
@[expose]
def reorientSymmetrify : Symmetrify (Reorient Q σ) ⥤q Symmetrify Q where
  obj := id
  map := fun {_ _} b =>
    match b with
    | Sum.inl (Sum.inl a) => Sum.inl a.1
    | Sum.inl (Sum.inr a) => Sum.inr a.1
    | Sum.inr (Sum.inl a) => Sum.inr a.1
    | Sum.inr (Sum.inr a) => Sum.inl a.1

/-- The inverse comparison: an arrow of the doubled quiver is sorted into one of the four pieces of
a hom set of `Symmetrify (Reorient Q σ)` according to whether it runs forwards or backwards in `Q`
and whether `σ` turns it around. As for `TauCeti.reorientSymmetrify`, exposure is needed for the
dependent endpoint types of its public arrow-map equations. -/
@[expose]
def reorientSymmetrifyInv : Symmetrify Q ⥤q Symmetrify (Reorient Q σ) where
  obj := id
  map := fun {_ _} b =>
    match b with
    | Sum.inl a =>
        if h : σ a then Sum.inr (Sum.inr ⟨a, h⟩) else Sum.inl (Sum.inl ⟨a, h⟩)
    | Sum.inr a =>
        if h : σ a then Sum.inl (Sum.inr ⟨a, h⟩) else Sum.inr (Sum.inl ⟨a, h⟩)

/-- The comparison of doubled quivers is the identity on vertices. -/
@[simp]
theorem reorientSymmetrify_obj (i : Symmetrify (Reorient Q σ)) :
    (reorientSymmetrify σ).obj i = i := (rfl)

/-- The inverse comparison of doubled quivers is the identity on vertices. -/
@[simp]
theorem reorientSymmetrifyInv_obj (i : Symmetrify Q) :
    (reorientSymmetrifyInv σ).obj i = i := (rfl)

/-- The defining case distinction of the inverse comparison on an arrow of `Q`, stated in terms of
`TauCeti.reorientKeep` and `TauCeti.reorientFlip`. The two sides are definitionally equal, the
`if`-branches being the two constructors of the reoriented hom set repackaged; the four public
equations below are the two instances of each branch. -/
private theorem reorientSymmetrifyInv_map_of {i j : Q} (a : i ⟶ j) :
    (reorientSymmetrifyInv σ).map (Symmetrify.of.map a) =
      if h : σ a then Quiver.reverse (Symmetrify.of.map (reorientFlip σ a h))
        else Symmetrify.of.map (reorientKeep σ a h) :=
  (rfl)

/-- The defining case distinction of the inverse comparison on the formal reverse of an arrow of
`Q`; see `TauCeti.reorientSymmetrifyInv_map_of`. -/
private theorem reorientSymmetrifyInv_map_reverse_of {i j : Q} (a : i ⟶ j) :
    (reorientSymmetrifyInv σ).map (Quiver.reverse (Symmetrify.of.map a)) =
      if h : σ a then Symmetrify.of.map (reorientFlip σ a h)
        else Quiver.reverse (Symmetrify.of.map (reorientKeep σ a h)) :=
  (rfl)

/-- The inverse comparison sends an arrow which `σ` leaves alone to the corresponding arrow of the
reoriented quiver. Deliberately not a `simp` lemma: `Quiver.Symmetrify.of_map` rewrites
`Symmetrify.of.map a` to `Sum.inl a` on the left-hand side, and `simpNF` rejects it. -/
theorem reorientSymmetrifyInv_map_of_keep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) :
    (reorientSymmetrifyInv σ).map (Symmetrify.of.map a) =
      Symmetrify.of.map (reorientKeep σ a h) := by
  rw [reorientSymmetrifyInv_map_of, dite_eq_right h]

/-- The inverse comparison sends the formal reverse of an arrow which `σ` leaves alone to the
formal reverse of the corresponding reoriented arrow. Deliberately not a `simp` lemma: simplifying
formal reversal first would make this a non-normal-form rule. -/
theorem reorientSymmetrifyInv_map_reverse_of_keep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) :
    (reorientSymmetrifyInv σ).map (Quiver.reverse (Symmetrify.of.map a)) =
      Quiver.reverse (Symmetrify.of.map (reorientKeep σ a h)) := by
  rw [reorientSymmetrifyInv_map_reverse_of, dite_eq_right h]

/-- The inverse comparison sends an arrow which `σ` turns around to the formal reverse of the
corresponding reoriented arrow. Deliberately not a `simp` lemma, for the reason recorded on
`TauCeti.reorientSymmetrifyInv_map_of_keep`. -/
theorem reorientSymmetrifyInv_map_of_flip {i j : Q} (a : i ⟶ j) (h : σ a) :
    (reorientSymmetrifyInv σ).map (Symmetrify.of.map a) =
      Quiver.reverse (Symmetrify.of.map (reorientFlip σ a h)) := by
  rw [reorientSymmetrifyInv_map_of, dite_eq_left h]

/-- The inverse comparison sends the formal reverse of an arrow which `σ` turns around to the
corresponding reoriented arrow. Deliberately not a `simp` lemma, for the reason recorded on
`TauCeti.reorientSymmetrifyInv_map_reverse_of_keep`. -/
theorem reorientSymmetrifyInv_map_reverse_of_flip {i j : Q} (a : i ⟶ j) (h : σ a) :
    (reorientSymmetrifyInv σ).map (Quiver.reverse (Symmetrify.of.map a)) =
      Symmetrify.of.map (reorientFlip σ a h) := by
  rw [reorientSymmetrifyInv_map_reverse_of, dite_eq_left h]

/-- An arrow of `Q` which `σ` leaves alone stays an arrow of the doubled quiver. Deliberately not a
`simp` lemma: `Quiver.Symmetrify.of_map` rewrites `Symmetrify.of.map ...` to `Sum.inl ...` on the
left-hand side, and `simpNF` rejects it. -/
theorem reorientSymmetrify_map_of_keep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) :
    (reorientSymmetrify σ).map (Symmetrify.of.map (reorientKeep σ a h)) =
      Symmetrify.of.map a :=
  (rfl)

/-- The formal reverse of an arrow which `σ` leaves alone stays a formal reverse. Deliberately not
a `simp` lemma: `Quiver.symmetrify_reverse` rewrites `Quiver.reverse` to `Sum.swap` on the left-hand
side, and `simpNF` rejects the pair. -/
theorem reorientSymmetrify_map_reverse_of_keep {i j : Q} (a : i ⟶ j) (h : ¬ σ a) :
    (reorientSymmetrify σ).map (Quiver.reverse (Symmetrify.of.map (reorientKeep σ a h))) =
      Quiver.reverse (Symmetrify.of.map a) :=
  (rfl)

/-- An arrow of `Q` which `σ` turns around becomes the formal reverse of itself. Deliberately not a
`simp` lemma, for the reason recorded on `TauCeti.reorientSymmetrify_map_of_keep`. -/
theorem reorientSymmetrify_map_of_flip {i j : Q} (a : j ⟶ i) (h : σ a) :
    (reorientSymmetrify σ).map (Symmetrify.of.map (reorientFlip σ a h)) =
      Quiver.reverse (Symmetrify.of.map a) :=
  (rfl)

/-- The formal reverse of a turned-around arrow is the arrow itself. Deliberately not a `simp`
lemma, for the reason recorded on `TauCeti.reorientSymmetrify_map_reverse_of_keep`. -/
theorem reorientSymmetrify_map_reverse_of_flip {i j : Q} (a : j ⟶ i) (h : σ a) :
    (reorientSymmetrify σ).map (Quiver.reverse (Symmetrify.of.map (reorientFlip σ a h))) =
      Symmetrify.of.map a :=
  (rfl)

/-- **The two comparisons are inverse**, starting from the reoriented quiver. -/
theorem reorientSymmetrify_comp_reorientSymmetrifyInv :
    (reorientSymmetrify σ).comp (reorientSymmetrifyInv σ) = Prefunctor.id _ := by
  refine Prefunctor.ext (fun _ => rfl) fun i j b => ?_
  obtain (⟨a, ha⟩ | ⟨a, ha⟩) | ⟨a, ha⟩ | ⟨a, ha⟩ := b <;>
    simp [reorientSymmetrify, reorientSymmetrifyInv, ha] <;> rfl

/-- **The two comparisons are inverse**, starting from the original quiver. -/
theorem reorientSymmetrifyInv_comp_reorientSymmetrify :
    (reorientSymmetrifyInv σ).comp (reorientSymmetrify σ) = Prefunctor.id _ := by
  refine Prefunctor.ext (fun _ => rfl) fun i j b => ?_
  obtain a | a := b <;> by_cases ha : σ a <;>
    simp [reorientSymmetrify, reorientSymmetrifyInv, ha] <;> rfl

/-- **The comparison of doubled quivers commutes with arrow reversal**, so it identifies the two
doubled quivers as quivers with an involutive reverse. -/
theorem reorientSymmetrify_map_reverse {i j : Symmetrify (Reorient Q σ)} (b : i ⟶ j) :
    (reorientSymmetrify σ).map (Quiver.reverse b) =
      Quiver.reverse ((reorientSymmetrify σ).map b) := by
  obtain (⟨a, ha⟩ | ⟨a, ha⟩) | ⟨a, ha⟩ | ⟨a, ha⟩ := b <;> rfl

end TauCeti
