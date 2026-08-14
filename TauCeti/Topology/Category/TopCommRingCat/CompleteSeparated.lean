/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The category of complete separated topological commutative rings

Wedhorn's structure presheaves take values among *complete separated* topological rings
(*Adic Spaces*, arXiv:1910.05934v1, §8.1; roadmap Layer 3.2). This file defines the
predicate and the full subcategory of `TopCommRingCat` it cuts out.

A bare topological ring carries no uniformity, so completeness is stated for the canonical
group uniformity `IsTopologicalAddGroup.rightUniformSpace` of the additive topological
group. Nothing is lost against any other compatible choice:
`IsUniformAddGroup.rightUniformSpace_eq` says every uniformity making the ring a uniform
additive group with this topology *equals* the canonical one, and the introduction and
elimination lemmas below package that transfer so consumers never perform it by hand.
Separatedness is stated as `T0Space`, with `IsCompleteSeparated.t2Space` providing the
Hausdorff form the equalizer arguments consume.

## Main definitions

* `TauCeti.TopCommRingCat.IsCompleteSeparated`: complete and Hausdorff for the group
  uniformity of the topology.
* `TauCeti.TopCommRingCat.isCompleteSeparated`: the same, as a named `ObjectProperty`.
* `TauCeti.CompleteSeparatedTopCommRingCat`: the full subcategory of `TopCommRingCat` on
  the complete separated objects, with `CompleteSeparatedTopCommRingCat.of` and element
  coercion.

## Main results

* `TauCeti.TopCommRingCat.isCompleteSeparated_of_completeSpace_of_t0Space` and
  `TauCeti.TopCommRingCat.completeSpace_of_isCompleteSeparated` : the transfer in and out of
  the predicate for a ring carrying its own compatible uniformity. Applied at a completion
  it gives the canonical witnesses — the family the structure presheaf's values come from —
  as the `example` below records.
* `TauCeti.TopCommRingCat.IsCompleteSeparated.t2Space` : separatedness in Hausdorff form.
* `TauCeti.TopCommRingCat.IsCompleteSeparated.pi` : a product of complete separated objects
  is complete separated. This is the closure half for products; the limit cones and the
  creation statement for the inclusion `CompleteSeparatedTopCommRingCat ⥤ TopCommRingCat`
  (roadmap Layer 3.2) are the follow-up, not proved here.
-/

public section

universe v u

open CategoryTheory

namespace TauCeti.TopCommRingCat

/-- A topological commutative ring is **complete separated** when it is complete and
Hausdorff for the group uniformity `IsTopologicalAddGroup.rightUniformSpace` of its
topology. This is Wedhorn's standing convention that "complete" includes "Hausdorff"
(*Adic Spaces*, §5.3); separatedness is stated as `T0Space`, with
`IsCompleteSeparated.t2Space` supplying the Hausdorff form. -/
structure IsCompleteSeparated (R : TopCommRingCat.{u}) : Prop where
  /-- Completeness for the group uniformity of the topology. -/
  completeSpace :
    letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    CompleteSpace R
  /-- Separatedness; `T0Space` suffices. -/
  t0Space : T0Space R

/-- **Introduction from a native uniformity**: a complete Hausdorff uniform topological ring
is complete separated as a topological ring — the group uniformity of its topology equals
the given uniformity. This is how completions, `Valued` rings, and closed subrings enter the
subcategory. -/
theorem isCompleteSeparated_of_completeSpace_of_t0Space (R : Type u) [CommRing R] [UniformSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] :
    IsCompleteSeparated (TopCommRingCat.of R) where
  completeSpace := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  t0Space := ‹T0Space R›

-- The canonical witnesses: the completion of any uniform commutative topological ring is a
-- complete separated object — the family the structure presheaf's values come from. This is
-- recorded as an `example` rather than a named theorem because it is the introduction lemma
-- above at the completion instances, which callers can apply directly.
example (B : Type u) [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] :
    IsCompleteSeparated (TopCommRingCat.of (UniformSpace.Completion B)) :=
  isCompleteSeparated_of_completeSpace_of_t0Space _

/-- **Elimination to a native uniformity**, the dual of
`isCompleteSeparated_of_completeSpace_of_t0Space`: a uniform topological ring whose
associated object is complete separated is complete for its own uniformity. -/
theorem completeSpace_of_isCompleteSeparated {R : Type u} [CommRing R] [UniformSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R]
    (h : IsCompleteSeparated (TopCommRingCat.of R)) : CompleteSpace R := by
  rw [← IsUniformAddGroup.rightUniformSpace_eq (G := R)]
  exact h.completeSpace

/-- Separatedness of a complete separated object, in Hausdorff form: for a topological
additive group, `T0Space` upgrades to `T2Space`. -/
theorem IsCompleteSeparated.t2Space {R : TopCommRingCat.{u}} (h : IsCompleteSeparated R) :
    T2Space R := by
  have := h.t0Space
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  infer_instance

/-- **A product of complete separated topological rings is complete separated**: the product
carries the product uniformity, for which it is complete and Hausdorff. -/
theorem IsCompleteSeparated.pi {β : Type v} {f : β → TopCommRingCat.{max u v}}
    (hf : ∀ b, IsCompleteSeparated (f b)) :
    IsCompleteSeparated (TopCommRingCat.of (∀ b, f b)) := by
  let _ : ∀ b, UniformSpace (f b) := fun b ↦ IsTopologicalAddGroup.rightUniformSpace _
  have huag : ∀ b, IsUniformAddGroup (f b) := fun b ↦ isUniformAddGroup_of_addCommGroup
  have hcompl : ∀ b, CompleteSpace (f b) := fun b ↦ (hf b).completeSpace
  have ht0 : ∀ b, T0Space (f b) := fun b ↦ (hf b).t0Space
  refine ⟨?_, inferInstance⟩
  let _ : UniformSpace (∀ b, f b) := Pi.uniformSpace _
  -- The group uniformity of the product topology is the product of the group uniformities:
  -- `IsUniformAddGroup.rightUniformSpace_eq` identifies it with `Pi.uniformSpace`.
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- The complete separated objects, as a named `ObjectProperty` — the form the subcategory
and its instance machinery key on. Consumers go through `isCompleteSeparated_iff` and the
object instances rather than the definition. -/
def isCompleteSeparated : ObjectProperty TopCommRingCat.{u} :=
  fun R ↦ IsCompleteSeparated R

/-- Membership in the object property is the predicate. -/
@[simp]
theorem isCompleteSeparated_iff (R : TopCommRingCat.{u}) :
    isCompleteSeparated R ↔ IsCompleteSeparated R := (Iff.rfl)

end TauCeti.TopCommRingCat

namespace TauCeti

/-- The category of complete separated topological commutative rings: the full subcategory
of `TopCommRingCat` on the objects that are complete and Hausdorff for the group uniformity
of their topology. This is the codomain of the adic structure presheaf. -/
noncomputable abbrev CompleteSeparatedTopCommRingCat : Type (u + 1) :=
  TopCommRingCat.isCompleteSeparated.{u}.FullSubcategory

namespace CompleteSeparatedTopCommRingCat

instance : CoeSort CompleteSeparatedTopCommRingCat.{u} (Type u) :=
  ⟨fun X ↦ X.obj⟩

/-- Build an object of `CompleteSeparatedTopCommRingCat` from a complete Hausdorff uniform
topological ring. -/
noncomputable def of (R : Type u) [CommRing R] [UniformSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] :
    CompleteSeparatedTopCommRingCat.{u} :=
  ⟨TopCommRingCat.of R, TopCommRingCat.isCompleteSeparated_of_completeSpace_of_t0Space R⟩

@[simp]
theorem of_obj (R : Type u) [CommRing R] [UniformSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] :
    (of R).obj = TopCommRingCat.of R := (rfl)

instance (X : CompleteSeparatedTopCommRingCat.{u}) : T2Space X.obj :=
  ((TopCommRingCat.isCompleteSeparated_iff _).mp X.property).t2Space

/-- Objects carry the group uniformity of their topology, so that the defining completeness
is available by inference. -/
noncomputable instance (X : CompleteSeparatedTopCommRingCat.{u}) : UniformSpace X.obj :=
  IsTopologicalAddGroup.rightUniformSpace X.obj

instance (X : CompleteSeparatedTopCommRingCat.{u}) : IsUniformAddGroup X.obj :=
  isUniformAddGroup_of_addCommGroup

instance (X : CompleteSeparatedTopCommRingCat.{u}) : CompleteSpace X.obj :=
  ((TopCommRingCat.isCompleteSeparated_iff _).mp X.property).completeSpace

end CompleteSeparatedTopCommRingCat

end TauCeti
