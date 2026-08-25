/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.SingleObj

/-!
# A connected groupoid is equivalent to its vertex group

Let `C` be a groupoid and `x₀ : C` a *weakly initial* object, that is, one which admits a morphism
to every object. This file proves that the one-object category `SingleObj (End x₀)` of the vertex
group at `x₀` is equivalent to `C`, through the functor sending the unique object to `x₀` and an
endomorphism to itself.

Both halves are immediate once the functor is written down. It is fully faithful in any category,
because its action on the single hom-set is the identity of `End x₀`, and it is essentially
surjective because in a groupoid a morphism `x₀ ⟶ x` is already an isomorphism. What the
equivalence buys is a dictionary: functors out of `C` become functors out of `SingleObj (End x₀)`,
that is, objects with an action of the vertex group, and the dictionary is natural in the target
category; `TauCeti.Groupoid.natIsoOfEnd` in `TauCeti.CategoryTheory.Groupoid.ConnectedFunctor` is
that dictionary applied to isomorphisms.

The weak initiality hypothesis is stated as the family of nonemptiness assertions
`∀ x, Nonempty (x₀ ⟶ x)` rather than through `CategoryTheory.IsConnected`: the intended source of
that data is a path-connected topological space, whose fundamental groupoid comes with paths out
of a chosen basepoint.

## Main declarations

* `TauCeti.Groupoid.singleObjFunctor`: the functor `SingleObj (End x₀) ⥤ C` picking out `x₀`.
* `TauCeti.Groupoid.fullyFaithfulSingleObjFunctor`: it is fully faithful, without hypotheses.
* `TauCeti.Groupoid.essSurj_singleObjFunctor` and
  `TauCeti.Groupoid.isEquivalence_singleObjFunctor`: it is essentially surjective, hence an
  equivalence, when `x₀` admits a morphism to every object.
* `TauCeti.Groupoid.singleObjEquivalence`: **a connected groupoid is equivalent to the
  one-object category of its vertex group.**
-/

public section

universe v u

open CategoryTheory

namespace TauCeti.Groupoid

section Category

variable {C : Type u} [Category.{v} C] (x₀ : C)

/-- The functor from the one-object category of the vertex group at `x₀` that sends the unique
object to `x₀` and an endomorphism to itself.

It is `@[expose]`d so that the object and morphism equations hold by `rfl` downstream. -/
@[expose] def singleObjFunctor : SingleObj (End x₀) ⥤ C :=
  SingleObj.functor (MonoidHom.id (End x₀))

@[simp]
theorem singleObjFunctor_obj (a : SingleObj (End x₀)) : (singleObjFunctor x₀).obj a = x₀ :=
  (rfl)

@[simp]
theorem singleObjFunctor_map (g : End x₀) :
    (singleObjFunctor x₀).map (X := SingleObj.star (End x₀)) (Y := SingleObj.star (End x₀)) g =
      g :=
  (rfl)

/-- The functor out of the one-object category of the vertex group is fully faithful: on the
single hom-set it is the identity of `End x₀`. -/
def fullyFaithfulSingleObjFunctor : (singleObjFunctor x₀).FullyFaithful where
  preimage f := f

instance singleObjFunctor_full : (singleObjFunctor x₀).Full :=
  (fullyFaithfulSingleObjFunctor x₀).full

instance singleObjFunctor_faithful : (singleObjFunctor x₀).Faithful :=
  (fullyFaithfulSingleObjFunctor x₀).faithful

end Category

section Groupoid

variable {C : Type u} [CategoryTheory.Groupoid.{v} C] (x₀ : C)

/-- If `x₀` admits a morphism to every object of the groupoid, then every object is isomorphic to
`x₀`, so the functor out of the one-object category is essentially surjective. -/
theorem essSurj_singleObjFunctor (hconn : ∀ x : C, Nonempty (x₀ ⟶ x)) :
    (singleObjFunctor x₀).EssSurj where
  mem_essImage x :=
    ⟨SingleObj.star (End x₀),
      ⟨(CategoryTheory.Groupoid.isoEquivHom x₀ x).symm (hconn x).some⟩⟩

/-- If `x₀` admits a morphism to every object of the groupoid, the functor out of the one-object
category of the vertex group is an equivalence. -/
theorem isEquivalence_singleObjFunctor (hconn : ∀ x : C, Nonempty (x₀ ⟶ x)) :
    (singleObjFunctor x₀).IsEquivalence :=
  haveI := essSurj_singleObjFunctor x₀ hconn
  { }

/-- **A connected groupoid is equivalent to the one-object category of its vertex group.**

The equivalence is induced by `TauCeti.Groupoid.singleObjFunctor`, so it sends the unique object
to `x₀` and an endomorphism to itself. -/
noncomputable def singleObjEquivalence (hconn : ∀ x : C, Nonempty (x₀ ⟶ x)) :
    SingleObj (End x₀) ≌ C :=
  haveI := isEquivalence_singleObjFunctor x₀ hconn
  (singleObjFunctor x₀).asEquivalence

@[simp]
theorem singleObjEquivalence_functor (hconn : ∀ x : C, Nonempty (x₀ ⟶ x)) :
    (singleObjEquivalence x₀ hconn).functor = singleObjFunctor x₀ :=
  (rfl)

end Groupoid

end TauCeti.Groupoid
