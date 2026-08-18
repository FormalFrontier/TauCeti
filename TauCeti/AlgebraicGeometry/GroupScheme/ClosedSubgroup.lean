/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Closed subgroup schemes

This file defines closed subgroup schemes of a group scheme over an arbitrary base scheme. A
closed subgroup scheme is a categorical subobject whose representative arrow is a closed
immersion on underlying schemes. Pulling the closed-immersion property back through the two
forgetful functors makes the condition independent of the chosen representative.

Neither the base nor the group scheme is required to be affine. Affineness enters only in
specialized constructions that import this generic API.

## Main declarations

* `TauCeti.closedSubgroupMorphismProperty`: the closed-immersion property for morphisms of group
  schemes.
* `TauCeti.ClosedSubgroupScheme`: closed subgroup subobjects of a group scheme.
* `TauCeti.ClosedSubgroupScheme.mk`: the closed subgroup represented by a closed immersion.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

open AlgebraicGeometry

/-- The property of a morphism of group schemes that its underlying scheme morphism is a closed
immersion. Pulling the property back along the two forgetful functors makes its invariance under
isomorphisms available from the generic morphism-property API. -/
def closedSubgroupMorphismProperty (X : Scheme.{u}) :
    MorphismProperty (Grp (Over X)) :=
  MorphismProperty.inverseImage (@IsClosedImmersion) (Grp.forget _ ⋙ Over.forget _)

/-- The underlying closed-immersion property is invariant under isomorphisms of group schemes. -/
instance closedSubgroupMorphismProperty_respectsIso (X : Scheme.{u}) :
    (closedSubgroupMorphismProperty X).RespectsIso := by
  unfold closedSubgroupMorphismProperty
  let _ : MorphismProperty.RespectsIso (@IsClosedImmersion) :=
    AlgebraicGeometry.IsClosedImmersion.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage (@IsClosedImmersion)
    (Grp.forget _ ⋙ Over.forget _)

/-- A group-scheme morphism whose underlying scheme morphism is a closed immersion is a
monomorphism. -/
instance (priority := 900) mono_of_isClosedImmersion_underlying {X : Scheme.{u}}
    {G K : Grp (Over X)} (f : G ⟶ K) [IsClosedImmersion f.hom.hom.left] : Mono f := by
  apply (Grp.forget _ ⋙ Over.forget _).mono_of_mono_map
  -- The composite forgetful functor maps `f` to `f.hom.hom.left`; its source and target are
  -- definitionally the underlying schemes, so the dependent `Mono` proposition needs this
  -- conversion after reflecting monomorphisms.
  change Mono f.hom.hom.left
  infer_instance

/-- A monomorphism of underlying schemes is injective on points over every scheme above the base.

The map on points is postcomposition with the group-scheme morphism. Its injectivity is the
functor-of-points form of the defining cancellation property of a monomorphism. -/
theorem pointsMap_injective_of_mono {X : Scheme.{u}}
    {G K : Grp (Over X)} (f : G ⟶ K) [Mono f.hom.hom.left]
    (T : Over X) : Function.Injective (IsMonHom.monoidHom f.hom.hom T) := by
  intro p q hpq
  apply Over.OverMorphism.ext
  apply (cancel_mono f.hom.hom.left).1
  simpa only [IsMonHom.monoidHom_apply, Over.comp_left] using
    congrArg Over.Hom.left hpq

/-- A morphism has `closedSubgroupMorphismProperty` exactly when its underlying scheme morphism is
a closed immersion. -/
@[simp]
lemma closedSubgroupMorphismProperty_iff (X : Scheme.{u})
    {G K : Grp (Over X)} (f : G ⟶ K) :
    closedSubgroupMorphismProperty X f ↔ IsClosedImmersion f.hom.hom.left := by
  unfold closedSubgroupMorphismProperty MorphismProperty.inverseImage
  rfl

/-- A closed subgroup scheme of `G` is a categorical subobject represented by a closed immersion
on underlying schemes. The use of `Subobject` identifies presentations isomorphic over `G`. -/
abbrev ClosedSubgroupScheme {X : Scheme.{u}} (G : Grp (Over X)) : Type _ :=
  {P : Subobject G // closedSubgroupMorphismProperty X P.arrow}

namespace ClosedSubgroupScheme

variable {X : Scheme.{u}} {G : Grp (Over X)}

/-- Construct a closed subgroup scheme from a morphism whose underlying scheme morphism is a
closed immersion. -/
noncomputable def mk {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] : ClosedSubgroupScheme G :=
  ⟨Subobject.mk i, by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk i,
      (closedSubgroupMorphismProperty X).cancel_left_of_respectsIso]
    exact (closedSubgroupMorphismProperty_iff X i).2 inferInstance⟩

/-- The subobject underlying a closed subgroup scheme constructed from an explicit arrow is the
subobject represented by that arrow. -/
@[simp]
lemma coe_mk {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] :
    (mk i).1 = Subobject.mk i :=
  by
    unfold mk
    rfl

end ClosedSubgroupScheme

end TauCeti
