/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Central isogenies and isomorphisms

Central isogenies are unchanged by replacing their source or target by an isomorphic group
scheme. This file proves the corresponding `MorphismProperty.RespectsIso` instance. It also
records the underlying fact that the all-test-schemes central-kernel condition is invariant under
pre- and postcomposition with an isomorphism.

The proofs stay at the functor-of-points level used by `GroupScheme.HasCentralKernel`. An
isomorphism of group schemes induces an injective map on points over every test scheme. On the
source this reflects commutativity, while on the target it shows that postcomposition does not
change the pointwise kernel.

## Main declarations

* `TauCeti.GroupScheme.pointMap_injective_of_isIso`: an isomorphism induces an injective map on
  points over every test scheme.
* `TauCeti.GroupScheme.hasCentralKernel_iso_hom_comp_iff`: central kernels are invariant under a
  source isomorphism.
* `TauCeti.GroupScheme.hasCentralKernel_comp_iso_hom_iff`: central kernels are invariant under a
  target isomorphism.
* `TauCeti.GroupScheme.centralIsogenies_respectsIso`: central isogenies respect isomorphisms of
  arrows.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

This supplies the isomorphism-invariance needed by the central-isogeny, simply-connected and
adjoint-form targets in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {F G H K : Grp (Over X)}

/-- An isomorphism of group schemes induces an injective map on points over every test scheme. -/
theorem pointMap_injective_of_isIso (e : G ⟶ H) [IsIso e] (T : Over X) :
    Function.Injective (pointMap e T) := by
  intro g h hgh
  have h := congrArg (pointMap (inv e) T) hgh
  simpa only [← MonoidHom.comp_apply, ← pointMap_comp, IsIso.hom_inv_id, pointMap_id,
    MonoidHom.id_apply] using h

/-- Precomposing with an isomorphism preserves the central-kernel condition. -/
theorem HasCentralKernel.precomp_isIso (e : F ⟶ G) [IsIso e] (f : G ⟶ H)
    (hf : HasCentralKernel f) : HasCentralKernel (e ≫ f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  have hg' : pointMap f T (pointMap e T g) = 1 := by
    rw [← MonoidHom.comp_apply, ← pointMap_comp]
    exact MonoidHom.mem_ker.mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply (pointMap_injective_of_isIso e T)
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp (hf T <| MonoidHom.mem_ker.mpr hg')
    (pointMap e T h))

/-- Postcomposing with an isomorphism preserves the central-kernel condition. -/
theorem HasCentralKernel.postcomp_isIso (f : G ⟶ H) (e : H ⟶ K) [IsIso e]
    (hf : HasCentralKernel f) : HasCentralKernel (f ≫ e) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  apply hf T
  rw [MonoidHom.mem_ker]
  apply pointMap_injective_of_isIso e T
  rw [map_one, ← MonoidHom.comp_apply, ← pointMap_comp]
  exact MonoidHom.mem_ker.mp hg

/-- The central-kernel condition is invariant under a source isomorphism. -/
theorem hasCentralKernel_iso_hom_comp_iff (e : F ≅ G) (f : G ⟶ H) :
    HasCentralKernel (e.hom ≫ f) ↔ HasCentralKernel f := by
  constructor
  · intro h
    have := h.precomp_isIso e.inv (e.hom ≫ f)
    simpa using this
  · exact HasCentralKernel.precomp_isIso e.hom f

/-- The central-kernel condition is invariant under a target isomorphism. -/
theorem hasCentralKernel_comp_iso_hom_iff (f : G ⟶ H) (e : H ≅ K) :
    HasCentralKernel (f ≫ e.hom) ↔ HasCentralKernel f := by
  constructor
  · intro h
    have := h.postcomp_isIso (f ≫ e.hom) e.inv
    simpa using this
  · exact HasCentralKernel.postcomp_isIso f e.hom

section Isogeny

variable {k : Type u} [Field k]
variable {F G H K : Grp (Over (Spec (CommRingCat.of k)))}

/-- Central isogenies are invariant under pre- and postcomposition with isomorphisms. -/
instance centralIsogenies_respectsIso : (centralIsogenies k).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    let hi : IsIsogeny (e.hom ≫ f) :=
      MorphismProperty.RespectsIso.precomp (isogenies k) e.hom f hf.isIsogeny
    apply (isCentralIsogeny_iff (e.hom ≫ f)).mpr
    exact ⟨hi.isFinite, hi.flat, hi.surjective,
      hf.hasCentralKernel.precomp_isIso e.hom f⟩
  · intro X Y Z e f hf
    let hi : IsIsogeny (f ≫ e.hom) :=
      MorphismProperty.RespectsIso.postcomp (isogenies k) e.hom f hf.isIsogeny
    apply (isCentralIsogeny_iff (f ≫ e.hom)).mpr
    exact ⟨hi.isFinite, hi.flat, hi.surjective,
      hf.hasCentralKernel.postcomp_isIso f e.hom⟩

/-- Precomposing a central isogeny with an isomorphism gives a central isogeny. -/
theorem IsCentralIsogeny.precomp_isIso (e : F ⟶ G) [IsIso e] (f : G ⟶ H)
    (hf : IsCentralIsogeny f) : IsCentralIsogeny (e ≫ f) :=
  MorphismProperty.RespectsIso.precomp (centralIsogenies k) e f hf

/-- Postcomposing a central isogeny with an isomorphism gives a central isogeny. -/
theorem IsCentralIsogeny.postcomp_isIso (f : G ⟶ H) (e : H ⟶ K) [IsIso e]
    (hf : IsCentralIsogeny f) : IsCentralIsogeny (f ≫ e) :=
  MorphismProperty.RespectsIso.postcomp (centralIsogenies k) e f hf

/-- Central isogeny is invariant under a source isomorphism. -/
theorem isCentralIsogeny_iso_hom_comp_iff (e : F ≅ G) (f : G ⟶ H) :
    IsCentralIsogeny (e.hom ≫ f) ↔ IsCentralIsogeny f :=
  (centralIsogenies k).cancel_left_of_respectsIso e.hom f

/-- Central isogeny is invariant under a target isomorphism. -/
theorem isCentralIsogeny_comp_iso_hom_iff (f : G ⟶ H) (e : H ≅ K) :
    IsCentralIsogeny (f ≫ e.hom) ↔ IsCentralIsogeny f :=
  (centralIsogenies k).cancel_right_of_respectsIso f e.hom

end Isogeny

end TauCeti.GroupScheme
