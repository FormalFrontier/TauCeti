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

The proofs stay at the functor-of-points level used by `GroupScheme.HasCentralKernel`. A morphism
whose underlying scheme morphism is monic induces an injective map on points over every test
scheme. On the source this reflects commutativity, while on the target it shows that
postcomposition does not change the pointwise kernel.

## Main declarations

* `TauCeti.GroupScheme.pointMap_injective_of_mono`: a morphism with monic underlying scheme
  morphism induces an injective map on points over every test scheme.
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

/-- A group-scheme morphism with monic underlying scheme morphism induces an injective map on
points over every test scheme. -/
theorem pointMap_injective_of_mono (e : G ⟶ H) [Mono e.hom.hom] (T : Over X) :
    Function.Injective (pointMap e T) := by
  intro g h hgh
  apply (cancel_mono e.hom.hom).1
  simpa only [pointMap_apply] using hgh

/-- Precomposing with a morphism whose underlying scheme morphism is monic preserves the
central-kernel condition. -/
theorem HasCentralKernel.precomp_mono (e : F ⟶ G) [Mono e.hom.hom] (f : G ⟶ H)
    (hf : HasCentralKernel f) : HasCentralKernel (e ≫ f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  have hg' : pointMap f T (pointMap e T g) = 1 := by
    rw [← MonoidHom.comp_apply, ← pointMap_comp]
    exact MonoidHom.mem_ker.mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply (pointMap_injective_of_mono e T)
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp (hf T <| MonoidHom.mem_ker.mpr hg')
    (pointMap e T h))

/-- Postcomposing with a morphism whose underlying scheme morphism is monic preserves the
central-kernel condition. -/
theorem HasCentralKernel.postcomp_mono (f : G ⟶ H) (e : H ⟶ K) [Mono e.hom.hom]
    (hf : HasCentralKernel f) : HasCentralKernel (f ≫ e) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  apply hf T
  rw [MonoidHom.mem_ker]
  apply pointMap_injective_of_mono e T
  rw [map_one, ← MonoidHom.comp_apply, ← pointMap_comp]
  exact MonoidHom.mem_ker.mp hg

/-- Having central kernel is invariant under isomorphisms of arrows. -/
instance centralKernels_respectsIso : (centralKernels X).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro _ _ _ e f hf
    exact hf.precomp_mono e.hom f
  · intro _ _ _ e f hf
    exact hf.postcomp_mono f e.hom

/-- The central-kernel condition is invariant under a source isomorphism. -/
theorem hasCentralKernel_iso_hom_comp_iff (e : F ≅ G) (f : G ⟶ H) :
    HasCentralKernel (e.hom ≫ f) ↔ HasCentralKernel f :=
  (centralKernels X).cancel_left_of_respectsIso e.hom f

/-- The central-kernel condition is invariant under a target isomorphism. -/
theorem hasCentralKernel_comp_iso_hom_iff (f : G ⟶ H) (e : H ≅ K) :
    HasCentralKernel (f ≫ e.hom) ↔ HasCentralKernel f :=
  (centralKernels X).cancel_right_of_respectsIso f e.hom

section Isogeny

variable {k : Type u} [Field k]
variable {F G H K : Grp (Over (Spec (CommRingCat.of k)))}

/-- Central isogenies are invariant under pre- and postcomposition with isomorphisms. -/
instance centralIsogenies_respectsIso : (centralIsogenies k).RespectsIso := by
  unfold centralIsogenies
  infer_instance

end Isogeny

end TauCeti.GroupScheme
