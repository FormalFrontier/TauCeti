/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Central isogenies and isomorphisms

An isogeny with monic underlying scheme morphism is an isomorphism. Central isogenies are also
unchanged by replacing their source or target by an isomorphic group scheme. This file proves the
corresponding `MorphismProperty.RespectsIso` instance and records the underlying fact that the
all-test-schemes central-kernel condition is invariant under pre- and postcomposition with an
isomorphism.

The proofs stay at the functor-of-points level used by `GroupScheme.HasCentralKernel`. A morphism
monic in `Over X` induces an injective map on points over every test scheme. On the source this
reflects commutativity, while on the target it shows that postcomposition does not change the
pointwise kernel.

## Main declarations

* `TauCeti.GroupScheme.HasCentralKernel.precomp_of_mono`: central kernels are preserved by
  precomposition with a morphism monic in `Over X`.
* `TauCeti.GroupScheme.HasCentralKernel.postcomp_of_mono`: central kernels are preserved by
  postcomposition with a morphism monic in `Over X`.
* `TauCeti.GroupScheme.hasCentralKernel_comp_iff_of_mono`: postcomposition by a morphism monic in
  `Over X` preserves and reflects central kernels.
* `TauCeti.GroupScheme.hasCentralKernel_respectsIso`: having central kernel respects isomorphisms
  of arrows.
* `TauCeti.GroupScheme.IsIsogeny.isIso_of_mono`: an isogeny whose underlying scheme morphism is
  monic is an isomorphism.
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

/-- Precomposing with a morphism monic in `Over X` preserves the central-kernel condition. -/
theorem HasCentralKernel.precomp_of_mono (e : F ⟶ G) [Mono e.hom.hom] (f : G ⟶ H)
    (hf : HasCentralKernel f) : HasCentralKernel (e ≫ f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  have hg' : pointMap f T (pointMap e T g) = 1 := by
    rw [← MonoidHom.comp_apply, ← pointMap_comp]
    exact MonoidHom.mem_ker.mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply pointMap_injective_of_mono e T
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp (hf T <| MonoidHom.mem_ker.mpr hg')
    (pointMap e T h))

/-- Postcomposing with a morphism monic in `Over X` preserves the central-kernel condition. -/
theorem HasCentralKernel.postcomp_of_mono (f : G ⟶ H) (e : H ⟶ K) [Mono e.hom.hom]
    (hf : HasCentralKernel f) : HasCentralKernel (f ≫ e) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  apply hf T
  rw [MonoidHom.mem_ker]
  apply pointMap_injective_of_mono e T
  rw [map_one, ← MonoidHom.comp_apply, ← pointMap_comp]
  exact MonoidHom.mem_ker.mp hg

/-- Postcomposition by a morphism monic in `Over X` preserves and reflects the central-kernel
condition. -/
theorem hasCentralKernel_comp_iff_of_mono (f : G ⟶ H) (e : H ⟶ K) [Mono e.hom.hom] :
    HasCentralKernel (f ≫ e) ↔ HasCentralKernel f := by
  constructor
  · intro hfe
    rw [hasCentralKernel_iff_pointMap_ker_le_center] at hfe ⊢
    intro T g hg
    apply hfe T
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [pointMap_comp, MonoidHom.comp_apply, hg, map_one]
  · exact fun hf ↦ hf.postcomp_of_mono f e

/-- Having central kernel is invariant under isomorphisms of arrows. -/
instance hasCentralKernel_respectsIso : (hasCentralKernel X).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro _ _ _ e f hf
    exact HasCentralKernel.precomp_of_mono e.hom f hf
  · intro _ _ _ e f hf
    exact HasCentralKernel.postcomp_of_mono f e.hom hf

section Isogeny

variable {k : Type u} [CommRing k]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

namespace IsIsogeny

/-- A group-scheme isogeny whose underlying scheme morphism is monic is an isomorphism. -/
theorem isIso_of_mono {f : G ⟶ H} (hf : IsIsogeny f) [Mono f.hom.hom.left] : IsIso f := by
  let _ : IsFinite f.hom.hom.left := hf.isFinite
  let _ : Flat f.hom.hom.left := hf.flat
  let _ : Surjective f.hom.hom.left := hf.surjective
  apply (isIso_iff_of_reflects_iso f
    (Grp.forget₂Mon (Over (Spec (CommRingCat.of k))))).mp
  apply (isIso_iff_of_reflects_iso f.hom
    (Mon.forget (Over (Spec (CommRingCat.of k))))).mp
  apply (isIso_iff_of_reflects_iso f.hom.hom
    (Over.forget (Spec (CommRingCat.of k)))).mp
  exact Flat.isIso_of_surjective_of_mono f.hom.hom.left

end IsIsogeny

/-- Central isogenies are invariant under pre- and postcomposition with isomorphisms. -/
instance centralIsogenies_respectsIso : (centralIsogenies k).RespectsIso := by
  rw [centralIsogenies_eq]
  exact MorphismProperty.RespectsIso.inf (isogenies k)
    (hasCentralKernel (Spec (CommRingCat.of k)))

end Isogeny

end TauCeti.GroupScheme
