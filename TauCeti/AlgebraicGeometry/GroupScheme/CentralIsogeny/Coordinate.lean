/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Coordinate criterion for central kernels

A morphism `f : H ⟶ K` of commutative Hopf algebras induces contravariantly a morphism
`Spec K ⟶ Spec H` of affine group schemes. This file identifies the two existing notions of a
central kernel for that morphism:

* `GroupScheme.HasCentralKernel` tests the kernel on points valued in every scheme over the base;
* `HopfIdeal.IsCentral` says that the represented kernel Hopf ideal is central.

The bridge must account for nonaffine test schemes in `HasCentralKernel`. It uses the relative
`Γ-Spec` multiplicative equivalence from `CommHopfAlgCat.SchemePoints`, so the group law on all
scheme-valued points is convolution on global sections. Naturality in `H` then identifies the
kernel of the scheme-valued point map with the points cut out by `kernelHopfIdeal f`.

## Main declarations

* `TauCeti.GroupScheme.hasCentralKernel_hopfSpec_map_iff`: the induced affine group-scheme morphism
  has central kernel exactly when its kernel Hopf ideal is central.
* `TauCeti.GroupScheme.isCentralIsogeny_hopfSpec_map_iff`: the resulting coordinate criterion
  for a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k, 2, and 18.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 2 and 10.

The relative global-sections comparison uses Mathlib's `algΓAlgSpecAdjunction` and
`AlgebraicGeometry.Spec.mapMulEquiv`. This synchronizes the Hopf-algebra and group-scheme
formulations of central isogenies required in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- If the represented kernel Hopf ideal is central, then the induced affine group-scheme
morphism has central kernel on points valued in every scheme over the base. -/
theorem hasCentralKernel_hopfSpec_map_of_isCentral_kernelHopfIdeal
    {H K : CommHopfAlgCat.{u} R} (f : H ⟶ K) (hf : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral) :
    HasCentralKernel ((hopfSpec (CommRingCat.of R)).map f.op) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center]
  intro T g hg
  -- The `hopfSpec` objects unfold to the relative spectrum presentations used by the comparison.
  let eK :
      (T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op K)).X) ≃*
        WithConv (K →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) :=
    CommHopfAlgCat.schemePointsAlgΓMulEquiv K T
  let eH :
      (T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) ≃*
        WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) :=
    CommHopfAlgCat.schemePointsAlgΓMulEquiv H T
  have hmap : AlgHom.mapDomain f.hom (eK g) = 1 := by
    calc
      AlgHom.mapDomain f.hom (eK g) =
          eH (pointMap ((hopfSpec (CommRingCat.of R)).map f.op) T g) := by
        dsimp only [eH, eK]
        rw [pointMap_apply]
        exact (CommHopfAlgCat.schemePointsAlgΓMulEquiv_mapDomain T f.hom g).symm
      _ = eH 1 := congrArg eH (MonoidHom.mem_ker.mp hg)
      _ = 1 := map_one eH
  rw [AlgHom.mapDomain_apply, ← CommHopfAlgCat.mapPointsFunctor_app_apply] at hmap
  have hmem : eK g ∈ CommHopfAlgCat.quotientPointsSubgroup K
      (CommHopfAlgCat.kernelHopfIdeal f) ((algΓ (CommRingCat.of R)).obj T).unop :=
    (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f _ (eK g)).mp hmap
  have hp := CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup
    K (CommHopfAlgCat.kernelHopfIdeal f) hf _ hmem
  rw [Subgroup.mem_center_iff]
  intro h
  exact (Commute.of_map eK.injective (hp.commute (eK h)).symm).eq

/-- If the induced affine group-scheme morphism has central kernel on all scheme-valued points,
then its represented kernel Hopf ideal is central. -/
theorem isCentral_kernelHopfIdeal_of_hasCentralKernel_hopfSpec_map
    {H K : CommHopfAlgCat.{u} R} (f : H ⟶ K)
    (hf : HasCentralKernel ((hopfSpec (CommRingCat.of R)).map f.op)) :
    (CommHopfAlgCat.kernelHopfIdeal f).IsCentral := by
  rw [CommHopfAlgCat.isCentral_iff_forall_isCentralPoint]
  intro A g hg
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ h
  let gB := AlgHom.mapValue φ g
  have hgB : gB ∈ CommHopfAlgCat.quotientPointsSubgroup K
      (CommHopfAlgCat.kernelHopfIdeal f) (CommAlgCat.of R B) :=
    CommHopfAlgCat.mapPoints_mem_quotientPointsSubgroup K
      (CommHopfAlgCat.kernelHopfIdeal f) (CommAlgCat.ofHom φ) hg
  have hmap : (CommHopfAlgCat.mapPointsFunctor f).app (CommAlgCat.of R B) gB = 1 :=
    (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f (CommAlgCat.of R B) gB).mpr hgB
  -- The `hopfSpec` objects unfold to the relative spectrum presentations used by `mapMulEquiv`.
  let eH : WithConv (H →ₐ[R] B) ≃*
      ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
        ((hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) :=
    AlgebraicGeometry.Spec.mapMulEquiv
  let eK : WithConv (K →ₐ[R] B) ≃*
      ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
        ((hopfSpec (CommRingCat.of R)).obj (Opposite.op K)).X) :=
    AlgebraicGeometry.Spec.mapMulEquiv
  have hnat : eK gB ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom =
      eH ((CommHopfAlgCat.mapPointsFunctor f).app (CommAlgCat.of R B) gB) := by
    dsimp only [eH, eK]
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    exact (CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of R B) f.hom gB).symm
  have hsg : eK gB ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom = 1 := by
    calc
      _ = eH ((CommHopfAlgCat.mapPointsFunctor f).app (CommAlgCat.of R B) gB) := hnat
      _ = eH 1 := congrArg eH hmap
      _ = 1 := map_one eH
  have hker : eK gB ∈
      (pointMap ((hopfSpec (CommRingCat.of R)).map f.op)
        ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))).ker := by
    apply MonoidHom.mem_ker.mpr
    exact (pointMap_apply _ _ _).trans hsg
  have hcenter := (hasCentralKernel_iff_pointMap_ker_le_center
    ((hopfSpec (CommRingCat.of R)).map f.op)).mp hf _ hker
  have hs := (Subgroup.mem_center_iff.mp hcenter) (eK h)
  exact Commute.of_map eK.injective (commute_iff_eq _ _ |>.mpr hs.symm)

/-- **Coordinate criterion for a central kernel.** The affine group-scheme morphism induced by
`f : H ⟶ K` has central kernel exactly when its represented kernel Hopf ideal is central. -/
theorem hasCentralKernel_hopfSpec_map_iff {H K : CommHopfAlgCat.{u} R} (f : H ⟶ K) :
    HasCentralKernel ((hopfSpec (CommRingCat.of R)).map f.op) ↔
      (CommHopfAlgCat.kernelHopfIdeal f).IsCentral :=
  ⟨isCentral_kernelHopfIdeal_of_hasCentralKernel_hopfSpec_map f,
    hasCentralKernel_hopfSpec_map_of_isCentral_kernelHopfIdeal f⟩

section Field

variable {k : Type u} [Field k] {H K : CommHopfAlgCat.{u} k}

/-- **Coordinate criterion for a central isogeny.** A Hopf-spectrum morphism is a central
isogeny exactly when it is an isogeny and its represented kernel Hopf ideal is central. -/
theorem isCentralIsogeny_hopfSpec_map_iff (f : H ⟶ K) :
    IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) ↔
      IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) ∧
        (CommHopfAlgCat.kernelHopfIdeal f).IsCentral := by
  rw [isCentralIsogeny_iff, isIsogeny_iff]
  simp only [and_assoc, hasCentralKernel_hopfSpec_map_iff]

end Field

end TauCeti.GroupScheme
