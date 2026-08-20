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

The bridge must account for nonaffine test schemes in `HasCentralKernel`. For an arbitrary test
scheme `T`, the relative `Γ-Spec` adjunction identifies its maps to `Spec H` with algebra maps
from `H` to the relative global sections of `T`. The first main construction upgrades that
adjunction equivalence to a multiplicative equivalence, so the group law on all scheme-valued
points is convolution on global sections. Naturality in `H` then identifies the kernel of the
scheme-valued point map with the points cut out by `kernelHopfIdeal f`.

## Main declarations

* `TauCeti.GroupScheme.schemePointsAlgΓMulEquiv`: maps from an arbitrary relative scheme to an
  affine Hopf spectrum are convolution points valued in its relative global sections.
* `TauCeti.GroupScheme.schemePointsAlgΓMulEquiv_mapDomain`: this comparison is contravariantly
  natural in the coordinate Hopf algebra.
* `TauCeti.GroupScheme.hasCentralKernel_hopfSpec_map_iff`: the induced affine group-scheme morphism
  has central kernel exactly when its kernel Hopf ideal is central.
* `TauCeti.GroupScheme.isCentralIsogeny_hopfSpec_map_iff`: the resulting coordinate criterion
  for a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k, 2, and 18.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 2 and 10.

The relative global-sections comparison uses Mathlib's `algΓAlgSpecAdjunction`; on affine test
schemes it specializes to Mathlib's `AlgebraicGeometry.Spec.mapMulEquiv`. This synchronizes the
Hopf-algebra and group-scheme formulations of central isogenies required in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- The relative `Γ-Spec` adjunction as an equivalence between scheme-valued points and
convolution points, before recording multiplicativity. -/
private noncomputable def schemePointsAlgΓEquiv
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) ≃
      WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) := by
  let e₀ := (algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T
    (Opposite.op (CommAlgCat.of R H))
  exact e₀.symm.trans
    { toFun := fun f ↦ toConv f.unop.hom
      invFun := fun f ↦ (CommAlgCat.ofHom f.ofConv).op
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }

/-- The adjunction unit, with its target presented as the relative spectrum of global sections. -/
private noncomputable def algΓUnitToSpec (T : Over (Spec (CommRingCat.of R))) :
    T ⟶ (Spec (CommRingCat.of ((algΓ (CommRingCat.of R)).obj T).unop)).asOver
      (Spec (CommRingCat.of R)) :=
  (algΓAlgSpecAdjunction (CommRingCat.of R)).unit.app T ≫ eqToHom (by rfl)

/-- A convolution point over the global sections of `T`, regarded as a `T`-valued point through
the relative spectrum presentation. -/
private noncomputable def algΓPointSchemePoint
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X :=
  algΓUnitToSpec T ≫
    CommHopfAlgCat.mapMulEquivOfPresentation H _ rfl p

private theorem algΓPointSchemePoint_eq_symm
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    algΓPointSchemePoint H T p = (schemePointsAlgΓEquiv H T).symm p := by
  rw [show (schemePointsAlgΓEquiv H T).symm p =
      (algΓAlgSpecAdjunction (CommRingCat.of R)).unit.app T ≫
        (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom p.ofConv).op by rfl]
  unfold algΓPointSchemePoint algΓUnitToSpec
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Category.assoc]
  rw [CommHopfAlgCat.mapMulEquivOfPresentation_apply_left H _ rfl rfl]
  rfl

private theorem algΓPointSchemePoint_mul
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R)))
    (p q : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    algΓPointSchemePoint H T (p * q) =
      algΓPointSchemePoint H T p * algΓPointSchemePoint H T q := by
  unfold algΓPointSchemePoint
  rw [map_mul, MonObj.comp_mul]

/-- Maps from an arbitrary scheme `T` over `Spec R` to the affine group scheme represented by
`H` are the convolution group of `H`-points valued in the relative global sections of `T`.

Unlike `AlgebraicGeometry.Spec.mapMulEquiv`, the test scheme here need not be affine. The
equivalence is the relative `Γ-Spec` adjunction, with its target given the convolution group law.
-/
noncomputable def schemePointsAlgΓMulEquiv
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) ≃*
      WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop) :=
  { schemePointsAlgΓEquiv H T with
    map_mul' := by
      intro g h
      apply (schemePointsAlgΓEquiv H T).symm.injective
      calc
        _ = g * h := (schemePointsAlgΓEquiv H T).symm_apply_apply (g * h)
        _ = algΓPointSchemePoint H T (schemePointsAlgΓEquiv H T g) *
            algΓPointSchemePoint H T (schemePointsAlgΓEquiv H T h) := by
          rw [algΓPointSchemePoint_eq_symm, algΓPointSchemePoint_eq_symm,
            Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        _ = algΓPointSchemePoint H T
            (schemePointsAlgΓEquiv H T g * schemePointsAlgΓEquiv H T h) :=
          (algΓPointSchemePoint_mul H T _ _).symm
        _ = (schemePointsAlgΓEquiv H T).symm
            (schemePointsAlgΓEquiv H T g * schemePointsAlgΓEquiv H T h) :=
          algΓPointSchemePoint_eq_symm H T _ }

private theorem schemePointsAlgΓMulEquiv_symm_apply
    (H : CommHopfAlgCat.{u} R) (T : Over (Spec (CommRingCat.of R)))
    (p : WithConv (H →ₐ[R] ((algΓ (CommRingCat.of R)).obj T).unop)) :
    (schemePointsAlgΓMulEquiv H T).symm p = algΓPointSchemePoint H T p :=
  (algΓPointSchemePoint_eq_symm H T p).symm

/-- The global-sections comparison is contravariantly natural in the coordinate Hopf algebra.
Postcomposing a scheme-valued point with `Spec f` is precomposition of its algebra point by `f`.
-/
theorem schemePointsAlgΓMulEquiv_mapDomain
    {H K : CommHopfAlgCat.{u} R} (T : Over (Spec (CommRingCat.of R))) (f : H ⟶ K)
    (g : T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op K)).X) :
    schemePointsAlgΓMulEquiv H T
        (g ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom) =
      AlgHom.mapDomain f.hom (schemePointsAlgΓMulEquiv K T g) := by
  let A : CommAlgCat R := ((algΓ (CommRingCat.of R)).obj T).unop
  let eH := schemePointsAlgΓMulEquiv H T
  let eK := schemePointsAlgΓMulEquiv K T
  apply eH.symm.injective
  calc
    eH.symm (eH (g ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom)) =
        g ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom := eH.symm_apply_apply _
    _ = eH.symm (AlgHom.mapDomain f.hom (eK g)) := by
      rw [← eK.symm_apply_apply g]
      rw [eK.apply_symm_apply]
      rw [schemePointsAlgΓMulEquiv_symm_apply, schemePointsAlgΓMulEquiv_symm_apply]
      unfold algΓPointSchemePoint
      rw [Category.assoc]
      congr 1
      simpa only [A, eqToHom_refl, Category.comp_id, Category.id_comp,
        CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply] using
        (CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain (R := R) A
          (hG := rfl) (hH' := rfl)
          (CommHopfAlgCat.mapMulEquivOfPresentation H A rfl)
          (CommHopfAlgCat.mapMulEquivOfPresentation K A rfl)
          (fun p ↦ CommHopfAlgCat.mapMulEquivOfPresentation_apply_left H A rfl rfl p)
          (fun p ↦ CommHopfAlgCat.mapMulEquivOfPresentation_apply_left K A rfl rfl p)
          f (eK g))

/-- The map on scheme-valued points of an affine Hopf-spectrum morphism becomes precomposition
by its coordinate Hopf morphism on relative global sections. -/
theorem schemePointsAlgΓMulEquiv_pointMap
    {H K : CommHopfAlgCat.{u} R} (T : Over (Spec (CommRingCat.of R))) (f : H ⟶ K)
    (g : T ⟶ ((hopfSpec (CommRingCat.of R)).obj (Opposite.op K)).X) :
    schemePointsAlgΓMulEquiv H T
        (pointMap ((hopfSpec (CommRingCat.of R)).map f.op) T g) =
      AlgHom.mapDomain f.hom (schemePointsAlgΓMulEquiv K T g) := by
  rw [pointMap_apply]
  exact schemePointsAlgΓMulEquiv_mapDomain T f g

/-- If the represented kernel Hopf ideal is central, then the induced affine group-scheme
morphism has central kernel on points valued in every scheme over the base. -/
theorem hasCentralKernel_hopfSpec_map_of_isCentral_kernelHopfIdeal
    {H K : CommHopfAlgCat.{u} R} (f : H ⟶ K) (hf : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral) :
    HasCentralKernel ((hopfSpec (CommRingCat.of R)).map f.op) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center]
  intro T g hg
  let eK := schemePointsAlgΓMulEquiv K T
  let eH := schemePointsAlgΓMulEquiv H T
  have hmap : AlgHom.mapDomain f.hom (eK g) = 1 := by
    calc
      AlgHom.mapDomain f.hom (eK g) =
          eH (pointMap ((hopfSpec (CommRingCat.of R)).map f.op) T g) := by
        rw [schemePointsAlgΓMulEquiv_pointMap]
      _ = eH 1 := congrArg eH (MonoidHom.mem_ker.mp hg)
      _ = 1 := map_one eH
  have hmem : eK g ∈ CommHopfAlgCat.quotientPointsSubgroup K
      (CommHopfAlgCat.kernelHopfIdeal f) ((algΓ (CommRingCat.of R)).obj T).unop :=
    (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f _ (eK g)).mp hmap
  have hp := CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup
    K (CommHopfAlgCat.kernelHopfIdeal f) hf _ hmem
  rw [Subgroup.mem_center_iff]
  intro h
  apply eK.injective
  simpa only [map_mul] using (hp.commute (eK h)).eq.symm

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
  let eH := CommHopfAlgCat.mapMulEquivOfPresentation H B
    (G := (hopfSpec (CommRingCat.of R)).obj (Opposite.op H)) rfl
  let eK := CommHopfAlgCat.mapMulEquivOfPresentation K B
    (G := (hopfSpec (CommRingCat.of R)).obj (Opposite.op K)) rfl
  have hnat : eK gB ≫ ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom =
      eH ((CommHopfAlgCat.mapPointsFunctor f).app (CommAlgCat.of R B) gB) := by
    simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
      (CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain B
        (hG := rfl) (hH' := rfl) eH eK
        (fun p ↦ CommHopfAlgCat.mapMulEquivOfPresentation_apply_left H B rfl rfl p)
        (fun p ↦ CommHopfAlgCat.mapMulEquivOfPresentation_apply_left K B rfl rfl p) f gB)
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
  rw [commute_iff_eq]
  apply eK.injective
  simpa only [map_mul] using hs.symm

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
  constructor
  · intro hf
    exact ⟨hf.isIsogeny,
      (hasCentralKernel_hopfSpec_map_iff f).mp hf.hasCentralKernel⟩
  · rintro ⟨hf, hker⟩
    apply (isCentralIsogeny_iff _).mpr
    exact ⟨hf.isFinite, hf.flat, hf.surjective,
      (hasCentralKernel_hopfSpec_map_iff f).mpr hker⟩

/-- An isogeny induced by a coordinate Hopf morphism is central when its represented kernel Hopf
ideal is central. -/
theorem IsIsogeny.isCentral_of_isCentral_kernelHopfIdeal (f : H ⟶ K)
    (hf : IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op))
    (hker : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral) :
    IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) :=
  (isCentralIsogeny_hopfSpec_map_iff f).mpr ⟨hf, hker⟩

/-- The represented kernel Hopf ideal of a central affine group-scheme isogeny is central. -/
theorem IsCentralIsogeny.isCentral_kernelHopfIdeal (f : H ⟶ K)
    (hf : IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    (CommHopfAlgCat.kernelHopfIdeal f).IsCentral :=
  (isCentralIsogeny_hopfSpec_map_iff f).mp hf |>.2

end Field

end TauCeti.GroupScheme
