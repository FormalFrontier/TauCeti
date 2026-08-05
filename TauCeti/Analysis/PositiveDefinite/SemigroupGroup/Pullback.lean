/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Spatial pullbacks of semigroup-group positive-definite functions

This file records the spatial-coordinate pullback API for Berg--Christensen--Ressel
positive-definite functions on `ℝ≥0 × V`. If `F` is semigroup-group positive definite and
`φ : W →+ V` is an additive homomorphism, then `(t, w) ↦ F (t, φ w)` is again
semigroup-group positive definite.

This is a small prerequisite for the BCR semigroup--Bochner representation milestone in the
`OneParameterSemigroups` roadmap. The Bochner part is stated on an arbitrary finite-dimensional
real inner-product space, so downstream arguments need to transport the spatial variable along
additive equivalences and continuous linear maps without unfolding the private BCR wrapper.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
function API item "pullbacks" and Milestone 2 ("BCR semigroup--Bochner").

## Main declarations

* `TauCeti.IsSemigroupGroupPD.comp_spatial`: spatial pullback along an additive homomorphism,
  stated using Mathlib's homomorphism classes.
* `TauCeti.IsSemigroupGroupPD.comp_spatial_comp`: composition of spatial pullbacks, stated
  using Mathlib's homomorphism classes.
* `TauCeti.IsSemigroupGroupPD.of_comp_spatial_surjective` and
  `TauCeti.IsSemigroupGroupPD.comp_spatial_iff_of_surjective`: descent and equivalence for
  surjective additive homomorphisms.
* `TauCeti.IsSemigroupGroupPD.comp_spatial_addEquiv_iff`: invariance under a spatial additive
  equivalence.
* `TauCeti.IsSemigroupGroupPD.comp_spatial_continuousLinearMap`: the continuous-linear-map form
  used for real vector spaces.
* `TauCeti.IsSemigroupGroupPD.continuous_comp_spatial`: spatial pullback preserves continuity
  along continuous maps.
* `TauCeti.IsSemigroupGroupPD.comp_spatial_and_continuous`,
  `TauCeti.IsSemigroupGroupPD.comp_spatial_continuousLinearMap_and_continuous`: packaged
  homomorphism-class and continuous-linear forms preserving both positive-definiteness and
  continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped NNReal ComplexOrder

namespace TauCeti

namespace IsSemigroupGroupPD

variable {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  {F : ℝ≥0 × V → ℂ}

private theorem map_sub_of_addHomClass {Φ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    (φ : Φ) (x y : W) : φ (x - y) = φ x - φ y := by
  have hneg : φ (-y) = -φ y := by
    have hzero : φ (0 : W) = 0 := by
      have h := map_add φ (0 : W) (0 : W)
      have h' : φ (0 : W) + φ (0 : W) = φ (0 : W) + 0 := by simpa using h.symm
      exact add_left_cancel h'
    have h := map_add φ y (-y)
    have hsum : φ y + φ (-y) = 0 := by
      simpa [hzero] using h.symm
    exact eq_neg_of_add_eq_zero_right hsum
  simp [sub_eq_add_neg, map_add, hneg]

/-- Pulling back the spatial coordinate of a semigroup-group positive-definite function along an
additive homomorphism preserves semigroup-group positive-definiteness. This is stated for
Mathlib's homomorphism classes so it applies to bundled additive homomorphisms, additive
equivalences, continuous linear maps, and similar maps. -/
theorem comp_spatial {Φ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    (hF : IsSemigroupGroupPD F) (φ : Φ) :
    IsSemigroupGroupPD fun p : ℝ≥0 × W => F (p.1, φ p.2) := by
  refine IsSemigroupGroupPD.of_isPositiveDefiniteKernel ?_
  have hK := isPositiveDefiniteKernel_comp hF.isPositiveDefiniteKernel
    (fun p : ℝ≥0 × W => (p.1, φ p.2))
  simpa [map_sub_of_addHomClass φ] using hK

/-- The explicit `AddMonoidHom` form of spatial pullback. -/
theorem comp_spatial_addMonoidHom (hF : IsSemigroupGroupPD F) (φ : W →+ V) :
    IsSemigroupGroupPD fun p : ℝ≥0 × W => F (p.1, φ p.2) :=
  hF.comp_spatial φ

/-- Spatial pullbacks compose as expected. -/
theorem comp_spatial_comp {Φ Ψ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    [FunLike Ψ U W] [AddHomClass Ψ U W] (hF : IsSemigroupGroupPD F) (φ : Φ) (ψ : Ψ) :
    IsSemigroupGroupPD fun p : ℝ≥0 × U => F (p.1, φ (ψ p.2)) :=
  (hF.comp_spatial φ).comp_spatial ψ

/-- Semigroup-group positive-definiteness descends along a surjective spatial additive
homomorphism. -/
theorem of_comp_spatial_surjective {Φ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    (φ : Φ) (hsurj : Function.Surjective φ)
    (hcomp : IsSemigroupGroupPD fun p : ℝ≥0 × W => F (p.1, φ p.2)) :
    IsSemigroupGroupPD F := by
  classical
  refine IsSemigroupGroupPD.of_isPositiveDefiniteKernel ?_
  choose w hw using hsurj
  have hK := isPositiveDefiniteKernel_comp hcomp.isPositiveDefiniteKernel
    (fun p : ℝ≥0 × V => (p.1, w p.2))
  simpa [hw, map_sub_of_addHomClass φ] using hK

/-- Along a surjective spatial additive homomorphism, a function is semigroup-group positive
definite if and only if its spatial pullback is. -/
theorem comp_spatial_iff_of_surjective {Φ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    (φ : Φ) (hsurj : Function.Surjective φ) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, φ p.2)) ↔ IsSemigroupGroupPD F :=
  ⟨of_comp_spatial_surjective φ hsurj, fun hF => hF.comp_spatial φ⟩

/-- The explicit `AddMonoidHom` form of the spatial pullback equivalence for surjective maps. -/
theorem comp_spatial_addMonoidHom_iff_of_surjective (φ : W →+ V) (hsurj : Function.Surjective φ) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, φ p.2)) ↔ IsSemigroupGroupPD F :=
  comp_spatial_iff_of_surjective φ hsurj

/-- Semigroup-group positive-definiteness is invariant under precomposition by a spatial
additive equivalence. -/
theorem comp_spatial_addEquiv_iff (e : W ≃+ V) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, e p.2)) ↔ IsSemigroupGroupPD F :=
  comp_spatial_addMonoidHom_iff_of_surjective e.toAddMonoidHom e.surjective

section Topology

variable [TopologicalSpace V] [TopologicalSpace W]

omit [AddCommGroup V] [AddCommGroup W] in
/-- If the spatial map is continuous, spatial pullback preserves continuity. -/
theorem continuous_comp_spatial (hF : Continuous F) (φ : W → V) (hφ : Continuous φ) :
    Continuous fun p : ℝ≥0 × W => F (p.1, φ p.2) :=
  hF.comp (continuous_fst.prodMk (hφ.comp continuous_snd))

/-- Package spatial pullback of a semigroup-group positive-definite function with continuity
of the pulled-back function. -/
theorem comp_spatial_and_continuous {Φ : Type*} [FunLike Φ W V] [AddHomClass Φ W V]
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) (φ : Φ) (hφ : Continuous φ) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × W => F (p.1, φ p.2)) ∧
      Continuous (fun p : ℝ≥0 × W => F (p.1, φ p.2)) :=
  ⟨hFpd.comp_spatial φ, continuous_comp_spatial hFcont φ hφ⟩

end Topology

section ContinuousLinearMap

variable {E : Type*} {E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {G : ℝ≥0 × E → ℂ}

/-- Spatial pullback along a continuous linear map preserves semigroup-group
positive-definiteness. -/
theorem comp_spatial_continuousLinearMap (hG : IsSemigroupGroupPD G) (φ : E' →L[ℝ] E) :
    IsSemigroupGroupPD fun p : ℝ≥0 × E' => G (p.1, φ p.2) :=
  hG.comp_spatial φ

/-- Spatial pullback along a continuous linear equivalence is an equivalence on
semigroup-group positive-definiteness. -/
theorem comp_spatial_continuousLinearEquiv_iff (e : E' ≃L[ℝ] E) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × E' => G (p.1, e p.2)) ↔ IsSemigroupGroupPD G :=
  comp_spatial_addEquiv_iff e.toAddEquiv

/-- Package spatial pullback along a continuous linear map with preservation of continuity. -/
theorem comp_spatial_continuousLinearMap_and_continuous (hGpd : IsSemigroupGroupPD G)
    (hGcont : Continuous G) (φ : E' →L[ℝ] E) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × E' => G (p.1, φ p.2)) ∧
      Continuous (fun p : ℝ≥0 × E' => G (p.1, φ p.2)) :=
  hGpd.comp_spatial_and_continuous hGcont φ φ.continuous

end ContinuousLinearMap

end IsSemigroupGroupPD

end TauCeti
