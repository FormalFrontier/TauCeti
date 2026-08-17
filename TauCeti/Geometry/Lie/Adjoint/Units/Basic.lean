/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The adjoint action on units of a normed algebra

For the Lie group of units of a complete real normed algebra, the tangent adjoint action is
ordinary algebra conjugation. In finite dimensions, the same formula describes the adjoint on
left-invariant derivations under the canonical identification with the ambient algebra. We obtain
the tangent formula by differentiating exponential equivariance along a line, reusing the already
established compatibility between the abstract Lie-group exponential and the Banach-algebra
exponential.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `tangentAd_units`: on the tangent Lie algebra of the unit group, `tangentAd g x` is
  `g * x * g⁻¹`.
* `unitsLieAlgebraEquiv_Ad`: under the canonical identification with the ambient algebra,
  `Ad g X` is `g * X * g⁻¹`.
* `groupLieAlgebra_units_ad_apply`: the tangent Lie bracket on algebra units is the associative
  commutator.
* `unitsLieAlgebraLieEquiv`: the canonical units identification as a Lie equivalence.
* `unitsLieAlgebraEquiv_ad`: the units identification transports the abstract adjoint operator to
  the bounded commutator operator.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] TauCeti.normedAlgebraRatOfReal

section Complete

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- On the units of a complete real normed algebra, the tangent adjoint is ordinary conjugation
in the ambient algebra. -/
@[simp high]
theorem tangentAd_units (g : Rˣ) (x : R) :
    tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) =
      (g : R) * x * ((g⁻¹ : Rˣ) : R) := by
  let y : R := tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
  have hfun :
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * ((g⁻¹ : Rˣ) : R)) =
      fun t : ℝ => (TauCeti.expUnitHom y (Multiplicative.ofAdd t) : R) := by
    funext t
    have h := conj_mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) g
      (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) (1 : Rˣ) t
    dsimp only at h
    simp only [mul_one, mul_inv_cancel] at h
    rw [← mulInvariantOneParameterSubgroup_apply
      (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) t] at h
    rw [← mulInvariantOneParameterSubgroup_apply
      (I := 𝓘(ℝ, R)) (G := Rˣ)
        (tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) t] at h
    -- The unit group's Lie algebra is definitionally its model space `R`; expose that
    -- identification so the bundled subgroup equalities can rewrite both sides.
    change g * mulInvariantOneParameterSubgroup
      (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
        (Multiplicative.ofAdd t) * g⁻¹ =
      mulInvariantOneParameterSubgroup
        (I := 𝓘(ℝ, R)) (G := Rˣ) (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
          (Multiplicative.ofAdd t) at h
    rw [mulInvariantOneParameterSubgroup_eq_expUnitHom,
      mulInvariantOneParameterSubgroup_eq_expUnitHom] at h
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, y] using congrArg Units.val h
  have hx := TauCeti.hasDerivAt_expUnitHom_val_zero x
  have hy := TauCeti.hasDerivAt_expUnitHom_val_zero y
  have hconj : HasDerivAt
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * ((g⁻¹ : Rˣ) : R))
      ((g : R) * x * ((g⁻¹ : Rˣ) : R)) 0 :=
    (HasDerivAt.const_mul (g : R) hx).mul_const (g⁻¹ : Rˣ)
  rw [hfun] at hconj
  exact hy.unique hconj

end Complete

section FiniteDimensional

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceAdjointUnits : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- The Lie bracket on the tangent Lie algebra of algebra units is the associative commutator. -/
@[simp]
theorem groupLieAlgebra_units_ad_apply (x y : R) :
    (show R from LieAlgebra.ad ℝ (GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
      (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) =
      x * y - y * x := by
  -- For units the model space, and hence `GroupLieAlgebra`, is definitionally the ambient algebra
  -- `R`; the displayed casts expose that identification to the generic tangent-adjoint theorem.
  let _ : T2Space Rˣ := t2Space_of_lieGroup (I := 𝓘(ℝ, R)) (n := ∞)
  have hgeom := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero
    (I := 𝓘(ℝ, R)) (G := Rˣ)
    (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
  have hcurve : (fun t : ℝ => show R from tangentAd (I := 𝓘(ℝ, R))
      (mulInvariantExp (I := 𝓘(ℝ, R)) (G := Rˣ)
        (t • (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)))
      (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) =
      fun t : ℝ => NormedSpace.exp (t • x) * y * NormedSpace.exp (-(t • x)) := by
    funext t
    rw [tangentAd_units]
    have hexp : mulInvariantExp (I := 𝓘(ℝ, R)) (G := Rˣ)
        (t • (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) = TauCeti.expUnit (t • x) := by
      have h := DFunLike.congr_fun
        (mulInvariantOneParameterSubgroup_eq_expUnitHom (R := R) x)
        (Multiplicative.ofAdd t)
      rw [show (mulInvariantOneParameterSubgroup
        (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ))
          (Multiplicative.ofAdd t) =
        mulInvariantExp (I := 𝓘(ℝ, R)) (G := Rˣ)
          (t • (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) from
            mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul
              (I := 𝓘(ℝ, R)) (G := Rˣ) x t] at h
      simpa only [TauCeti.expUnitHom_apply] using h
    rw [hexp]
    simp only [TauCeti.expUnit_coe, ← TauCeti.expUnit_neg, TauCeti.expUnit_coe]
  have hx := hasDerivAt_exp_smul_const x (0 : ℝ)
  have hnegx := hasDerivAt_exp_smul_const (-x) (0 : ℝ)
  have hexp : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • x) * y * NormedSpace.exp (-(t • x)))
      (x * y - y * x) 0 := by
    convert (hx.mul_const y).mul hnegx using 1
    · funext t
      rw [Pi.mul_apply, smul_neg]
    · simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg,
        sub_eq_add_neg]
  have hgeom' : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • x) * y * NormedSpace.exp (-(t • x)))
      (show R from LieAlgebra.ad ℝ (GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
        (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) 0 := by
    rw [← hcurve]
    exact hgeom
  exact hgeom'.unique hexp

/-- On the units of a finite-dimensional real normed algebra, the abstract group adjoint is
ordinary conjugation in the ambient algebra. -/
@[simp high]
theorem unitsLieAlgebraEquiv_Ad (g : Rˣ)
    (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) g X) =
      (g : R) * unitsLieAlgebraEquiv X * (g⁻¹ : Rˣ) := by
  have h := leftInvariantDerivationLieEquivGroupLieAlgebra_Ad
    (I := 𝓘(ℝ, R)) g X
  -- Expose the same definitional identification with `R` to compare the general tangent-space
  -- transport theorem with the units-specific equivalence.
  have hR := congrArg
    (fun x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ ↦ show R from x) h
  have ht := tangentAd_units (R := R) g
    (show R from leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := 𝓘(ℝ, R)) (G := Rˣ)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, R)) (n := ∞) (by simp) (1 : Rˣ)) X)
  rw [ht] at hR
  simpa only [unitsLieAlgebraEquiv_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply] using hR

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical identification of the Lie algebra of `Rˣ` with `R`, equipped with its associative
commutator bracket. -/
noncomputable def unitsLieAlgebraLieEquiv :
    LeftInvariantDerivation 𝓘(ℝ, R) Rˣ ≃ₗ⁅ℝ⁆ R :=
  { unitsLieAlgebraEquiv (R := R) with
    map_lie' := by
      intro X Y
      let _ : T2Space Rˣ := t2Space_of_lieGroup (I := 𝓘(ℝ, R)) (n := ∞)
      let e := leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := 𝓘(ℝ, R)) (G := Rˣ) BoundarylessManifold.isInteriorPoint
      have hmap := e.map_lie X Y
      have hmapR := congrArg
        (fun z : GroupLieAlgebra 𝓘(ℝ, R) Rˣ => show R from z) hmap
      dsimp only [e] at hmapR
      have hgroup := groupLieAlgebra_units_ad_apply (R := R)
        (unitsLieAlgebraEquiv X) (unitsLieAlgebraEquiv Y)
      have hcomm : ⁅unitsLieAlgebraEquiv X, unitsLieAlgebraEquiv Y⁆ =
          unitsLieAlgebraEquiv X * unitsLieAlgebraEquiv Y -
            unitsLieAlgebraEquiv Y * unitsLieAlgebraEquiv X := by
        exact LieRing.of_associative_ring_bracket _ _
      have hmapUnits : unitsLieAlgebraEquiv ⁅X, Y⁆ =
          (show R from LieAlgebra.ad ℝ (GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
            (show GroupLieAlgebra 𝓘(ℝ, R) Rˣ from
              (unitsLieAlgebraEquiv (R := R) X : R))
            (show GroupLieAlgebra 𝓘(ℝ, R) Rˣ from
              (unitsLieAlgebraEquiv (R := R) Y : R))) := by
        rw [LieAlgebra.ad_apply]
        simpa only [unitsLieAlgebraEquiv_apply,
          leftInvariantDerivationLieEquivGroupLieAlgebra_apply] using hmapR
      exact hmapUnits.trans (hgroup.trans hcomm.symm) }

/-- The units Lie equivalence has the same forward map as the canonical linear equivalence. -/
@[simp]
theorem unitsLieAlgebraLieEquiv_apply (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraLieEquiv X = unitsLieAlgebraEquiv X := by
  rfl

/-- The inverse units Lie equivalence has the same map as the inverse canonical linear
equivalence. -/
@[simp]
theorem unitsLieAlgebraLieEquiv_symm_apply (x : R) :
    (unitsLieAlgebraLieEquiv (R := R)).symm x =
      (unitsLieAlgebraEquiv (R := R)).symm x := by
  rfl

/-- Forgetting the bracket-preserving structure recovers the canonical linear equivalence. -/
@[simp]
theorem unitsLieAlgebraLieEquiv_toLinearEquiv :
    (unitsLieAlgebraLieEquiv (R := R)).toLinearEquiv = unitsLieAlgebraEquiv := by
  rfl

local instance finiteDimensionalLeftInvariantDerivationAdjointUnits :
    FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- Conjugating the abstract adjoint operator by the units Lie-algebra identification gives the
bounded associative commutator operator. -/
@[simp]
theorem unitsLieAlgebraEquiv_ad (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    let e := (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv
    e.conjContinuousAlgEquiv
        (LinearMap.toContinuousLinearMap
          (LieAlgebra.ad ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) X)) =
      continuousCommutator (unitsLieAlgebraEquiv X) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro Y
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    LinearMap.coe_toContinuousLinearMap']
  -- The conjugation API exposes continuous-linear maps, while the characteristic equivalence is
  -- linear; change only the wrapper so the explicit Lie-equivalence application lemmas can apply.
  change unitsLieAlgebraEquiv (LieAlgebra.ad ℝ _ X
    ((unitsLieAlgebraEquiv (R := R)).symm Y)) = continuousCommutator _ Y
  rw [LieAlgebra.ad_apply]
  change unitsLieAlgebraLieEquiv ⁅X, (unitsLieAlgebraLieEquiv (R := R)).symm Y⁆ =
    continuousCommutator _ Y
  rw [unitsLieAlgebraLieEquiv.map_lie, LieEquiv.apply_symm_apply,
    LieRing.of_associative_ring_bracket, continuousCommutator_apply]
  rfl

end FiniteDimensional

end TauCeti.Lie
