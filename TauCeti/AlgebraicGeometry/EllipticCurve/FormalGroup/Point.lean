/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Eval

/-!
# Points of a Weierstrass curve from formal-group parameters
-/

public section

open PowerSeries

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {K : Type*} [Field K] [Algebra O K]

namespace WeierstrassCurve

variable (W : WeierstrassCurve O)

theorem formalPoint_equation {t : O} (ht : PowerSeries.HasEval t)
    (hw : algebraMap O K (W.formalWEval t) ≠ 0) :
    (W.baseChange K).toAffine.Equation
      (algebraMap O K t / algebraMap O K (W.formalWEval t))
      (-(algebraMap O K (W.formalWEval t))⁻¹) := by
  have hkey := congrArg (algebraMap O K) (W.formalWEval_wEquation ht)
  rw [wEquationRHS_def] at hkey
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hkey
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  field_simp
  linear_combination hkey

variable [W.IsElliptic]

theorem formalPoint_nonsingular {t : O} (ht : PowerSeries.HasEval t)
    (hw : algebraMap O K (W.formalWEval t) ≠ 0) :
    (W.baseChange K).toAffine.Nonsingular
      (algebraMap O K t / algebraMap O K (W.formalWEval t))
      (-(algebraMap O K (W.formalWEval t))⁻¹) := by
  have hΔ : (W.baseChange K).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact (W.isUnit_Δ.map _).ne_zero
  exact ((W.baseChange K).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (W.formalPoint_equation ht hw)

variable [IsDomain O] [IsFractionRing O K]

omit [W.IsElliptic] in
/-- `w(t)` is nonzero in `K` at a nonzero parameter of an adic ideal: it factors as
`t ^ 3 * u(t)` with `u(t)` a unit, and `algebraMap O K` is injective. -/
theorem algebraMap_formalWEval_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) : algebraMap O K (W.formalWEval t) ≠ 0 := by
  have h3 : t ^ 3 ≠ 0 := pow_ne_zero _ ht0
  exact fun h ↦ W.formalWEval_ne_zero hI ht h3
    ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective O K) _ h)

open scoped Classical in
/-- **The point attached to a formal-group parameter**: a nonzero `t` in an adic ideal gives the
affine point `(t / w(t), -1 / w(t))`, and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    (W.baseChange K).toAffine.Point :=
  if h0 : t = 0 then 0
  else .some _ _ (W.formalPoint_nonsingular (K := K)
    (hI.isTopologicallyNilpotent_of_mem ht)
    (W.algebraMap_formalWEval_ne_zero hI ht h0))

open scoped Classical in
@[simp]
theorem formalPoint_of_eq_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t = 0) :
    W.formalPoint (K := K) hI ht = 0 :=
  dif_pos h0

open scoped Classical in
theorem formalPoint_of_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t ≠ 0) :
    W.formalPoint (K := K) hI ht =
      .some _ _ (W.formalPoint_nonsingular (K := K) (hI.isTopologicallyNilpotent_of_mem ht)
        (W.algebraMap_formalWEval_ne_zero hI ht h0)) :=
  dif_neg h0

end WeierstrassCurve
