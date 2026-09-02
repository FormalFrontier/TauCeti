/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Algebra.TensorProduct.RingHomBaseChange

/-!
# Specialization of Laurent modules

This file applies scalar extension of a module along evaluation maps.  For the coefficient ring
`ℤ[q,q⁻¹]`, the two distinguished evaluations are `laurentEvalOne` and `laurentEvalNegOne`; the
resulting shift formulas record the specializations at `q = 1` and `q = -1`.

## Main results

* `TauCeti.RingHom.baseChangeModule_laurentEval_T_smul`: a Laurent shift acts by the corresponding
  integer-unit power after evaluation.
* `TauCeti.RingHom.baseChangeModule_laurentEvalOne_T_smul`: at `q = 1`, a Laurent shift acts
  trivially.
* `TauCeti.RingHom.baseChangeModule_laurentEvalNegOne_T_smul`: at `q = -1`, a Laurent shift acts
  by the sign `n.negOnePow`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 3.1, for the specialization convention and
  the warning that specialization may change nondegeneracy.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "Algebraic specialization".
-/

public section

namespace TauCeti

open LaurentPolynomial

variable {M : Type*} [AddCommMonoid M] [Module (LaurentPolynomial ℤ) M]

/-- At a unit `u`, a Laurent shift acts by the corresponding integer power on base change. -/
theorem RingHom.baseChangeModule_laurentEval_T_smul (u : ℤˣ) (n : ℤ) (x : M) :
    RingHom.baseChangeModule.of ((laurentEval (R := ℤ) u).toRingHom) M
        ((T n : LaurentPolynomial ℤ) • x) =
      ((u ^ n : ℤˣ) : ℤ) •
        RingHom.baseChangeModule.of ((laurentEval (R := ℤ) u).toRingHom) M x := by
  rw [(RingHom.baseChangeModule.of _ _).map_smulₛₗ]
  change laurentEval (R := ℤ) u (T n) • _ = _
  rw [laurentEval_T]

/-- At `q = 1`, a Laurent shift acts trivially after base change. -/
theorem RingHom.baseChangeModule_laurentEvalOne_T_smul (n : ℤ) (x : M) :
    RingHom.baseChangeModule.of laurentEvalOne M
        ((T n : LaurentPolynomial ℤ) • x) =
      RingHom.baseChangeModule.of laurentEvalOne M x := by
  rw [laurentEvalOne_def]
  rw [RingHom.baseChangeModule_laurentEval_T_smul]
  rw [one_zpow, Units.val_one, one_smul]

/-- At `q = -1`, a Laurent shift acts by the sign `n.negOnePow` after base change. -/
theorem RingHom.baseChangeModule_laurentEvalNegOne_T_smul (n : ℤ) (x : M) :
    RingHom.baseChangeModule.of laurentEvalNegOne M
        ((T n : LaurentPolynomial ℤ) • x) =
    (n.negOnePow : ℤ) •
      RingHom.baseChangeModule.of laurentEvalNegOne M x := by
  rw [laurentEvalNegOne_def]
  rw [RingHom.baseChangeModule_laurentEval_T_smul]
  simp [Int.negOnePow_def]

end TauCeti
