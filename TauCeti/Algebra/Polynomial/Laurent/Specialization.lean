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

* `RingHom.baseChangeModule.of_laurentEval_T_smul`: a Laurent shift acts by the corresponding
  integer-unit power after evaluation.
* `RingHom.baseChangeModule.of_laurentEvalOne_T_smul`: at `q = 1`, a Laurent shift acts
  trivially.
* `RingHom.baseChangeModule.of_laurentEvalNegOne_T_smul`: at `q = -1`, a Laurent shift acts
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

/-- At a unit `u`, a Laurent shift acts by the corresponding integer power on base change. -/
theorem _root_.RingHom.baseChangeModule.of_laurentEval_T_smul
    {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module (LaurentPolynomial R) M] (u : Aˣ) (n : ℤ) (x : M) :
    _root_.RingHom.baseChangeModule.of ((laurentEval (R := R) u).toRingHom) M
        ((T n : LaurentPolynomial R) • x) =
      ((u ^ n : Aˣ) : A) •
        _root_.RingHom.baseChangeModule.of ((laurentEval (R := R) u).toRingHom) M x := by
  rw [(_root_.RingHom.baseChangeModule.of _ _).map_smulₛₗ]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    congrArg (fun a : A => a •
      _root_.RingHom.baseChangeModule.of ((laurentEval (R := R) u).toRingHom) M x)
      (laurentEval_T (R := R) u n)

/-- At `q = 1`, a Laurent shift acts trivially after base change. -/
theorem _root_.RingHom.baseChangeModule.of_laurentEvalOne_T_smul
    {M : Type*} [AddCommMonoid M] [Module (LaurentPolynomial ℤ) M] (n : ℤ) (x : M) :
    _root_.RingHom.baseChangeModule.of laurentEvalOne M
        ((T n : LaurentPolynomial ℤ) • x) =
      _root_.RingHom.baseChangeModule.of laurentEvalOne M x := by
  simp only [TauCeti.laurentEvalOne]
  rw [RingHom.baseChangeModule.of_laurentEval_T_smul]
  rw [one_zpow, Units.val_one, one_smul]

/-- At `q = -1`, a Laurent shift acts by the sign `n.negOnePow` after base change. -/
theorem _root_.RingHom.baseChangeModule.of_laurentEvalNegOne_T_smul
    {M : Type*} [AddCommMonoid M] [Module (LaurentPolynomial ℤ) M] (n : ℤ) (x : M) :
    _root_.RingHom.baseChangeModule.of laurentEvalNegOne M
        ((T n : LaurentPolynomial ℤ) • x) =
    (n.negOnePow : ℤ) •
      _root_.RingHom.baseChangeModule.of laurentEvalNegOne M x := by
  simp only [TauCeti.laurentEvalNegOne]
  rw [RingHom.baseChangeModule.of_laurentEval_T_smul]
  simp [Int.negOnePow_def]

end TauCeti
