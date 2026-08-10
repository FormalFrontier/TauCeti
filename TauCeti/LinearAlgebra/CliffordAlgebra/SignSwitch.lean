/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Project
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Sign-switch equivalence for Clifford algebras

Adjoining one positive line identifies the Clifford algebras of a quadratic form and its
negation. The construction is generic over a commutative ring.

## Main results

* `TauCeti.CliffordAlgebra.signSwitchEquiv`: the sign-switch algebra equivalence;
* `TauCeti.CliffordAlgebra.signSwitchEquiv_ι`: its equation on generators;
* `TauCeti.CliffordAlgebra.signSwitchEquiv_symm_apply_ι`: the inverse generator equation.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open Module QuadraticMap

namespace TauCeti.CliffordAlgebra

section SignSwitch

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (P P' : QuadraticForm R N)

private def signSwitchGenerator :
    N × R →ₗ[R]
      _root_.CliffordAlgebra (P'.prod (QuadraticMap.sq (R := R) (A := R))) :=
  ((LinearMap.mulLeft R
      (_root_.CliffordAlgebra.ι (P'.prod (QuadraticMap.sq (R := R) (A := R))) (0, 1))).comp
    ((_root_.CliffordAlgebra.ι (P'.prod (QuadraticMap.sq (R := R) (A := R)))).comp
      (LinearMap.inl R N R))).coprod
    (LinearMap.toSpanSingleton R _
      (_root_.CliffordAlgebra.ι
        (P'.prod (QuadraticMap.sq (R := R) (A := R))) (0, 1)))

private theorem signSwitchGenerator_apply (x : N × R) :
    signSwitchGenerator P' x =
      _root_.CliffordAlgebra.ι
          (P'.prod (QuadraticMap.sq (R := R) (A := R))) (0, 1) *
          _root_.CliffordAlgebra.ι
            (P'.prod (QuadraticMap.sq (R := R) (A := R))) (x.1, 0) +
        x.2 • _root_.CliffordAlgebra.ι
          (P'.prod (QuadraticMap.sq (R := R) (A := R))) (0, 1) :=
  rfl

private theorem signSwitchGenerator_sq (h : P' = -P) (x : N × R) :
    signSwitchGenerator P' x * signSwitchGenerator P' x =
      algebraMap R _ ((P.prod (QuadraticMap.sq (R := R) (A := R))) x) := by
  let Q' := P'.prod (QuadraticMap.sq (R := R) (A := R))
  let e := _root_.CliffordAlgebra.ι Q' (0, 1)
  let v := _root_.CliffordAlgebra.ι Q' (x.1, 0)
  have he : e * e = 1 := by
    dsimp only [e]
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [Q']
  have hv : v * v = algebraMap R _ (-P x.1) := by
    dsimp only [v]
    rw [_root_.CliffordAlgebra.ι_sq_scalar]
    simp [Q', h]
  have hev : e * v + v * e = 0 := by
    dsimp only [e, v]
    rw [_root_.CliffordAlgebra.ι_mul_ι_add_swap]
    simp [Q', QuadraticMap.polar]
  rw [signSwitchGenerator_apply]
  -- Expose the two local Clifford generators used in the square calculation.
  change (e * v + x.2 • e) * (e * v + x.2 • e) = _
  rw [Algebra.smul_def]
  let r := algebraMap R (_root_.CliffordAlgebra Q') x.2
  -- Name the scalar's central image so the four noncommutative terms can be compared directly.
  change (e * v + r * e) * (e * v + r * e) = _
  have hve : v * e = -(e * v) := eq_neg_of_add_eq_zero_right hev
  have hre : r * e = e * r := Algebra.commutes x.2 e
  have hrv : r * v = v * r := Algebra.commutes x.2 v
  have hterm1 : (e * v) * (e * v) = -(v * v) := by
    calc
      (e * v) * (e * v) = e * ((v * e) * v) := by simp only [mul_assoc]
      _ = e * (-(e * v) * v) := by rw [hve]
      _ = -(v * v) := by rw [neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, he, one_mul]
  have hterm2 : (e * v) * (r * e) = -(r * v) := by
    calc
      (e * v) * (r * e) = e * (v * r) * e := by simp only [mul_assoc]
      _ = e * (r * v) * e := by rw [hrv]
      _ = (e * r) * v * e := by simp only [mul_assoc]
      _ = (r * e) * v * e := by rw [← hre]
      _ = r * (e * v) * e := by rw [mul_assoc r e v]
      _ = r * (e * (v * e)) := by simp only [mul_assoc]
      _ = r * (e * (-(e * v))) := by rw [hve]
      _ = -(r * v) := by rw [mul_neg, mul_neg, ← mul_assoc e e, he, one_mul]
  have hterm3 : (r * e) * (e * v) = r * v := by
    rw [mul_assoc r e, ← mul_assoc e e, he, one_mul]
  have hterm4 : (r * e) * (r * e) = r * r := by
    calc
      (r * e) * (r * e) = r * (e * r) * e := by simp only [mul_assoc]
      _ = r * (r * e) * e := by rw [← hre]
      _ = r * r * (e * e) := by simp only [mul_assoc]
      _ = r * r := by rw [he, mul_one]
  calc
    (e * v + r * e) * (e * v + r * e) = -(v * v) + r * r := by
      rw [mul_add, add_mul, add_mul, hterm1, hterm2, hterm3, hterm4]
      abel
    _ = algebraMap R _ (P x.1 + x.2 * x.2) := by
      rw [hv, map_neg, neg_neg, ← map_mul, ← map_add]
    _ = algebraMap R _ ((P.prod (QuadraticMap.sq (R := R) (A := R))) x) := by
      simp [QuadraticMap.prod_apply]

private def signSwitchTo (h : P' = -P) :
    _root_.CliffordAlgebra (P.prod (QuadraticMap.sq (R := R) (A := R))) →ₐ[R]
      _root_.CliffordAlgebra (P'.prod (QuadraticMap.sq (R := R) (A := R))) :=
  _root_.CliffordAlgebra.lift _ ⟨signSwitchGenerator P', signSwitchGenerator_sq P P' h⟩

private theorem signSwitchTo_ι (h : P' = -P) (x : N × R) :
    signSwitchTo P P' h (_root_.CliffordAlgebra.ι _ x) = signSwitchGenerator P' x :=
  _root_.CliffordAlgebra.lift_ι_apply _ _ x

private theorem signSwitchTo_comp_signSwitchTo
    (h : P' = -P) (h' : P = -P') :
    (signSwitchTo P' P h').comp (signSwitchTo P P' h) = AlgHom.id R _ := by
  apply _root_.CliffordAlgebra.hom_ext
  apply LinearMap.ext
  rintro ⟨m, r⟩
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    signSwitchTo_ι, signSwitchGenerator_apply, map_add, map_mul, map_smul]
  -- Split a source generator into its module and scalar components for the linear lift.
  rw [show (m, r) = (m, 0) + r • (0, 1) by ext <;> simp, map_add, map_smul]
  -- Expose the zero module-scalar pair so the Clifford generator reduces with `map_zero`.
  rw [show ((0 : N), (0 : R)) = 0 by rfl, map_zero]
  simp only [mul_zero, zero_add, add_zero, one_smul, zero_smul]
  rw [← mul_assoc, _root_.CliffordAlgebra.ι_sq_scalar]
  simp

/-- Adjoining a positive line to a quadratic form or to its negation gives equivalent Clifford
algebras. -/
def signSwitchEquiv :
    _root_.CliffordAlgebra (P.prod (QuadraticMap.sq (R := R) (A := R))) ≃ₐ[R]
      _root_.CliffordAlgebra ((-P).prod (QuadraticMap.sq (R := R) (A := R))) :=
  AlgEquiv.ofAlgHom (signSwitchTo P (-P) rfl) (signSwitchTo (-P) P (neg_neg P).symm)
    (signSwitchTo_comp_signSwitchTo (-P) P (neg_neg P).symm rfl)
    (signSwitchTo_comp_signSwitchTo P (-P) rfl (neg_neg P).symm)

/-- The sign-switch equivalence sends a generating pair to the product with the new positive
generator plus its scalar component. -/
@[simp]
theorem signSwitchEquiv_ι (x : N × R) :
    signSwitchEquiv P (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι _ (0, 1) * _root_.CliffordAlgebra.ι _ (x.1, 0) +
        x.2 • _root_.CliffordAlgebra.ι _ (0, 1) := by
  rw [signSwitchEquiv, AlgEquiv.ofAlgHom_apply, signSwitchTo_ι,
    signSwitchGenerator_apply]

/-- The inverse sign-switch equivalence has the same equation on Clifford generators. -/
@[simp]
theorem signSwitchEquiv_symm_apply_ι (x : N × R) :
    (signSwitchEquiv P).symm (_root_.CliffordAlgebra.ι _ x) =
      _root_.CliffordAlgebra.ι _ (0, 1) * _root_.CliffordAlgebra.ι _ (x.1, 0) +
        x.2 • _root_.CliffordAlgebra.ι _ (0, 1) := by
  -- Expose the reverse lift stored in `AlgEquiv.ofAlgHom` so its generator equation applies.
  change signSwitchTo (-P) P (neg_neg P).symm (_root_.CliffordAlgebra.ι _ x) = _
  rw [signSwitchTo_ι, signSwitchGenerator_apply]

end SignSwitch

end TauCeti.CliffordAlgebra
