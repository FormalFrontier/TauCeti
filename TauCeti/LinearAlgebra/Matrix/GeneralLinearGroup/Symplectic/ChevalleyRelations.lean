/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Chevalley commutator relations in the symplectic group

This file proves the rank-two, multiply-laced commutator relations among the explicit root
subgroups of `TauCeti.GLSymplecticFin`. For distinct `i` and `j`, the roots
`eᵢ - eⱼ`, `2eⱼ`, `eᵢ + eⱼ`, and `2eᵢ` form a type-`C₂` root string, and the chosen
matrix parametrizations satisfy

```text
⁅x_{eᵢ-eⱼ}(a), x_{2eⱼ}(b)⁆
  = x_{eᵢ+eⱼ}(ab) x_{2eᵢ}(a²b).
```

The second relation records the non-unit structure constant in the same rank-two system:

```text
⁅x_{eᵢ-eⱼ}(a), x_{eᵢ+eⱼ}(b)⁆ = x_{2eᵢ}(2ab).
```

These are the two rank-two relations needed to compare the standard symplectic realization with
the characteristic-two special isogeny of type `B₂/C₂`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2 and §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- **The multiply-laced Chevalley relation in the standard symplectic group.** The commutator
of `x_{eᵢ-eⱼ}(a)` and `x_{2eⱼ}(b)` is the product of the two remaining root subgroups in
their root string, with parameters `ab` and `a²b`. -/
theorem commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
    ⁅differenceShortRootUnit hij a, positiveLongRootTransvectionUnit j b⁆ =
      positiveSumShortRootUnit hij (a * b) *
        positiveLongRootTransvectionUnit i (a ^ 2 * b) := by
  apply Subtype.ext
  -- The subgroup coercion does not expose the commutator to rewriting, so spell out the same
  -- equality in the ambient general linear group before using the type-A relations.
  change
    ⁅(differenceShortRootUnit hij a : GL (Fin (m + m)) R),
        (positiveLongRootTransvectionUnit j b : GL (Fin (m + m)) R)⁆ =
      (positiveSumShortRootUnit hij (a * b) : GL (Fin (m + m)) R) *
        positiveLongRootTransvectionUnit i (a ^ 2 * b)
  rw [coe_differenceShortRootUnit, coe_positiveLongRootTransvectionUnit,
    coe_positiveSumShortRootUnit, coe_positiveLongRootTransvectionUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJI' : J ≠ I' := finSumFinEquiv_inl_ne_inr j i
  have hII' : I ≠ I' := finSumFinEquiv_inl_ne_inr i i
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hJJ' : J ≠ J' := finSumFinEquiv_inl_ne_inr j j
  have hIJ' : I ≠ J' := finSumFinEquiv_inl_ne_inr i j
  have hBC :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hJJ' b⁆ =
        transvectionUnit hJI' (a * b) := by
    rw [commutatorElement_transvectionUnit_reverse hJ'I' hJJ' hJI']
    congr 1
    ring
  have hAC :
      ⁅transvectionUnit hIJ a, transvectionUnit hJJ' b⁆ =
        transvectionUnit hIJ' (a * b) :=
    commutatorElement_transvectionUnit hIJ hJJ' hIJ' a b
  have hAE :
      ⁅transvectionUnit hIJ a, transvectionUnit hJI' (a * b)⁆ =
        transvectionUnit hII' (a ^ 2 * b) := by
    rw [commutatorElement_transvectionUnit hIJ hJI' hII']
    congr 1
    ring
  rw [commutatorElement_mul_left_eq_conj_mul, hBC, hAC]
  calc
    transvectionUnit hIJ a * transvectionUnit hJI' (a * b) *
          (transvectionUnit hIJ a)⁻¹ * transvectionUnit hIJ' (a * b) =
        ⁅transvectionUnit hIJ a, transvectionUnit hJI' (a * b)⁆ *
          transvectionUnit hJI' (a * b) * transvectionUnit hIJ' (a * b) := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    _ = transvectionUnit hII' (a ^ 2 * b) * transvectionUnit hJI' (a * b) *
          transvectionUnit hIJ' (a * b) := by rw [hAE]
    _ = transvectionUnit hIJ' (a * b) * transvectionUnit hJI' (a * b) *
          transvectionUnit hII' (a ^ 2 * b) := by
      rw [(commute_transvectionUnit hII' hJI' (finSumFinEquiv_inr_ne_inl i j)
          (finSumFinEquiv_inr_ne_inl i i) _ _).eq,
        mul_assoc,
        (commute_transvectionUnit hII' hIJ' (finSumFinEquiv_inr_ne_inl i i)
          (finSumFinEquiv_inr_ne_inl j i) _ _).eq,
        ← mul_assoc,
        (commute_transvectionUnit hJI' hIJ' (finSumFinEquiv_inr_ne_inl i i)
          (finSumFinEquiv_inr_ne_inl j j) _ _).eq]

/-- **The structure-constant-two Chevalley relation in the standard symplectic group.** The
commutator of `x_{eᵢ-eⱼ}(a)` and `x_{eᵢ+eⱼ}(b)` is `x_{2eᵢ}(2ab)`. -/
theorem commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit
    (hij : i ≠ j) (a b : R) :
    ⁅differenceShortRootUnit hij a, positiveSumShortRootUnit hij b⁆ =
      positiveLongRootTransvectionUnit i (2 * a * b) := by
  apply Subtype.ext
  -- As above, expose the commutator only at the ambient `GL` level.
  change
    ⁅(differenceShortRootUnit hij a : GL (Fin (m + m)) R),
        (positiveSumShortRootUnit hij b : GL (Fin (m + m)) R)⁆ =
      (positiveLongRootTransvectionUnit i (2 * a * b) : GL (Fin (m + m)) R)
  rw [coe_differenceShortRootUnit, coe_positiveSumShortRootUnit,
    coe_positiveLongRootTransvectionUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hIJ' : I ≠ J' := finSumFinEquiv_inl_ne_inr i j
  have hJI' : J ≠ I' := finSumFinEquiv_inl_ne_inr j i
  have hII' : I ≠ I' := finSumFinEquiv_inl_ne_inr i i
  have hBD :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hIJ' b⁆ =
        transvectionUnit hII' (a * b) := by
    rw [commutatorElement_transvectionUnit_reverse hJ'I' hIJ' hII']
    congr 1
    ring
  have hAE :
      ⁅transvectionUnit hIJ a, transvectionUnit hJI' b⁆ =
        transvectionUnit hII' (a * b) :=
    commutatorElement_transvectionUnit hIJ hJI' hII' a b
  have hBDE :
      ⁅transvectionUnit hJ'I' (-a),
          transvectionUnit hIJ' b * transvectionUnit hJI' b⁆ =
        transvectionUnit hII' (a * b) := by
    rw [commutatorElement_mul_right_eq_mul_conj, hBD,
      (commute_transvectionUnit hJ'I' hJI' (finSumFinEquiv_inr_ne_inl i j)
        hJ'I'.symm _ _).commutator_eq]
    simp only [mul_one, mul_assoc, mul_inv_cancel, mul_one]
  have hADE :
      ⁅transvectionUnit hIJ a,
          transvectionUnit hIJ' b * transvectionUnit hJI' b⁆ =
        transvectionUnit hII' (a * b) := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      (commute_transvectionUnit hIJ hIJ' hIJ.symm hIJ'.symm _ _).commutator_eq,
      one_mul, hAE]
    rw [(commute_transvectionUnit hIJ' hII' (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inr_ne_inl i i) _ _).eq, mul_inv_cancel_right]
  rw [commutatorElement_mul_left_eq_conj_mul, hBDE, hADE]
  rw [(commute_transvectionUnit hIJ hII' hIJ.symm hII'.symm _ _).eq]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [← transvectionUnit_add]
  congr 1
  ring

end TauCeti.GLSymplecticFin
