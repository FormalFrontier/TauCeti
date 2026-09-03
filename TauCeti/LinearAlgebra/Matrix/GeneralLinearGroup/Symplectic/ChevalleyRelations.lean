/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
import TauCeti.GroupTheory.Commutator

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

The opposite-root-string analogues are

```text
⁅x_{eᵢ-eⱼ}(a), x_{-2eᵢ}(b)⁆
  = x_{-eᵢ-eⱼ}(-ab) x_{-2eⱼ}(a²b),
⁅x_{eᵢ-eⱼ}(a), x_{-eᵢ-eⱼ}(b)⁆ = x_{-2eⱼ}(-2ab).
```

The second relation in each root string records its non-unit structure constant; for the
positive string it is

```text
⁅x_{eᵢ-eⱼ}(a), x_{eᵢ+eⱼ}(b)⁆ = x_{2eᵢ}(2ab).
```

Together these four identities are the rank-two relations needed to compare the standard
symplectic realization with the characteristic-two special isogeny of type `B₂/C₂`.

The complementary long-root strings, starting from the sum roots, are

```text
⁅x_{eᵢ+eⱼ}(a), x_{-2eⱼ}(b)⁆
  = x_{eᵢ-eⱼ}(ab) x_{2eᵢ}(-a²b),
⁅x_{-eᵢ-eⱼ}(a), x_{2eⱼ}(b)⁆
  = x_{eⱼ-eᵢ}(-ab) x_{-2eᵢ}(-a²b).
```

Thus every interaction between a long root and a nonopposite short root in the rank-two
subsystem is available without changing coordinates.

The type-`A` subsystem of difference roots also satisfies the structure-constant-one relation

```text
⁅x_{eᵢ-eⱼ}(a), x_{eⱼ-eₖ}(b)⁆ = x_{eᵢ-eₖ}(ab).
```

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2 and §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- **The structure-constant-one Chevalley relation in the difference-root subsystem.** For
pairwise distinct indices, the commutator of `x_{eᵢ-eⱼ}(a)` and `x_{eⱼ-eₖ}(b)` is
`x_{eᵢ-eₖ}(ab)`. -/
theorem commutatorElement_differenceShortRootUnit_differenceShortRootUnit
    {k : Fin m} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅differenceShortRootUnit hij a, differenceShortRootUnit hjk b⁆ =
      differenceShortRootUnit hik (a * b) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement]
  -- Expose the ambient general-linear equality so that the explicit matrix formulas apply.
  change
    ⁅((differenceShortRootUnit hij a : GLSymplecticFin m R) : GL (Fin (m + m)) R),
        ((differenceShortRootUnit hjk b : GLSymplecticFin m R) : GL (Fin (m + m)) R)⁆ =
      ((differenceShortRootUnit hik (a * b) : GLSymplecticFin m R) :
        GL (Fin (m + m)) R)
  rw [coe_differenceShortRootUnit, coe_differenceShortRootUnit,
    coe_differenceShortRootUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let K := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl k)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  let K' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr k)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJK : J ≠ K := differenceShortRoot_first_indices_ne hjk
  have hIK : I ≠ K := differenceShortRoot_first_indices_ne hik
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hK'J' : K' ≠ J' := differenceShortRoot_second_indices_ne hjk
  have hK'I' : K' ≠ I' := differenceShortRoot_second_indices_ne hik
  -- The upper and lower blocks each satisfy the type-A transvection relation.
  have hAC :
      ⁅transvectionUnit hIJ a, transvectionUnit hJK b⁆ =
        transvectionUnit hIK (a * b) :=
    commutatorElement_transvectionUnit hIJ hJK hIK a b
  have hBD :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hK'J' (-b)⁆ =
        transvectionUnit hK'I' (-(a * b)) := by
    rw [commutatorElement_transvectionUnit_reverse hJ'I' hK'J' hK'I']
    congr 1
    ring
  -- All cross-block terms commute, including the two factors in the resulting root element.
  have hBC : Commute (transvectionUnit hJ'I' (-a)) (transvectionUnit hJK b) :=
    commute_transvectionUnit hJ'I' hJK
      (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inl_ne_inr k j) _ _
  have hAD : Commute (transvectionUnit hIJ a) (transvectionUnit hK'J' (-b)) :=
    commute_transvectionUnit hIJ hK'J'
      (finSumFinEquiv_inl_ne_inr j k) (finSumFinEquiv_inr_ne_inl j i) _ _
  have hCQ : Commute (transvectionUnit hJK b) (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hJK hK'I'
      (finSumFinEquiv_inl_ne_inr k k) (finSumFinEquiv_inr_ne_inl i j) _ _
  have hAQ : Commute (transvectionUnit hIJ a) (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hIJ hK'I'
      (finSumFinEquiv_inl_ne_inr j k) (finSumFinEquiv_inr_ne_inl i i) _ _
  have hPQ : Commute (transvectionUnit hIK (a * b))
      (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hIK hK'I'
      (finSumFinEquiv_inl_ne_inr k k) (finSumFinEquiv_inr_ne_inl i i) _ _
  rw [TauCeti.commutatorElement_mul_mul_eq_mul_of_commute hBC hAD
    (by simpa only [hBD] using hCQ) (by simpa only [hBD] using hAQ)
    (by simpa only [hAC, hBD] using hPQ), hAC, hBD]

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

/-- **The negative multiply-laced Chevalley relation in the standard symplectic group.** The
commutator of `x_{eᵢ-eⱼ}(a)` and `x_{-2eᵢ}(b)` is the product of the two remaining root
subgroups in their root string, with parameters `-ab` and `a²b`. -/
theorem commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
    ⁅differenceShortRootUnit hij a, negativeLongRootTransvectionUnit i b⁆ =
      negativeSumShortRootUnit hij (-(a * b)) *
        negativeLongRootTransvectionUnit j (a ^ 2 * b) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement, map_mul, Subgroup.coe_subtype,
    coe_differenceShortRootUnit, coe_negativeLongRootTransvectionUnit,
    coe_negativeSumShortRootUnit, coe_negativeLongRootTransvectionUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hI'I : I' ≠ I := finSumFinEquiv_inr_ne_inl i i
  have hI'J : I' ≠ J := finSumFinEquiv_inr_ne_inl i j
  have hJ'I : J' ≠ I := finSumFinEquiv_inr_ne_inl j i
  have hJ'J : J' ≠ J := finSumFinEquiv_inr_ne_inl j j
  have hBC :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hI'I b⁆ =
        transvectionUnit hJ'I (-(a * b)) := by
    rw [commutatorElement_transvectionUnit hJ'I' hI'I hJ'I]
    congr 1
    ring
  have hAC :
      ⁅transvectionUnit hIJ a, transvectionUnit hI'I b⁆ =
        transvectionUnit hI'J (-(a * b)) := by
    rw [commutatorElement_transvectionUnit_reverse hIJ hI'I hI'J]
    congr 1
    ring
  have hAE :
      ⁅transvectionUnit hIJ a, transvectionUnit hJ'I (-(a * b))⁆ =
        transvectionUnit hJ'J (a ^ 2 * b) := by
    rw [commutatorElement_transvectionUnit_reverse hIJ hJ'I hJ'J]
    congr 1
    ring
  rw [commutatorElement_mul_left_eq_conj_mul, hBC, hAC]
  calc
    transvectionUnit hIJ a * transvectionUnit hJ'I (-(a * b)) *
          (transvectionUnit hIJ a)⁻¹ * transvectionUnit hI'J (-(a * b)) =
        ⁅transvectionUnit hIJ a, transvectionUnit hJ'I (-(a * b))⁆ *
          transvectionUnit hJ'I (-(a * b)) * transvectionUnit hI'J (-(a * b)) := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    _ = transvectionUnit hJ'J (a ^ 2 * b) * transvectionUnit hJ'I (-(a * b)) *
          transvectionUnit hI'J (-(a * b)) := by rw [hAE]
    _ = transvectionUnit hI'J (-(a * b)) * transvectionUnit hJ'I (-(a * b)) *
          transvectionUnit hJ'J (a ^ 2 * b) := by
      rw [(commute_transvectionUnit hJ'J hJ'I hJ'J.symm hJ'I.symm _ _).eq,
        mul_assoc,
        (commute_transvectionUnit hJ'J hI'J hI'J.symm hJ'J.symm _ _).eq,
        ← mul_assoc,
        (commute_transvectionUnit hJ'I hI'J hI'I.symm hJ'J.symm _ _).eq]

/-- **The negative structure-constant-two Chevalley relation in the standard symplectic
group.** The commutator of `x_{eᵢ-eⱼ}(a)` and `x_{-eᵢ-eⱼ}(b)` is `x_{-2eⱼ}(-2ab)`. -/
theorem commutatorElement_differenceShortRootUnit_negativeSumShortRootUnit
    (hij : i ≠ j) (a b : R) :
    ⁅differenceShortRootUnit hij a, negativeSumShortRootUnit hij b⁆ =
      negativeLongRootTransvectionUnit j (-(2 * a * b)) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement, Subgroup.coe_subtype, coe_differenceShortRootUnit,
    coe_negativeSumShortRootUnit, coe_negativeLongRootTransvectionUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hI'J : I' ≠ J := finSumFinEquiv_inr_ne_inl i j
  have hJ'I : J' ≠ I := finSumFinEquiv_inr_ne_inl j i
  have hJ'J : J' ≠ J := finSumFinEquiv_inr_ne_inl j j
  have hBC :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hI'J b⁆ =
        transvectionUnit hJ'J (-(a * b)) := by
    rw [commutatorElement_transvectionUnit hJ'I' hI'J hJ'J]
    congr 1
    ring
  have hAD :
      ⁅transvectionUnit hIJ a, transvectionUnit hJ'I b⁆ =
        transvectionUnit hJ'J (-(a * b)) := by
    rw [commutatorElement_transvectionUnit_reverse hIJ hJ'I hJ'J]
    congr 1
    ring
  have hBCD :
      ⁅transvectionUnit hJ'I' (-a),
          transvectionUnit hI'J b * transvectionUnit hJ'I b⁆ =
        transvectionUnit hJ'J (-(a * b)) := by
    rw [commutatorElement_mul_right_eq_mul_conj, hBC,
      (commute_transvectionUnit hJ'I' hJ'I hJ'I'.symm hJ'I.symm _ _).commutator_eq]
    simp only [mul_one, mul_assoc, mul_inv_cancel, mul_one]
  have hACD :
      ⁅transvectionUnit hIJ a,
          transvectionUnit hI'J b * transvectionUnit hJ'I b⁆ =
        transvectionUnit hJ'J (-(a * b)) := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      (commute_transvectionUnit hIJ hI'J hI'J.symm hIJ.symm _ _).commutator_eq,
      one_mul, hAD]
    rw [(commute_transvectionUnit hI'J hJ'J hJ'J.symm hI'J.symm _ _).eq,
      mul_inv_cancel_right]
  rw [commutatorElement_mul_left_eq_conj_mul, hBCD, hACD]
  rw [(commute_transvectionUnit hIJ hJ'J hJ'J.symm hIJ.symm _ _).eq]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [← transvectionUnit_add]
  congr 1
  ring

private theorem commutatorElement_transvectionUnit_pair_chain
    {n : Type*} [Fintype n] [DecidableEq n] {p q r t : n}
    (hpr : p ≠ r) (hqt : q ≠ t) (hrq : r ≠ q) (hrt : r ≠ t) (hpq : p ≠ q)
    (hpt : p ≠ t) (a b : R) :
    ⁅transvectionUnit hpr a * transvectionUnit hqt a, transvectionUnit hrq b⁆ =
      transvectionUnit hpq (a * b) * transvectionUnit hrt (-(a * b)) *
        transvectionUnit hpt (-(a ^ 2 * b)) := by
  have hBC :
      ⁅transvectionUnit hqt a, transvectionUnit hrq b⁆ =
        transvectionUnit hrt (-(a * b)) := by
    rw [commutatorElement_transvectionUnit_reverse hqt hrq hrt]
    congr 1
    ring
  have hAC :
      ⁅transvectionUnit hpr a, transvectionUnit hrq b⁆ =
        transvectionUnit hpq (a * b) :=
    commutatorElement_transvectionUnit hpr hrq hpq a b
  have hAE :
      ⁅transvectionUnit hpr a, transvectionUnit hrt (-(a * b))⁆ =
        transvectionUnit hpt (-(a ^ 2 * b)) := by
    rw [commutatorElement_transvectionUnit hpr hrt hpt]
    congr 1
    ring
  rw [commutatorElement_mul_left_eq_conj_mul, hBC, hAC]
  calc
    transvectionUnit hpr a * transvectionUnit hrt (-(a * b)) *
          (transvectionUnit hpr a)⁻¹ * transvectionUnit hpq (a * b) =
        ⁅transvectionUnit hpr a, transvectionUnit hrt (-(a * b))⁆ *
          transvectionUnit hrt (-(a * b)) * transvectionUnit hpq (a * b) := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    _ = transvectionUnit hpt (-(a ^ 2 * b)) * transvectionUnit hrt (-(a * b)) *
          transvectionUnit hpq (a * b) := by
      rw [hAE]
    _ = transvectionUnit hpq (a * b) * transvectionUnit hrt (-(a * b)) *
          transvectionUnit hpt (-(a ^ 2 * b)) := by
      rw [(commute_transvectionUnit hpt hrt hrt.symm hpt.symm _ _).eq, mul_assoc,
        (commute_transvectionUnit hpt hpq hpt.symm hpq.symm _ _).eq, ← mul_assoc,
        (commute_transvectionUnit hrt hpq hpt.symm hrq.symm _ _).eq]

/-- **The complementary positive-sum multiply-laced Chevalley relation.** The commutator of
`x_{eᵢ+eⱼ}(a)` and `x_{-2eⱼ}(b)` is the product of the root subgroups for `eᵢ-eⱼ`
and `2eᵢ`, with parameters `ab` and `-a²b`. -/
theorem commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
    ⁅positiveSumShortRootUnit hij a, negativeLongRootTransvectionUnit j b⁆ =
      differenceShortRootUnit hij (a * b) *
        positiveLongRootTransvectionUnit i (-(a ^ 2 * b)) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement, map_mul, Subgroup.coe_subtype,
    coe_positiveSumShortRootUnit, coe_negativeLongRootTransvectionUnit,
    coe_differenceShortRootUnit, coe_positiveLongRootTransvectionUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hIJ' : I ≠ J' := finSumFinEquiv_inl_ne_inr i j
  have hJI' : J ≠ I' := finSumFinEquiv_inl_ne_inr j i
  have hJ'J : J' ≠ J := finSumFinEquiv_inr_ne_inl j j
  have hII' : I ≠ I' := finSumFinEquiv_inl_ne_inr i i
  exact commutatorElement_transvectionUnit_pair_chain hIJ' hJI' hJ'J hJ'I' hIJ hII' a b

/-- **The complementary negative-sum multiply-laced Chevalley relation.** The commutator of
`x_{-eᵢ-eⱼ}(a)` and `x_{2eⱼ}(b)` is the product of the root subgroups for `eⱼ-eᵢ`
and `-2eᵢ`, both with the signs forced by the chosen parametrizations. -/
theorem commutatorElement_negativeSumShortRootUnit_positiveLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
    ⁅negativeSumShortRootUnit hij a, positiveLongRootTransvectionUnit j b⁆ =
      differenceShortRootUnit hij.symm (-(a * b)) *
        negativeLongRootTransvectionUnit i (-(a ^ 2 * b)) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement, map_mul, Subgroup.coe_subtype,
    coe_negativeSumShortRootUnit, coe_positiveLongRootTransvectionUnit,
    coe_differenceShortRootUnit, coe_negativeLongRootTransvectionUnit]
  simp only [neg_neg]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  have hJI : J ≠ I := differenceShortRoot_first_indices_ne hij.symm
  have hI'J' : I' ≠ J' := differenceShortRoot_second_indices_ne hij.symm
  have hI'J : I' ≠ J := finSumFinEquiv_inr_ne_inl i j
  have hJ'I : J' ≠ I := finSumFinEquiv_inr_ne_inl j i
  have hJJ' : J ≠ J' := finSumFinEquiv_inl_ne_inr j j
  have hI'I : I' ≠ I := finSumFinEquiv_inr_ne_inl i i
  rw [commutatorElement_transvectionUnit_pair_chain hI'J hJ'I hJJ' hJI hI'J' hI'I]
  rw [(commute_transvectionUnit hJI hI'J' hI'I.symm hJJ'.symm (-(a * b)) (a * b)).eq]

end TauCeti.GLSymplecticFin
