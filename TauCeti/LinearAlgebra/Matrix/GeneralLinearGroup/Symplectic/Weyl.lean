/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The symplectic root subgroups and their underlying transvection formulas are used below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Weyl elements in the standard symplectic group

For distinct coordinate indices `i` and `j`, this file constructs the standard representative

```text
n_{i,j} = x_{e_i-e_j}(1) x_{e_j-e_i}(-1) x_{e_i-e_j}(1)
```

of the Weyl reflection exchanging `i` and `j`. Conjugation by `n_{i,j}` transports the positive
and negative long-root subgroups at `j` to those at `i`. These identities work over an arbitrary
commutative ring: their parameters are unchanged, so no division or characteristic restriction is
needed.

The conjugation formulas are the long-root transport step in the generation of the standard
type-`C_m` symplectic group by its simple root subgroups. Together with the difference-root
generation and the Chevalley commutator relations, they generate the remaining long and sum root
subgroups. This advances the explicit full-weight type-`C` carrier in Layer 9 of the
`ReductiveGroups` roadmap, consumed by milestone L0 of `CFSGStatement`.

## Main definitions and results

* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement`: the standard representative of the
  reflection in `e_i-e_j`.
* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement_conj_positiveLongRootTransvectionUnit`: it
  transports `x_{2e_j}(c)` to `x_{2e_i}(c)`.
* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement_conj_negativeLongRootTransvectionUnit`:
  the corresponding transport of `x_{-2e_j}(c)`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §3.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u v

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- The standard representative of the Weyl reflection in the short root `e_i-e_j`:
`x_{e_i-e_j}(1) x_{e_j-e_i}(-1) x_{e_i-e_j}(1)`. -/
def differenceShortRootWeylElement (hij : i ≠ j) : GLSymplecticFin m R :=
  differenceShortRootUnit hij 1 * differenceShortRootUnit hij.symm (-1) *
    differenceShortRootUnit hij 1

/-- The short-root Weyl element is the standard three-factor word in the two opposite root
subgroups. -/
theorem differenceShortRootWeylElement_def (hij : i ≠ j) :
    differenceShortRootWeylElement (R := R) hij =
      differenceShortRootUnit hij 1 * differenceShortRootUnit hij.symm (-1) *
        differenceShortRootUnit hij 1 := (rfl)

private theorem coe_differenceShortRootWeylElement (hij : i ≠ j) :
    ((differenceShortRootWeylElement (R := R) hij : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      TauCeti.transvectionWeylElement (differenceShortRoot_first_indices_ne hij) *
        (TauCeti.transvectionWeylElement
          (differenceShortRoot_second_indices_ne hij))⁻¹ := by
  rw [differenceShortRootWeylElement_def, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_differenceShortRootUnit, coe_differenceShortRootUnit (hij := hij.symm),
    TauCeti.transvectionWeylElement_inv, TauCeti.transvectionWeylElement_def]
  simp only [neg_neg]
  let a := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R)
  let b := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R)
  let c := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R)
  let d := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm (1 : R)
  -- Fold the four transvections so that only their three cross-commutations remain visible.
  change (a * c) * (b * d) * (a * c) = (a * b * a) * (c * d * c)
  have hac : Commute a c := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inr_ne_inl i i) 1 (-1)
  have had : Commute a d := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inr_ne_inl j i) 1 1
  have hbc : Commute b c := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr i j) (finSumFinEquiv_inr_ne_inl i j) (-1) (-1)
  calc
    (a * c) * (b * d) * (a * c) = a * (c * b) * d * a * c := by group
    _ = a * (b * c) * d * a * c := by rw [hbc.eq]
    _ = a * b * c * (d * a) * c := by group
    _ = a * b * c * (a * d) * c := by rw [had.eq]
    _ = a * b * (c * a) * d * c := by group
    _ = a * b * (a * c) * d * c := by rw [hac.eq]
    _ = (a * b * a) * (c * d * c) := by group

/-- **A short-root Weyl element transports positive long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{2e_j}(c)` to `x_{2e_i}(c)`, with no change of parameter. -/
theorem differenceShortRootWeylElement_conj_positiveLongRootTransvectionUnit
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * positiveLongRootTransvectionUnit j c *
        (differenceShortRootWeylElement hij)⁻¹ =
      positiveLongRootTransvectionUnit i c := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_positiveLongRootTransvectionUnit, coe_positiveLongRootTransvectionUnit]
  let left := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_first_indices_ne hij)
  let right := (TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_second_indices_ne hij))⁻¹
  -- Fold the two commuting coordinate-block Weyl representatives used by the symplectic word.
  change (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
      (left * right)⁻¹ = TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c
  calc
    (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
          (left * right)⁻¹ =
        left * (right * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
          right⁻¹) * left⁻¹ := by group
    _ = left * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j i) c * left⁻¹ := by
      rw [TauCeti.transvectionWeylElement_inv_conj_transvectionUnit_right
        (differenceShortRoot_second_indices_ne hij)
        (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr j i)]
    _ = TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c := by
      exact TauCeti.transvectionWeylElement_conj_transvectionUnit_left
        (differenceShortRoot_first_indices_ne hij)
        (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inl_ne_inr i i) c

/-- **A short-root Weyl element transports negative long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{-2e_j}(c)` to `x_{-2e_i}(c)`, with no change of parameter. -/
theorem differenceShortRootWeylElement_conj_negativeLongRootTransvectionUnit
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * negativeLongRootTransvectionUnit j c *
        (differenceShortRootWeylElement hij)⁻¹ =
      negativeLongRootTransvectionUnit i c := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_negativeLongRootTransvectionUnit, coe_negativeLongRootTransvectionUnit]
  let left := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_first_indices_ne hij)
  let right := (TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_second_indices_ne hij))⁻¹
  -- Fold the two commuting coordinate-block Weyl representatives used by the symplectic word.
  change (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
      (left * right)⁻¹ = TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c
  calc
    (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
          (left * right)⁻¹ =
        left * (right * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
          right⁻¹) * left⁻¹ := by group
    _ = left * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i j) c * left⁻¹ := by
      rw [TauCeti.transvectionWeylElement_inv_conj_transvectionUnit_left
        (differenceShortRoot_second_indices_ne hij)
        (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl i j)]
    _ = TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c := by
      exact TauCeti.transvectionWeylElement_conj_transvectionUnit_right
        (differenceShortRoot_first_indices_ne hij)
        (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inr_ne_inl i i) c

/-- Applying a ring homomorphism entrywise to a short-root Weyl element gives the corresponding
Weyl element over the target ring. -/
@[simp]
theorem map_differenceShortRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (hij : i ≠ j) :
    GLSymplecticFin.map m R f (differenceShortRootWeylElement hij) =
      differenceShortRootWeylElement hij := by
  simp [differenceShortRootWeylElement]

end TauCeti.GLSymplecticFin
