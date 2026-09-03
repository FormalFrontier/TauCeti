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
* `differenceShortRootWeylElement_mem`: a subgroup containing the two difference-root elements
  forming a Weyl word contains the corresponding Weyl representative.
* `coe_differenceShortRootWeylElement`: in sum coordinates it is a product of two type-`A` Weyl
  representatives.
* `differenceShortRootWeylElement_inv`: the representative for the opposite root is its inverse.
* `differenceShortRootWeylElement_mul_differenceShortRootUnit_mul_inv`: its reflection action on
  the short-root subgroup.
* `differenceShortRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv`: it
  transports `x_{2e_j}(c)` to `x_{2e_i}(c)`.
* `differenceShortRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv`:
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

/-- A subgroup containing the two difference-root elements forming a Weyl word contains the
corresponding Weyl reflection representative. -/
theorem differenceShortRootWeylElement_mem (H : Subgroup (GLSymplecticFin m R))
    (hij : i ≠ j) (hforward : differenceShortRootUnit hij 1 ∈ H)
    (hbackward : differenceShortRootUnit hij.symm (-1) ∈ H) :
    differenceShortRootWeylElement hij ∈ H := by
  rw [differenceShortRootWeylElement]
  exact H.mul_mem (H.mul_mem hforward hbackward) hforward

/-- In sum coordinates the short-root Weyl representative is the product of the type-`A` Weyl
representative on the first block and the inverse of the one on the second block. -/
@[simp]
theorem coe_differenceShortRootWeylElement (hij : i ≠ j) :
    ((differenceShortRootWeylElement (R := R) hij : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      TauCeti.transvectionWeylElement (differenceShortRoot_first_indices_ne hij) *
        (TauCeti.transvectionWeylElement
          (differenceShortRoot_second_indices_ne hij))⁻¹ := by
  -- The inverse of the second block's Weyl word is that word with opposite parameters.
  have hinv : (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_second_indices_ne hij))⁻¹ =
        TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1) *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm 1 *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1) := by
    simp [TauCeti.transvectionWeylElement_def, _root_.mul_inv_rev, mul_assoc]
  rw [differenceShortRootWeylElement, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_differenceShortRootUnit, coe_differenceShortRootUnit (hij := hij.symm),
    hinv, TauCeti.transvectionWeylElement_def]
  simp only [neg_neg]
  let a := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R)
  let b := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R)
  let c := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R)
  let d := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm (1 : R)
  -- Fold the four transvections so that only their three cross-commutations remain visible;
  -- the `Ne` proof arguments for `hij.symm` are identified here by proof irrelevance.
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

private theorem commute_differenceShortRootWeylElements (hij : i ≠ j) : Commute
    (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_first_indices_ne hij))
    (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_second_indices_ne hij)) := by
  have houter : Commute
      (TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij)) :=
    TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij)
      (differenceShortRoot_first_indices_ne hij)
      (finSumFinEquiv_inr_ne_inl i i) (finSumFinEquiv_inl_ne_inr j j)
      (finSumFinEquiv_inr_ne_inl j i) (finSumFinEquiv_inl_ne_inr j i) 1
  have hmiddle : Commute
      (TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij)) :=
    TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij)
      (differenceShortRoot_first_indices_ne hij).symm
      (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inl_ne_inr i j)
      (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inl_ne_inr i i) (-1)
  rw [TauCeti.transvectionWeylElement_def]
  exact (houter.mul_left hmiddle).mul_left houter

/-- The inverse of the Weyl representative for `e_i-e_j` is the representative for the
opposite root `e_j-e_i`. -/
@[simp]
theorem differenceShortRootWeylElement_inv (hij : i ≠ j) :
    (differenceShortRootWeylElement (R := R) hij)⁻¹ =
      differenceShortRootWeylElement hij.symm := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_differenceShortRootWeylElement (R := R) hij.symm]
  rw [← TauCeti.transvectionWeylElement_inv
    (differenceShortRoot_first_indices_ne hij),
    TauCeti.transvectionWeylElement_inv
      (differenceShortRoot_second_indices_ne hij.symm)]
  rw [_root_.mul_inv_rev, inv_inv]
  exact (commute_differenceShortRootWeylElements (R := R) hij).inv_left.eq.symm

/-- Conjugation by the Weyl representative for `e_i-e_j` sends its short-root subgroup to
the opposite short-root subgroup and negates the parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_differenceShortRootUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * differenceShortRootUnit hij c *
        differenceShortRootWeylElement hij.symm =
      differenceShortRootUnit hij.symm (-c) := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_differenceShortRootUnit, coe_differenceShortRootUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  simp only [neg_neg]
  set left := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_first_indices_ne hij)
  set right := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_second_indices_ne hij).symm
  set x := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) c
  set y := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-c)
  set u := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-c)
  set v := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm c
  have hleft : left * x * left⁻¹ = u :=
    by simpa only [left, x, u, TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_self
        (differenceShortRoot_first_indices_ne hij) c
  have hright : right * y * right⁻¹ = v :=
    by simpa only [right, y, v, TauCeti.transvectionWeylElement_inv, neg_neg] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_symm
        (differenceShortRoot_second_indices_ne hij).symm (-c)
  have hright_x : Commute right x :=
    (TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij).symm
      (differenceShortRoot_first_indices_ne hij)
      (finSumFinEquiv_inr_ne_inl j i) (finSumFinEquiv_inl_ne_inr j i)
      (finSumFinEquiv_inr_ne_inl i i) (finSumFinEquiv_inl_ne_inr j j) c).symm
  have hleft_v : Commute left v :=
    (TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_first_indices_ne hij)
      (differenceShortRoot_second_indices_ne hij).symm
      (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inl_ne_inr i i) (finSumFinEquiv_inr_ne_inl j j) c).symm
  calc
    (left * right) * (x * y) * (left * right)⁻¹ =
        left * (right * x * right⁻¹) * (right * y * right⁻¹) * left⁻¹ := by group
    _ = left * (x * v) * left⁻¹ := by
      rw [hright_x.mul_inv_cancel, hright]
      simp only [mul_assoc]
    _ = (left * x * left⁻¹) * (left * v * left⁻¹) := by group
    _ = u * v := by rw [hleft, hleft_v.mul_inv_cancel]

private theorem conjugate_crossBlockTransvectionByWeylPair
    {pi pj qi qj : Fin (m + m)} (hpij : pi ≠ pj) (hqij : qi ≠ qj)
    (hpjqj : pj ≠ qj) (hpjqi : pj ≠ qi) (hpiqi : pi ≠ qi) (c : R) :
    (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij) *
        TauCeti.transvectionUnit hpjqj c *
        (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij)⁻¹ =
      TauCeti.transvectionUnit hpiqi c := by
  have hright :
      TauCeti.transvectionWeylElement hqij * TauCeti.transvectionUnit hpjqj c *
          (TauCeti.transvectionWeylElement hqij)⁻¹ =
        TauCeti.transvectionUnit hpjqi c := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_right
        hqij hpjqj hpjqi c
  have hleft :
      TauCeti.transvectionWeylElement hpij * TauCeti.transvectionUnit hpjqi c *
          (TauCeti.transvectionWeylElement hpij)⁻¹ =
        TauCeti.transvectionUnit hpiqi c := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_left
        hpij hpjqi hpiqi c
  calc
    (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij) *
          TauCeti.transvectionUnit hpjqj c *
          (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij)⁻¹ =
        TauCeti.transvectionWeylElement hpij *
          (TauCeti.transvectionWeylElement hqij * TauCeti.transvectionUnit hpjqj c *
            (TauCeti.transvectionWeylElement hqij)⁻¹) *
          (TauCeti.transvectionWeylElement hpij)⁻¹ := by group
    _ = TauCeti.transvectionUnit hpiqi c := by rw [hright, hleft]

/-- **A short-root Weyl element transports positive long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{2e_j}(c)` to `x_{2e_i}(c)`, with no change of parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * positiveLongRootTransvectionUnit j c *
        differenceShortRootWeylElement hij.symm =
      positiveLongRootTransvectionUnit i c := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_positiveLongRootTransvectionUnit, coe_positiveLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  exact conjugate_crossBlockTransvectionByWeylPair
    (differenceShortRoot_first_indices_ne hij)
    (differenceShortRoot_second_indices_ne hij).symm
    (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr j i)
    (finSumFinEquiv_inl_ne_inr i i) c

/-- **A short-root Weyl element transports negative long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{-2e_j}(c)` to `x_{-2e_i}(c)`, with no change of parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * negativeLongRootTransvectionUnit j c *
        differenceShortRootWeylElement hij.symm =
      negativeLongRootTransvectionUnit i c := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_negativeLongRootTransvectionUnit, coe_negativeLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  have hcomm : Commute
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_first_indices_ne hij))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij).symm) := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      (commute_differenceShortRootWeylElements (R := R) hij).inv_right
  rw [hcomm.eq]
  exact conjugate_crossBlockTransvectionByWeylPair
    (differenceShortRoot_second_indices_ne hij).symm
    (differenceShortRoot_first_indices_ne hij)
    (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl j i)
    (finSumFinEquiv_inr_ne_inl i i) c

/-- Applying a ring homomorphism entrywise to a short-root Weyl element gives the corresponding
Weyl element over the target ring. -/
@[simp]
theorem map_differenceShortRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (hij : i ≠ j) :
    GLSymplecticFin.map m R f (differenceShortRootWeylElement hij) =
      differenceShortRootWeylElement hij := by
  simp [differenceShortRootWeylElement]

end TauCeti.GLSymplecticFin
