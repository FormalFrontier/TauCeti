/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations

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
* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement_mul_positiveLongRoot_mul_inv`: it
  transports `x_{2e_j}(c)` to `x_{2e_i}(c)`.
* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement_mul_negativeLongRoot_mul_inv`: the
  corresponding transport of `x_{-2e_j}(c)`.

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

private def transvectionWeylElement {n : Type*} [Fintype n] [DecidableEq n]
    {a b : n} (hab : a ≠ b) : GL n R :=
  TauCeti.transvectionUnit hab 1 * TauCeti.transvectionUnit hab.symm (-1) *
    TauCeti.transvectionUnit hab 1

private theorem transvectionWeylElement_conj_outgoing {n : Type*}
    [Fintype n] [DecidableEq n] {a b k : n} (hab : a ≠ b) (hbk : b ≠ k)
    (hak : a ≠ k) (c : R) :
    transvectionWeylElement hab * TauCeti.transvectionUnit hbk c *
        (transvectionWeylElement hab)⁻¹ =
      TauCeti.transvectionUnit hak c := by
  let x := TauCeti.transvectionUnit hab (1 : R)
  let y := TauCeti.transvectionUnit hab.symm (-1 : R)
  let z := TauCeti.transvectionUnit hbk c
  let t := TauCeti.transvectionUnit hak c
  have hxz : MulAut.conj x z = t * z := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit hab hbk hak]
    simp only [one_mul, z, t]
  have hyt : MulAut.conj y t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit hab.symm hak hbk]
    simp only [neg_one_mul, TauCeti.transvectionUnit_inv, z, t]
  have hyz : Commute y z :=
    TauCeti.commute_transvectionUnit hab.symm hbk hab hbk.symm (-1) c
  have hxt : Commute x t :=
    TauCeti.commute_transvectionUnit hab hak hab.symm hak.symm 1 c
  have htz : Commute t z :=
    TauCeti.commute_transvectionUnit hak hbk hbk.symm hak.symm c c
  change (x * y * x) * z * (x * y * x)⁻¹ = t
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * (t * z) * y⁻¹) * x⁻¹ := by
      rw [← MulAut.conj_apply x z, hxz]
    _ = x * ((y * t * y⁻¹) * (y * z * y⁻¹)) * x⁻¹ := by group
    _ = x * ((z⁻¹ * t) * z) * x⁻¹ := by
      rw [← MulAut.conj_apply y t, hyt, hyz.mul_inv_cancel]
    _ = x * t * x⁻¹ := by rw [htz.symm.inv_mul_cancel]
    _ = t := hxt.mul_inv_cancel

private theorem transvectionWeylElement_conj_incoming {n : Type*}
    [Fintype n] [DecidableEq n] {a b k : n} (hab : a ≠ b) (hkb : k ≠ b)
    (hka : k ≠ a) (c : R) :
    transvectionWeylElement hab * TauCeti.transvectionUnit hkb c *
        (transvectionWeylElement hab)⁻¹ =
      TauCeti.transvectionUnit hka c := by
  let x := TauCeti.transvectionUnit hab (1 : R)
  let y := TauCeti.transvectionUnit hab.symm (-1 : R)
  let z := TauCeti.transvectionUnit hkb c
  let t := TauCeti.transvectionUnit hka c
  have hxz : Commute x z :=
    TauCeti.commute_transvectionUnit hab hkb hkb.symm hab.symm 1 c
  have hyz : MulAut.conj y z = t * z := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit_reverse hab.symm hkb hka]
    simp only [mul_neg, mul_one, neg_neg, z, t]
  have hxt : MulAut.conj x t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit_reverse hab hka hkb]
    simp only [mul_one, TauCeti.transvectionUnit_inv, z, t]
  have htz : Commute t z :=
    TauCeti.commute_transvectionUnit hka hkb hka.symm hkb.symm c c
  change (x * y * x) * z * (x * y * x)⁻¹ = t
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * z * y⁻¹) * x⁻¹ := by rw [hxz.mul_inv_cancel]
    _ = x * (t * z) * x⁻¹ := by rw [← MulAut.conj_apply y z, hyz]
    _ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
    _ = (z⁻¹ * t) * z := by rw [← MulAut.conj_apply x t, hxt, hxz.mul_inv_cancel]
    _ = t := htz.symm.inv_mul_cancel

private theorem reverseTransvectionWeylElement_conj_incoming {n : Type*}
    [Fintype n] [DecidableEq n] {a b k : n} (hab : a ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) (c : R) :
    (TauCeti.transvectionUnit hab (-1) * TauCeti.transvectionUnit hab.symm 1 *
          TauCeti.transvectionUnit hab (-1)) *
        TauCeti.transvectionUnit hka c *
        (TauCeti.transvectionUnit hab (-1) * TauCeti.transvectionUnit hab.symm 1 *
          TauCeti.transvectionUnit hab (-1))⁻¹ =
      TauCeti.transvectionUnit hkb c := by
  let x := TauCeti.transvectionUnit hab (-1 : R)
  let y := TauCeti.transvectionUnit hab.symm (1 : R)
  let z := TauCeti.transvectionUnit hka c
  let t := TauCeti.transvectionUnit hkb c
  have hxz : MulAut.conj x z = t * z := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit_reverse hab hka hkb]
    simp only [mul_neg, mul_one, neg_neg, z, t]
  have hyt : MulAut.conj y t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit_reverse hab.symm hkb hka]
    simp only [mul_one, TauCeti.transvectionUnit_inv, z, t]
  have hyz : Commute y z :=
    TauCeti.commute_transvectionUnit hab.symm hka hka.symm hab 1 c
  have hxt : Commute x t :=
    TauCeti.commute_transvectionUnit hab hkb hkb.symm hab.symm (-1) c
  have htz : Commute t z :=
    TauCeti.commute_transvectionUnit hkb hka hkb.symm hka.symm c c
  change (x * y * x) * z * (x * y * x)⁻¹ = t
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * (t * z) * y⁻¹) * x⁻¹ := by
      rw [← MulAut.conj_apply x z, hxz]
    _ = x * ((y * t * y⁻¹) * (y * z * y⁻¹)) * x⁻¹ := by group
    _ = x * ((z⁻¹ * t) * z) * x⁻¹ := by
      rw [← MulAut.conj_apply y t, hyt, hyz.mul_inv_cancel]
    _ = x * t * x⁻¹ := by rw [htz.symm.inv_mul_cancel]
    _ = t := hxt.mul_inv_cancel

private theorem reverseTransvectionWeylElement_conj_outgoing {n : Type*}
    [Fintype n] [DecidableEq n] {a b k : n} (hab : a ≠ b) (hak : a ≠ k)
    (hbk : b ≠ k) (c : R) :
    (TauCeti.transvectionUnit hab (-1) * TauCeti.transvectionUnit hab.symm 1 *
          TauCeti.transvectionUnit hab (-1)) *
        TauCeti.transvectionUnit hak c *
        (TauCeti.transvectionUnit hab (-1) * TauCeti.transvectionUnit hab.symm 1 *
          TauCeti.transvectionUnit hab (-1))⁻¹ =
      TauCeti.transvectionUnit hbk c := by
  let x := TauCeti.transvectionUnit hab (-1 : R)
  let y := TauCeti.transvectionUnit hab.symm (1 : R)
  let z := TauCeti.transvectionUnit hak c
  let t := TauCeti.transvectionUnit hbk c
  have hxz : Commute x z :=
    TauCeti.commute_transvectionUnit hab hak hab.symm hak.symm (-1) c
  have hyz : MulAut.conj y z = t * z := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit hab.symm hak hbk]
    simp only [one_mul, z, t]
  have hxt : MulAut.conj x t = z⁻¹ * t := by
    rw [conj_eq_commutatorElement_mul,
      TauCeti.commutatorElement_transvectionUnit hab hbk hak]
    simp only [neg_one_mul, TauCeti.transvectionUnit_inv, z, t]
  have htz : Commute t z :=
    TauCeti.commute_transvectionUnit hbk hak hak.symm hbk.symm c c
  change (x * y * x) * z * (x * y * x)⁻¹ = t
  calc
    (x * y * x) * z * (x * y * x)⁻¹ =
        x * (y * (x * z * x⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * z * y⁻¹) * x⁻¹ := by rw [hxz.mul_inv_cancel]
    _ = x * (t * z) * x⁻¹ := by rw [← MulAut.conj_apply y z, hyz]
    _ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
    _ = (z⁻¹ * t) * z := by rw [← MulAut.conj_apply x t, hxt, hxz.mul_inv_cancel]
    _ = t := htz.symm.inv_mul_cancel

private theorem interleaved_triples_eq {G : Type*} [Group G] {a b c d : G}
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) :
    (a * c) * (b * d) * (a * c) = (a * b * a) * (c * d * c) := by
  calc
    (a * c) * (b * d) * (a * c) = a * (c * b) * d * a * c := by group
    _ = a * (b * c) * d * a * c := by rw [hbc.eq]
    _ = a * b * c * (d * a) * c := by group
    _ = a * b * c * (a * d) * c := by rw [had.eq]
    _ = a * b * (c * a) * d * c := by group
    _ = a * b * (a * c) * d * c := by rw [hac.eq]
    _ = (a * b * a) * (c * d * c) := by group

private theorem coe_differenceShortRootWeylElement (hij : i ≠ j) :
    ((differenceShortRootWeylElement (R := R) hij : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      transvectionWeylElement (differenceShortRoot_first_indices_ne hij) *
        (TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1) *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm 1 *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1)) := by
  rw [differenceShortRootWeylElement]
  change
    (((differenceShortRootUnit hij 1 : GLSymplecticFin m R) : GL (Fin (m + m)) R) *
        ((differenceShortRootUnit hij.symm (-1) : GLSymplecticFin m R) :
          GL (Fin (m + m)) R)) *
        ((differenceShortRootUnit hij 1 : GLSymplecticFin m R) : GL (Fin (m + m)) R) = _
  rw [coe_differenceShortRootUnit]
  rw [coe_differenceShortRootUnit (hij := hij.symm)]
  simp only [neg_neg, transvectionWeylElement]
  let a := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R)
  let b := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R)
  let c := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R)
  let d := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm (1 : R)
  change (a * c) * (b * d) * (a * c) = (a * b * a) * (c * d * c)
  apply interleaved_triples_eq
  · exact TauCeti.commute_transvectionUnit _ _
      (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inr_ne_inl i i) 1 (-1)
  · exact TauCeti.commute_transvectionUnit _ _
      (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inr_ne_inl j i) 1 1
  · exact TauCeti.commute_transvectionUnit _ _
      (finSumFinEquiv_inl_ne_inr i j) (finSumFinEquiv_inr_ne_inl i j) (-1) (-1)

/-- **A short-root Weyl element transports positive long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{2e_j}(c)` to `x_{2e_i}(c)`, with no change of parameter. -/
theorem differenceShortRootWeylElement_mul_positiveLongRoot_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * positiveLongRootTransvectionUnit j c *
        (differenceShortRootWeylElement hij)⁻¹ =
      positiveLongRootTransvectionUnit i c := by
  apply (GLSymplecticFin m R).subtype_injective
  change
    ((differenceShortRootWeylElement hij : GLSymplecticFin m R) : GL (Fin (m + m)) R) *
          ((positiveLongRootTransvectionUnit j c : GLSymplecticFin m R) :
            GL (Fin (m + m)) R) *
        (((differenceShortRootWeylElement hij : GLSymplecticFin m R) :
          GL (Fin (m + m)) R))⁻¹ =
      ((positiveLongRootTransvectionUnit i c : GLSymplecticFin m R) :
        GL (Fin (m + m)) R)
  rw [coe_differenceShortRootWeylElement (R := R) hij,
    coe_positiveLongRootTransvectionUnit, coe_positiveLongRootTransvectionUnit]
  let left := transvectionWeylElement (R := R) (differenceShortRoot_first_indices_ne hij)
  let right :=
    TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R) *
      TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm 1 *
      TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1)
  change (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
      (left * right)⁻¹ = TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c
  calc
    (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
          (left * right)⁻¹ =
        left * (right * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j j) c *
          right⁻¹) * left⁻¹ := by group
    _ = left * TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr j i) c * left⁻¹ := by
      rw [reverseTransvectionWeylElement_conj_incoming
        (differenceShortRoot_second_indices_ne hij)
        (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr j i)]
    _ = TauCeti.transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c := by
      exact transvectionWeylElement_conj_outgoing
        (differenceShortRoot_first_indices_ne hij)
        (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inl_ne_inr i i) c

/-- **A short-root Weyl element transports negative long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{-2e_j}(c)` to `x_{-2e_i}(c)`, with no change of parameter. -/
theorem differenceShortRootWeylElement_mul_negativeLongRoot_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * negativeLongRootTransvectionUnit j c *
        (differenceShortRootWeylElement hij)⁻¹ =
      negativeLongRootTransvectionUnit i c := by
  apply (GLSymplecticFin m R).subtype_injective
  change
    ((differenceShortRootWeylElement hij : GLSymplecticFin m R) : GL (Fin (m + m)) R) *
          ((negativeLongRootTransvectionUnit j c : GLSymplecticFin m R) :
            GL (Fin (m + m)) R) *
        (((differenceShortRootWeylElement hij : GLSymplecticFin m R) :
          GL (Fin (m + m)) R))⁻¹ =
      ((negativeLongRootTransvectionUnit i c : GLSymplecticFin m R) :
        GL (Fin (m + m)) R)
  rw [coe_differenceShortRootWeylElement (R := R) hij,
    coe_negativeLongRootTransvectionUnit, coe_negativeLongRootTransvectionUnit]
  let left := transvectionWeylElement (R := R) (differenceShortRoot_first_indices_ne hij)
  let right :=
    TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R) *
      TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm 1 *
      TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1)
  change (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
      (left * right)⁻¹ = TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c
  calc
    (left * right) * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
          (left * right)⁻¹ =
        left * (right * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl j j) c *
          right⁻¹) * left⁻¹ := by group
    _ = left * TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i j) c * left⁻¹ := by
      rw [reverseTransvectionWeylElement_conj_outgoing
        (differenceShortRoot_second_indices_ne hij)
        (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl i j)]
    _ = TauCeti.transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c := by
      exact transvectionWeylElement_conj_incoming
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
