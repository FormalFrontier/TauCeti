/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Group.End
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# Unipotent linear automorphisms

A linear automorphism is unipotent when its underlying endomorphism minus the identity is
nilpotent. This file records the elementary group-theoretic closure properties needed to use
unipotent elements in algebraic groups: inverses, products of commuting elements, powers, and
conjugates are unipotent.

It also records the rank-one rigidity statement: over a reduced base, a unipotent automorphism
of a free rank-one module is the identity.

Products require commutativity. Indeed, writing `g = 1 + x` and `h = 1 + y`, their product is
`1 + (x + y + xy)`; when `g` and `h` commute, the three displayed nilpotent endomorphisms commute.

## Main declarations

* `TauCeti.GeneralLinearGroup.IsUnipotent`: a linear automorphism is unipotent when its
  difference from the identity is nilpotent.
* `TauCeti.GeneralLinearGroup.isUnipotent_def`: the defining nilpotence criterion.
* `TauCeti.GeneralLinearGroup.isUnipotent_one`: the identity automorphism is unipotent.
* `TauCeti.GeneralLinearGroup.IsUnipotent.inv`: the inverse of a unipotent automorphism is
  unipotent.
* `TauCeti.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff`: unipotence after converting a
  linear equivalence to a general-linear-group element.
* `TauCeti.GeneralLinearGroup.isUnipotent_congrLinearEquiv_iff`: unipotence is invariant under
  transport by a linear equivalence.
* `TauCeti.GeneralLinearGroup.isUnipotent_inv_iff`: an automorphism is unipotent exactly when
  its inverse is.
* `TauCeti.GeneralLinearGroup.IsUnipotent.mul_of_commute`: commuting unipotent automorphisms have
  unipotent product.
* `TauCeti.GeneralLinearGroup.IsUnipotent.pow` and `.zpow`: every natural or integer power of a
  unipotent automorphism is unipotent.
* `TauCeti.GeneralLinearGroup.isUnipotent_conj_iff`: unipotence is invariant under
  conjugation.
* `TauCeti.GeneralLinearGroup.IsUnipotent.eq_one_of_finrank_eq_one`: a unipotent automorphism
  of a free rank-one module over a reduced commutative ring is the identity.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

open _root_.Module

universe u v w

variable {K : Type u} {V : Type v} [Semiring K] [AddCommGroup V] [Module K V]

/-- A linear automorphism is unipotent if its difference from the identity is nilpotent. -/
def IsUnipotent (g : GeneralLinearGroup K V) : Prop :=
  _root_.IsNilpotent ((g : End K V) - 1)

/-- Unipotence of a linear automorphism means that its underlying endomorphism minus the
identity is nilpotent. -/
theorem isUnipotent_def (g : GeneralLinearGroup K V) :
    IsUnipotent g ↔ _root_.IsNilpotent ((g : End K V) - 1) :=
  Iff.rfl

/-- An element of the general linear group is unipotent in its natural representation exactly
when subtracting the identity from its underlying matrix gives a nilpotent matrix. -/
theorem isUnipotent_toLin_iff
    (m : Type*) [Fintype m] [LinearOrder m] (R : Type u) [CommRing R] (g : GL m R) :
    IsUnipotent (Matrix.GeneralLinearGroup.toLin g) ↔
      _root_.IsNilpotent ((g : Matrix m m R) - 1) := by
  rw [isUnipotent_def, ← Matrix.isNilpotent_toLin'_iff, map_sub, Matrix.toLin'_one]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply',
    Module.End.one_eq_id]

/-- The identity automorphism is unipotent. -/
@[simp]
theorem isUnipotent_one : IsUnipotent (1 : GeneralLinearGroup K V) := by
  unfold IsUnipotent
  simp

/-- A linear equivalence is unipotent after conversion to the general linear group exactly when
its underlying endomorphism minus the identity is nilpotent. -/
@[simp]
theorem isUnipotent_ofLinearEquiv_iff (f : V ≃ₗ[K] V) :
    IsUnipotent (LinearMap.GeneralLinearGroup.ofLinearEquiv f) ↔
      _root_.IsNilpotent (f.toLinearMap - 1) := by
  rw [isUnipotent_def]
  have h :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv f : GeneralLinearGroup K V) : End K V) =
        f.toLinearMap := by
    ext x
    exact congrFun (LinearMap.GeneralLinearGroup.coe_ofLinearEquiv f) x
  rw [h]

/-- Unipotence of a linear automorphism is invariant under transport by a linear equivalence. -/
theorem isUnipotent_congrLinearEquiv_iff
    {W : Type w} [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    IsUnipotent (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (e.symm.trans (g.toLinearEquiv.trans e))) ↔ IsUnipotent g := by
  rw [isUnipotent_ofLinearEquiv_iff, isUnipotent_def]
  have hmap :
      LinearEquiv.conjRingEquiv e ((g : End K V) - 1) =
        (e.symm.trans (g.toLinearEquiv.trans e)).toLinearMap - 1 := by
    ext x
    simp
  rw [← hmap]
  exact IsNilpotent.map_iff (LinearEquiv.conjRingEquiv e).injective

/-- The inverse of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.inv {g : GeneralLinearGroup K V} (hg : IsUnipotent g) :
    IsUnipotent g⁻¹ := by
  rw [isUnipotent_def] at hg ⊢
  have hc : Commute ((g⁻¹ : GeneralLinearGroup K V) : End K V)
      ((g : End K V) - 1) :=
    (Commute.units_val (Commute.refl g).inv_left).sub_right (Commute.one_right _)
  have hnil : _root_.IsNilpotent
      (((g⁻¹ : GeneralLinearGroup K V) : End K V) * ((g : End K V) - 1)) :=
    hc.isNilpotent_mul_left hg
  have heq : ((g⁻¹ : GeneralLinearGroup K V) : End K V) - 1 =
      -(((g⁻¹ : GeneralLinearGroup K V) : End K V) * ((g : End K V) - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
    simp
  rw [heq]
  exact hnil.neg

/-- A linear automorphism is unipotent if and only if its inverse is unipotent. -/
@[simp]
theorem isUnipotent_inv_iff (g : GeneralLinearGroup K V) :
    IsUnipotent g⁻¹ ↔ IsUnipotent g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsUnipotent.inv

/-- The product of two commuting unipotent linear automorphisms is unipotent. -/
theorem IsUnipotent.mul_of_commute {g h : GeneralLinearGroup K V}
    (hg : IsUnipotent g) (hh : IsUnipotent h) (hcomm : Commute g h) :
    IsUnipotent (g * h) := by
  rw [isUnipotent_def] at hg hh ⊢
  let x : End K V := (g : End K V) - 1
  let y : End K V := (h : End K V) - 1
  have hxy : Commute x y :=
    (hcomm.units_val.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
  have hxyNil : _root_.IsNilpotent (x * y) := hxy.isNilpotent_mul_right hg
  have hsumNil : _root_.IsNilpotent (x + y) := hxy.isNilpotent_add hg hh
  have hsumComm : Commute (x + y) (x * y) :=
    ((Commute.refl x).mul_right hxy).add_left
      (hxy.symm.mul_right (Commute.refl y))
  have hnil : _root_.IsNilpotent (x + y + x * y) :=
    hsumComm.isNilpotent_add hsumNil hxyNil
  have heq : (((g * h : GeneralLinearGroup K V) : End K V) - 1) = x + y + x * y := by
    dsimp only [x, y]
    rw [Units.val_mul]
    noncomm_ring
  rw [heq]
  exact hnil

/-- Every natural power of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.pow {g : GeneralLinearGroup K V} (hg : IsUnipotent g) (n : ℕ) :
    IsUnipotent (g ^ n) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ]
      exact hn.mul_of_commute hg (Commute.self_pow g n).symm

/-- Every integer power of a unipotent linear automorphism is unipotent. -/
theorem IsUnipotent.zpow {g : GeneralLinearGroup K V} (hg : IsUnipotent g) (n : ℤ) :
    IsUnipotent (g ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hg.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hg.pow n.succ).inv

/-- Unipotence is invariant under conjugation by a linear automorphism. -/
@[simp]
theorem isUnipotent_conj_iff (g h : GeneralLinearGroup K V) :
    IsUnipotent (h * g * h⁻¹) ↔ IsUnipotent g := by
  have hconj : LinearMap.GeneralLinearGroup.ofLinearEquiv
      (h.toLinearEquiv.symm.trans (g.toLinearEquiv.trans h.toLinearEquiv)) =
        h * g * h⁻¹ := by
    ext x
    simp only [LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Units.val_mul, Module.End.mul_apply]
    apply congrArg (fun y ↦ (h : End K V) ((g : End K V) y))
    -- The preceding coercion normalization hides the inverse linear equivalence behind the
    -- inverse unit's function. Expose it so the named conversion lemma can rewrite it.
    change h.toLinearEquiv.symm x = (h⁻¹).toLinearEquiv x
    rw [LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
    rfl
  rw [← hconj]
  simpa only [isUnipotent_ofLinearEquiv_iff] using
    isUnipotent_congrLinearEquiv_iff h.toLinearEquiv g

/-- A unipotent automorphism of a free rank-one module over a reduced commutative ring is the
identity. -/
theorem IsUnipotent.eq_one_of_finrank_eq_one
    {F : Type u} {W : Type v} [CommRing F] [IsReduced F]
    [AddCommGroup W] [Module F W] [Module.Free F W]
    {g : GeneralLinearGroup F W} (hg : IsUnipotent g) (hdim : finrank F W = 1) :
    g = 1 := by
  by_cases hF : Subsingleton F
  · let _ : Subsingleton F := hF
    let _ : Subsingleton W := Module.subsingleton F W
    exact Subsingleton.elim _ _
  let _ : Nontrivial F := not_subsingleton_iff_nontrivial.mp hF
  let c : F := (LinearEquiv.smul_id_of_finrank_eq_one hdim).symm (g : End F W)
  have hc : (g : End F W) = c • LinearMap.id := by
    simpa only [LinearEquiv.smul_id_of_finrank_eq_one_apply] using
      ((LinearEquiv.smul_id_of_finrank_eq_one hdim).apply_symm_apply
        (g : End F W)).symm
  have hEnd : (g : End F W) - 1 = algebraMap F (End F W) (c - 1) := by
    rw [hc, Module.algebraMap_end_eq_smul_id]
    ext w
    simp [sub_smul]
  have hnil : _root_.IsNilpotent (c - 1) := by
    rw [isUnipotent_def, hEnd] at hg
    apply (IsNilpotent.map_iff ?_).mp hg
    intro a b hab
    apply (LinearEquiv.smul_id_of_finrank_eq_one hdim).injective
    simpa only [LinearEquiv.smul_id_of_finrank_eq_one_apply,
      Module.algebraMap_end_eq_smul_id] using hab
  have hc_one : c = 1 := sub_eq_zero.mp hnil.eq_zero
  apply Units.ext
  rw [hc, hc_one, one_smul]
  ext w
  simp

end GeneralLinearGroup

end TauCeti
