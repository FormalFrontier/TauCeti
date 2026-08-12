/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative
import Mathlib.Tactic.NoncommRing

/-!
# Closure properties of unipotent linear automorphisms

A linear automorphism is unipotent when its underlying endomorphism minus the identity is
nilpotent. This file records the elementary group-theoretic closure properties needed to use
unipotent elements in algebraic groups: inverses, products of commuting elements, powers, and
conjugates are unipotent.

Products require commutativity. Indeed, writing `g = 1 + x` and `h = 1 + y`, their product is
`1 + (x + y + xy)`; when `g` and `h` commute, the three displayed nilpotent endomorphisms commute.

## Main declarations

* `TauCeti.GeneralLinearGroup.IsUnipotent.inv`: the inverse of a unipotent automorphism is
  unipotent.
* `TauCeti.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff`: unipotence after converting a
  linear equivalence to a general-linear-group element.
* `TauCeti.GeneralLinearGroup.isUnipotent_inv_iff`: an automorphism is unipotent exactly when
  its inverse is.
* `TauCeti.GeneralLinearGroup.IsUnipotent.mul`: commuting unipotent automorphisms have unipotent
  product.
* `TauCeti.GeneralLinearGroup.IsUnipotent.pow`: every natural power of a unipotent automorphism
  is unipotent.
* `TauCeti.GeneralLinearGroup.isUnipotent_mul_mul_inv_iff`: unipotence is invariant under
  conjugation.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

open _root_.Module

universe u v

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]

/-- The endomorphism underlying a linear equivalence converted to the general linear group is
the original linear equivalence's underlying endomorphism. -/
theorem ofLinearEquiv_toLinearMap (f : V ≃ₗ[K] V) :
    ((LinearMap.GeneralLinearGroup.ofLinearEquiv f : GeneralLinearGroup K V) : End K V) =
      f.toLinearMap :=
  rfl

/-- Converting a power of a linear equivalence to the general linear group commutes with taking
that power. -/
theorem ofLinearEquiv_pow (f : V ≃ₗ[K] V) (n : ℕ) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv (f ^ n) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv f ^ n :=
  map_pow (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm f n

/-- A linear equivalence is unipotent after conversion to the general linear group exactly when
its underlying endomorphism minus the identity is nilpotent. -/
theorem isUnipotent_ofLinearEquiv_iff (f : V ≃ₗ[K] V) :
    IsUnipotent (LinearMap.GeneralLinearGroup.ofLinearEquiv f) ↔
      _root_.IsNilpotent (f.toLinearMap - 1) := by
  rw [isUnipotent_def, ofLinearEquiv_toLinearMap]

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
theorem IsUnipotent.mul {g h : GeneralLinearGroup K V}
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
      exact hn.mul hg (Commute.self_pow g n).symm

private theorem isNilpotent_conjugate_iff (x : End K V) (h : GeneralLinearGroup K V) :
    _root_.IsNilpotent ((h : End K V) * x * ((h⁻¹ : GeneralLinearGroup K V) : End K V)) ↔
      _root_.IsNilpotent x := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      x ^ n = ((h⁻¹ : GeneralLinearGroup K V) : End K V) *
          ((h : End K V) * x ^ n * ((h⁻¹ : GeneralLinearGroup K V) : End K V)) *
          (h : End K V) := by simp [mul_assoc]
      _ = ((h⁻¹ : GeneralLinearGroup K V) : End K V) *
          (((h : End K V) * x * ((h⁻¹ : GeneralLinearGroup K V) : End K V)) ^ n) *
          (h : End K V) := by rw [Units.conj_pow]
      _ = 0 := by rw [hn]; simp
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Units.conj_pow, hn]
    simp

/-- Unipotence is invariant under conjugation by a linear automorphism. -/
@[simp]
theorem isUnipotent_mul_mul_inv_iff (g h : GeneralLinearGroup K V) :
    IsUnipotent (h * g * h⁻¹) ↔ IsUnipotent g := by
  rw [isUnipotent_def, isUnipotent_def]
  have heq : (((h * g * h⁻¹ : GeneralLinearGroup K V) : End K V) - 1) =
      (h : End K V) * ((g : End K V) - 1) *
        ((h⁻¹ : GeneralLinearGroup K V) : End K V) := by
    simp only [Units.val_mul]
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  rw [heq, isNilpotent_conjugate_iff]

end GeneralLinearGroup

end TauCeti
