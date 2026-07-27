/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RepresentationTheory.Character

/-!
# Determinant-power representations of the general linear group

This file packages the determinant and its integral powers as one-dimensional representations of
the general linear group. These are the rational characters used to form determinant twists of
polynomial representations.

## Main definitions

* `TauCeti.detPowerRep` is the representation on the scalar module with action by `det(g)^m`.
* `TauCeti.detRep` is the determinant representation, the case `m = 1`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The one-dimensional representation of `GL n k` on which `g` acts by `det(g)^m`. -/
def detPowerRep (m : ℤ) : Representation k (GL (Fin n) k) k where
  toFun g := LinearMap.lsmul k k (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp [mul_zpow, mul_assoc]

/-- The determinant representation of `GL n k`. -/
abbrev detRep : Representation k (GL (Fin n) k) k := detPowerRep k n 1

/-- The determinant-power action is scalar multiplication by the indicated determinant power. -/
@[simp]
theorem detPowerRep_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n m g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) * x := by
  simp [detPowerRep, smul_eq_mul]

/-- The zero determinant power is the trivial representation. -/
@[simp]
theorem detPowerRep_zero : detPowerRep k n 0 = 1 := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  simp

/-- Adding exponents composes the corresponding determinant actions. -/
theorem detPowerRep_add_apply (m l : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (m + l) g x = detPowerRep k n m g (detPowerRep k n l g x) := by
  simp only [detPowerRep_apply, zpow_add, Units.val_mul]
  rw [mul_assoc]

/-- Every determinant-power representation restricts to the trivial representation of `SL n k`. -/
@[simp]
theorem detPowerRep_comp_toGL (m : ℤ) :
    (detPowerRep k n m).comp Matrix.SpecialLinearGroup.toGL =
      Representation.trivial k (Matrix.SpecialLinearGroup (Fin n) k) k := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  -- Unfolding the two composed monoid homomorphisms exposes the scalar-action formula.
  change detPowerRep k n m (Matrix.SpecialLinearGroup.toGL g) x = x
  rw [detPowerRep_apply]
  simp

/-- The determinant-power representation as a finite-dimensional representation. -/
noncomputable abbrev detPowerFDRep (m : ℤ) : FDRep k (GL (Fin n) k) :=
  FDRep.of (detPowerRep k n m)

/-- The determinant representation as a finite-dimensional representation. -/
noncomputable abbrev detFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (detRep k n)

end CommRing

section Field

variable [Field k]

/-- Negating the exponent makes the determinant scalar the inverse of the original power. -/
theorem detPowerRep_neg_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (-m) g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k)⁻¹ * x := by
  simp only [detPowerRep_apply, zpow_neg, Units.val_inv_eq_inv_val]

/-- The character of the determinant-power representation is the corresponding determinant power. -/
@[simp]
theorem char_detPowerRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
  rw [Representation.character]
  have haction : detPowerRep k n m g =
      LinearMap.lsmul k k (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
    apply LinearMap.ext
    intro x
    simp only [detPowerRep_apply, LinearMap.lsmul_apply, smul_eq_mul]
  rw [haction]
  have hlsmul : LinearMap.lsmul k k (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) =
      LinearMap.id.smulRight (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
    apply LinearMap.ext
    intro x
    simp [LinearMap.lsmul_apply, mul_comm]
  rw [hlsmul]
  simp only [LinearMap.trace_smulRight, LinearMap.id_apply]

/-- The bundled determinant-power character is the corresponding determinant power. -/
@[simp]
theorem char_detPowerFDRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerFDRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using char_detPowerRep k n m g

/-- The bundled determinant character is the determinant. -/
theorem char_detFDRep (g : GL (Fin n) k) :
    (detFDRep k n).character g = (Matrix.GeneralLinearGroup.det g : k) := by
  simpa only [zpow_one, Matrix.GeneralLinearGroup.val_det_apply] using char_detPowerFDRep k n 1 g

end Field

end TauCeti
