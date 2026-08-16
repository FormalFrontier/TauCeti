/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry

/-!
# Norms of integral lattices

The norm of a vector in an integral lattice is its self-pairing under the lattice bilinear form.
On lattice vectors this rational value has a canonical integral lift, the integral norm.

This file develops the rational and integral norm quadratic forms, their basic properties and
polarization identities, and the set of lattice vectors having a prescribed norm. An
integral-lattice isometry induces an isometry equivalence of the rational norm forms and preserves
the integral norm on the carrier.

## Main definitions

* `TauCeti.IntegralLattice.norm`: the rational quadratic form on ambient vectors.
* `TauCeti.IntegralLattice.integralNorm`: the induced integer quadratic form on lattice vectors.
* `TauCeti.IntegralLattice.vectorsOfNorm`: the lattice vectors of a specified rational norm.

## Main results

* `TauCeti.IntegralLattice.norm_apply`: evaluating the rational norm yields self-pairing.
* `TauCeti.IntegralLattice.integralNorm_apply`: evaluating the integral norm yields
  integral self-pairing.
* `TauCeti.IntegralLattice.integralNorm_cast`: the integral norm recovers the rational norm in `ℚ`.
* `TauCeti.IntegralLattice.Isometry.normIsometryEquiv`: the norm-form isometry induced by a lattice
  isometry.
* `TauCeti.IntegralLattice.norm_add`: polarization identity for the rational norm.
* `TauCeti.IntegralLattice.norm_sub`: subtractive polarization identity for the rational norm.
* `TauCeti.IntegralLattice.integralNorm_add`: polarization identity for the integral norm.
* `TauCeti.IntegralLattice.integralNorm_sub`: subtractive polarization identity for the integral
  norm.
* `TauCeti.IntegralLattice.mem_vectorsOfNorm_intCast`: characterization of integer-norm vectors.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

namespace IntegralLattice

/-! ## Norms -/

/-- The rational quadratic form on ambient vectors given by self-pairing. -/
def norm (L : IntegralLattice V) : QuadraticForm ℚ V := L.form.toQuadraticMap

/-- The rational norm form is the quadratic form associated to the ambient bilinear form. -/
theorem norm_def (L : IntegralLattice V) :
    L.norm = L.form.toQuadraticMap :=
  (rfl)

-- The evaluation and negation identities below remain explicit rewrite lemmas. Registering them
-- with `simp` makes the specialized cast, zero, and scaling rules fail the `simpNF` linter.

/-- Evaluating the rational norm of an ambient vector yields its self-pairing. -/
theorem norm_apply (L : IntegralLattice V) (x : V) : L.norm x = L.form x x :=
  LinearMap.BilinMap.toQuadraticMap_apply L.form x

/-- The canonical integer quadratic form induced on the lattice carrier. -/
noncomputable def integralNorm (L : IntegralLattice V) : QuadraticForm ℤ L :=
  L.integralForm.toQuadraticMap

/-- Evaluating the integral norm of a lattice vector yields its integral self-pairing. -/
theorem integralNorm_apply (L : IntegralLattice V) (x : L) :
    L.integralNorm x = L.integralForm x x :=
  LinearMap.BilinMap.toQuadraticMap_apply L.integralForm x

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- An integral-lattice isometry, regarded as an isometry equivalence of the associated rational
norm forms. -/
def normIsometryEquiv (e : Isometry L M) : L.norm.IsometryEquiv M.norm where
  toLinearEquiv := e
  map_app' x := e.toIsometryEquiv.map_app x x

/-- The linear equivalence underlying the norm isometry is the original ambient equivalence. -/
@[simp]
theorem normIsometryEquiv_toLinearEquiv (e : Isometry L M) :
    e.normIsometryEquiv.toLinearEquiv = (e : V ≃ₗ[ℚ] W) :=
  (rfl)

/-- An integral-lattice isometry preserves the rational norm. -/
@[simp]
theorem norm_apply (e : Isometry L M) (x : V) : M.norm (e x) = L.norm x :=
  e.normIsometryEquiv.map_app x

/-- The carrier equivalence of an integral-lattice isometry preserves the integral norm. -/
@[simp]
theorem integralNorm_carrierEquiv (e : Isometry L M) (x : L) :
    M.integralNorm (e.carrierEquiv x) = L.integralNorm x := by
  rw [M.integralNorm_apply, L.integralNorm_apply, e.carrierEquiv_map_integralForm]

end Isometry

/-- The integral norm recovers the rational norm after coercion to `ℚ`. -/
@[simp]
theorem integralNorm_cast (L : IntegralLattice V) (x : L) :
    (L.integralNorm x : ℚ) = L.norm x := by
  simpa only [integralNorm_apply, norm_apply] using L.integralForm_cast x x

/-- The rational norm of zero is zero. -/
@[simp]
theorem norm_zero (L : IntegralLattice V) : L.norm 0 = 0 :=
  L.norm.map_zero

/-- The rational norm is invariant under negation. -/
theorem norm_neg (L : IntegralLattice V) (x : V) : L.norm (-x) = L.norm x :=
  L.norm.map_neg x

/-- Scaling an ambient vector squares its rational norm. -/
@[simp]
theorem norm_smul (L : IntegralLattice V) (a : ℚ) (x : V) :
    L.norm (a • x) = a ^ 2 * L.norm x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

/-- Polarization of the norm using symmetry of the lattice form. -/
theorem norm_add (L : IntegralLattice V) (x y : V) :
    L.norm (x + y) = L.norm x + L.norm y + 2 * L.form x y := by
  rw [QuadraticMap.map_add L.norm x y, norm, LinearMap.BilinMap.polar_toQuadraticMap,
    L.isSymm.eq y x]
  ring

/-- The subtraction form of the norm polarization identity. -/
theorem norm_sub (L : IntegralLattice V) (x y : V) :
    L.norm (x - y) = L.norm x + L.norm y - 2 * L.form x y := by
  rw [sub_eq_add_neg, L.norm_add, L.norm_neg, map_neg, mul_neg, sub_eq_add_neg]

/-- The integral norm of zero is zero. -/
@[simp]
theorem integralNorm_zero (L : IntegralLattice V) : L.integralNorm 0 = 0 :=
  L.integralNorm.map_zero

/-- The integral norm is invariant under negation. -/
theorem integralNorm_neg (L : IntegralLattice V) (x : L) :
    L.integralNorm (-x) = L.integralNorm x :=
  L.integralNorm.map_neg x

/-- Scaling a lattice vector by an integer scales its integral norm by the square. -/
@[simp]
theorem integralNorm_zsmul (L : IntegralLattice V) (a : ℤ) (x : L) :
    L.integralNorm (a • x) = a ^ 2 * L.integralNorm x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

/-- Integral polarization of the norm. -/
theorem integralNorm_add (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x + y) =
      L.integralNorm x + L.integralNorm y + 2 * L.integralForm x y := by
  rw [QuadraticMap.map_add L.integralNorm x y, integralNorm,
    LinearMap.BilinMap.polar_toQuadraticMap, L.isSymm_integralForm.eq y x]
  ring

/-- Integral polarization for a difference. -/
theorem integralNorm_sub (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x - y) =
      L.integralNorm x + L.integralNorm y - 2 * L.integralForm x y := by
  rw [sub_eq_add_neg, L.integralNorm_add, L.integralNorm_neg, map_neg, mul_neg, sub_eq_add_neg]

/-! ## Vectors of prescribed norm -/

/-- The lattice vectors having the prescribed rational norm. -/
def vectorsOfNorm (L : IntegralLattice V) (n : ℚ) : Set L := {x | L.norm x = n}

/-- Membership condition for `vectorsOfNorm`. -/
@[simp]
theorem mem_vectorsOfNorm {L : IntegralLattice V} {n : ℚ} {x : L} :
    x ∈ L.vectorsOfNorm n ↔ L.norm x = n := Iff.rfl

/-- Membership in `vectorsOfNorm (n : ℚ)` for an integer `n` is equivalent to having integral norm
equal to `n`.  This remains an explicit rewrite lemma because `mem_vectorsOfNorm` already
simplifies its left-hand side, so tagging both lemmas would violate `simpNF`. -/
theorem mem_vectorsOfNorm_intCast (L : IntegralLattice V) {n : ℤ} {x : L} :
    x ∈ L.vectorsOfNorm (n : ℚ) ↔ L.integralNorm x = n := by
  rw [mem_vectorsOfNorm, ← L.integralNorm_cast x]
  exact Int.cast_inj

/-- The zero vector in an integral lattice has norm zero. -/
theorem zero_mem_vectorsOfNorm (L : IntegralLattice V) : (0 : L) ∈ L.vectorsOfNorm 0 := by
  simp

/-- A lattice vector has norm `n` if and only if its negation does. -/
theorem neg_mem_vectorsOfNorm_iff {L : IntegralLattice V} {n : ℚ} (x : L) :
    -x ∈ L.vectorsOfNorm n ↔ x ∈ L.vectorsOfNorm n := by
  simp [mem_vectorsOfNorm]

-- This membership transport is not registered with `simp`: `mem_vectorsOfNorm`,
-- `coe_carrierEquiv_apply`, and `Isometry.norm_apply` already prove it, so tagging it fails the
-- `simpNF` linter.

/-- A carrier vector belongs to a prescribed norm set if and only if its image under an isometry
does. -/
theorem Isometry.carrierEquiv_mem_vectorsOfNorm_iff {L : IntegralLattice V}
    {M : IntegralLattice W} (e : Isometry L M) (x : L) (n : ℚ) :
    e.carrierEquiv x ∈ M.vectorsOfNorm n ↔ x ∈ L.vectorsOfNorm n := by
  simp only [mem_vectorsOfNorm, e.coe_carrierEquiv_apply, e.norm_apply]

/-- If a rational number is not an integer, no lattice vector has that norm. -/
theorem vectorsOfNorm_eq_empty_of_forall_ne_intCast (L : IntegralLattice V) {n : ℚ}
    (hn : ∀ z : ℤ, n ≠ z) : L.vectorsOfNorm n = ∅ := by
  ext x
  simp only [mem_vectorsOfNorm, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn (L.integralNorm x) (hx.symm.trans (L.integralNorm_cast x).symm)

end IntegralLattice

end TauCeti
