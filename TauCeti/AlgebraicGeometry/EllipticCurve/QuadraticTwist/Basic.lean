/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Quadratic twists of Weierstrass curves

This file defines the quadratic twist of a Weierstrass curve by the trace and norm of a
quadratic element. The construction works over an arbitrary commutative ring, including in
characteristic two.

For parameters `t` and `n`, put `D = t² - 4n`. If a quadratic element `θ` has trace `t` and
norm `n`, then it satisfies `θ² = tθ - n`. When the associated quadratic algebra is separable
and nontrivial, the twist is obtained by descent along its nontrivial automorphism. The displayed
formulas remain defined over an arbitrary commutative ring, whether or not this descent
interpretation applies. Its invariants transform by

* `b₂ ↦ D b₂`, `b₄ ↦ D² b₄`, and `b₆ ↦ D³ b₆`;
* `c₄ ↦ D² c₄`, `c₆ ↦ D³ c₆`, and `Δ ↦ D⁶ Δ`.

Consequently a twist of an elliptic curve over a field is elliptic when `D ≠ 0`, and it has
the same `j`-invariant. The construction commutes with arbitrary ring homomorphisms. Changing a
quadratic generator changes `(t, n)` by
`(t, n) ↦ (a t + 2b, b² + abt + a²n)`; the resulting twists are related by an explicit
admissible change of variables.

The mathematics follows [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009],
Chapter X, §5. The characteristic-free formulas and proofs are adapted from the FLT quadratic
twist development, `FLT/KnownIn1980s/EllipticCurves/QuadraticTwists/QuadraticTwists.lean` at
revision `bc2fe8ff7396` (Apache 2.0), by Kevin Buzzard and Claude.

## Main declarations

* `TauCeti.WeierstrassCurve.quadraticTwistOf` is the characteristic-free twist by `(t, n)`;
* `TauCeti.WeierstrassCurve.map_quadraticTwistOf` proves compatibility with ring homomorphisms;
* `TauCeti.WeierstrassCurve.isElliptic_quadraticTwistOf` proves ellipticity over a field;
* `TauCeti.WeierstrassCurve.j_quadraticTwistOf` proves invariance of the `j`-invariant;
* `TauCeti.WeierstrassCurve.exists_smul_quadraticTwistOf_eq` proves independence of the quadratic
  generator up to an admissible change of variables.
-/

public section

namespace TauCeti

namespace WeierstrassCurve

universe u

open _root_.WeierstrassCurve

section CommRing

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The quadratic twist of `E` by parameters `t` and `n`, interpreted as the trace and norm of a
quadratic element. The discriminant of its defining quadratic polynomial is `t ^ 2 - 4 * n`.

This formula is valid in every characteristic. Over a field of characteristic different from two,
setting `t = 0` recovers the usual square-class twist after a harmless square rescaling. In
characteristic two it also captures Artin–Schreier twists. -/
def quadraticTwistOf (t n : A) : WeierstrassCurve A where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

@[simp]
theorem quadraticTwistOf_a₁ (t n : A) : (quadraticTwistOf E t n).a₁ = t * E.a₁ :=
  (rfl)

@[simp]
theorem quadraticTwistOf_a₂ (t n : A) :
    (quadraticTwistOf E t n).a₂ = (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2 :=
  (rfl)

@[simp]
theorem quadraticTwistOf_a₃ (t n : A) :
    (quadraticTwistOf E t n).a₃ = (t ^ 2 - 4 * n) * t * E.a₃ :=
  (rfl)

@[simp]
theorem quadraticTwistOf_a₄ (t n : A) :
    (quadraticTwistOf E t n).a₄ =
      (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃ :=
  (rfl)

@[simp]
theorem quadraticTwistOf_a₆ (t n : A) :
    (quadraticTwistOf E t n).a₆ =
      (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2 :=
  (rfl)

variable (t n : A)

/-- The `b₂`-invariant of a quadratic twist is multiplied by its parameter discriminant. -/
@[simp]
theorem b₂_quadraticTwistOf :
    (quadraticTwistOf E t n).b₂ = (t ^ 2 - 4 * n) * E.b₂ := by
  simp only [b₂, quadraticTwistOf_a₁, quadraticTwistOf_a₂]
  ring

/-- The `b₄`-invariant of a quadratic twist is multiplied by the square of its parameter
discriminant. -/
@[simp]
theorem b₄_quadraticTwistOf :
    (quadraticTwistOf E t n).b₄ = (t ^ 2 - 4 * n) ^ 2 * E.b₄ := by
  simp only [b₄, quadraticTwistOf_a₁, quadraticTwistOf_a₃, quadraticTwistOf_a₄]
  ring

/-- The `b₆`-invariant of a quadratic twist is multiplied by the cube of its parameter
discriminant. -/
@[simp]
theorem b₆_quadraticTwistOf :
    (quadraticTwistOf E t n).b₆ = (t ^ 2 - 4 * n) ^ 3 * E.b₆ := by
  simp only [b₆, quadraticTwistOf_a₃, quadraticTwistOf_a₆]
  ring

/-- The `b₈`-invariant of a quadratic twist is multiplied by the fourth power of its parameter
discriminant. -/
@[simp]
theorem b₈_quadraticTwistOf :
    (quadraticTwistOf E t n).b₈ = (t ^ 2 - 4 * n) ^ 4 * E.b₈ := by
  simp only [b₈, quadraticTwistOf_a₁, quadraticTwistOf_a₂, quadraticTwistOf_a₃,
    quadraticTwistOf_a₄, quadraticTwistOf_a₆]
  ring

/-- The `c₄`-invariant of a quadratic twist is multiplied by the square of its parameter
discriminant. -/
@[simp]
theorem c₄_quadraticTwistOf :
    (quadraticTwistOf E t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [c₄, b₂_quadraticTwistOf, b₄_quadraticTwistOf]
  ring

/-- The `c₆`-invariant of a quadratic twist is multiplied by the cube of its parameter
discriminant. -/
@[simp]
theorem c₆_quadraticTwistOf :
    (quadraticTwistOf E t n).c₆ = (t ^ 2 - 4 * n) ^ 3 * E.c₆ := by
  simp only [c₆, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf]
  ring

/-- The discriminant of a quadratic twist is multiplied by the sixth power of its parameter
discriminant. -/
@[simp]
theorem Δ_quadraticTwistOf :
    (quadraticTwistOf E t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [Δ, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf,
    b₈_quadraticTwistOf]
  ring

/-- Quadratic twisting commutes with a ring homomorphism. -/
@[simp]
theorem map_quadraticTwistOf {B : Type*} [CommRing B] (f : A →+* B) :
    (quadraticTwistOf E t n).map f = quadraticTwistOf (E.map f) (f t) (f n) := by
  ext <;>
    simp only [quadraticTwistOf_a₁, quadraticTwistOf_a₂, quadraticTwistOf_a₃,
      quadraticTwistOf_a₄, quadraticTwistOf_a₆, map_a₁, map_a₂, map_a₃, map_a₄,
      map_a₆, map_mul, map_sub, map_pow, map_ofNat]

/-- Quadratic twisting commutes with extension of scalars. -/
@[simp]
theorem baseChange_quadraticTwistOf {B : Type*} [CommRing B] [Algebra A B] :
    (quadraticTwistOf E t n).baseChange B =
      quadraticTwistOf (E.baseChange B) (algebraMap A B t) (algebraMap A B n) :=
  map_quadraticTwistOf E t n (algebraMap A B)

/-- A quadratic twist of an elliptic curve remains elliptic when the parameter discriminant is a
unit. -/
theorem isElliptic_quadraticTwistOf_of_isUnit [E.IsElliptic] (hD : IsUnit (t ^ 2 - 4 * n)) :
    (quadraticTwistOf E t n).IsElliptic := by
  rw [isElliptic_iff, Δ_quadraticTwistOf]
  exact (hD.pow 6).mul E.isUnit_Δ

/-- Quadratic twisting preserves the `j`-invariant over a commutative ring. -/
theorem j_quadraticTwistOf [E.IsElliptic] (h : (quadraticTwistOf E t n).IsElliptic) :
    (quadraticTwistOf E t n).j = E.j := by
  have hD : IsUnit (t ^ 2 - 4 * n) := by
    have hΔ := (quadraticTwistOf E t n).isUnit_Δ
    rw [Δ_quadraticTwistOf] at hΔ
    exact (isUnit_pow_iff (by norm_num : 6 ≠ 0)).mp (IsUnit.mul_iff.mp hΔ).1
  rcases hD with ⟨Dunit, hD⟩
  have hΔ : (quadraticTwistOf E t n).Δ' = Dunit ^ 6 * E.Δ' := by
    ext
    simp only [coe_Δ', Units.val_mul, Units.val_pow_eq_pow_val,
      Δ_quadraticTwistOf, hD]
  simp only [j, hΔ, mul_inv_rev, Units.val_mul, c₄_quadraticTwistOf]
  rw [← hD]
  calc
    (↑E.Δ'⁻¹ : A) * (↑Dunit⁻¹ : A) ^ 6 * ((↑Dunit : A) ^ 2 * E.c₄) ^ 3 =
        (↑E.Δ'⁻¹ : A) * ((↑Dunit⁻¹ : A) ^ 6 * (↑Dunit : A) ^ 6) * E.c₄ ^ 3 := by
      ring
    _ = (↑E.Δ'⁻¹ : A) * E.c₄ ^ 3 := by
      rw [pow_mul_pow_eq_one 6 Dunit.inv_mul]
      ring

/-- Twisting twice by the same parameters gives a curve isomorphic to the original one when the
parameter discriminant is a unit. -/
theorem exists_smul_eq_quadraticTwistOf_quadraticTwistOf_of_isUnit
    (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ C : VariableChange A,
      C • E = quadraticTwistOf (quadraticTwistOf E t n) t n := by
  generalize hDdef : t ^ 2 - 4 * n = D at hD
  let _ := hD.invertible
  have ht : t ^ 2 = D + 4 * n := by rw [← hDdef]; ring
  have hDi : D * ⅟D = 1 := mul_invOf_self D
  have hDi2 : D ^ 2 * ⅟D ^ 2 = 1 := pow_mul_pow_eq_one 2 hDi
  refine ⟨⟨(unitOfInvertible D)⁻¹, 0, 2 * n * ⅟D * E.a₁,
    2 * n * ⅟D * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf_a₁, quadraticTwistOf_a₂, quadraticTwistOf_a₃,
    quadraticTwistOf_a₄, quadraticTwistOf_a₆, inv_inv, unitOfInvertible]
  all_goals try rw [hDdef]
  all_goals ring_nf
  all_goals rw [ht]
  all_goals ring_nf
  case a₁ => linear_combination E.a₁ * n * 4 * hDi
  case a₂ => linear_combination (-(D * n * E.a₁ ^ 2 * 2)) * hDi -
      (n ^ 2 * E.a₁ ^ 2 * 4) * hDi2
  case a₃ => linear_combination D ^ 2 * E.a₃ * n * 4 * hDi
  case a₄ => linear_combination (-(D ^ 3 * n * E.a₁ * E.a₃ * 4)) * hDi -
      (D ^ 2 * n ^ 2 * E.a₁ * E.a₃ * 8) * hDi2
  case a₆ => linear_combination (-(D ^ 5 * n * E.a₃ ^ 2 * 2)) * hDi -
      (D ^ 4 * n ^ 2 * E.a₃ ^ 2 * 4) * hDi2

/-- Replacing a quadratic generator `θ` by `aθ + b`, for a unit `a`, changes the corresponding
twist by an admissible change of variables. -/
theorem exists_smul_quadraticTwistOf_eq_of_isUnit {a : A} (b : A) (ha : IsUnit a) :
    ∃ C : VariableChange A, C • quadraticTwistOf E t n =
      quadraticTwistOf E (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) := by
  let _ := ha.invertible
  have hai : a * ⅟a = 1 := mul_invOf_self a
  have hai2 : a ^ 2 * ⅟a ^ 2 = 1 := pow_mul_pow_eq_one 2 hai
  refine ⟨⟨(unitOfInvertible a)⁻¹, 0, ⅟a * b * E.a₁,
    ⅟a * b * (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf_a₁, quadraticTwistOf_a₂, quadraticTwistOf_a₃,
    quadraticTwistOf_a₄, quadraticTwistOf_a₆, inv_inv, unitOfInvertible]
  all_goals ring_nf
  case a₁ => linear_combination E.a₁ * b * 2 * hai
  case a₂ => linear_combination (-(a * t * E.a₁ ^ 2 * b)) * hai -
      (E.a₁ ^ 2 * b ^ 2) * hai2
  case a₃ => linear_combination (a ^ 2 * b * E.a₃ * (t ^ 2 - 4 * n) * 2) * hai
  case a₄ => linear_combination (a ^ 3 * t * b * E.a₁ * E.a₃ *
      (8 * n - 2 * t ^ 2)) * hai +
      (a ^ 2 * b ^ 2 * E.a₁ * E.a₃ * (8 * n - 2 * t ^ 2)) * hai2
  case a₆ => linear_combination (a ^ 5 * t * b * E.a₃ ^ 2 *
      (-16 * n ^ 2 + 8 * t ^ 2 * n - t ^ 4)) * hai +
      (a ^ 4 * b ^ 2 * E.a₃ ^ 2 * (8 * t ^ 2 * n - t ^ 4 - 16 * n ^ 2)) * hai2

end CommRing

section Field

variable {K : Type u} [Field K] (E : WeierstrassCurve K) (t n : K)

/-- A quadratic twist of an elliptic curve is elliptic when the parameter discriminant is
nonzero. -/
theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : t ^ 2 - 4 * n ≠ 0) :
    (quadraticTwistOf E t n).IsElliptic :=
  isElliptic_quadraticTwistOf_of_isUnit E t n (isUnit_iff_ne_zero.mpr hD)

/-- Twisting twice by the same parameters gives a curve isomorphic to the original one. -/
theorem exists_smul_eq_quadraticTwistOf_quadraticTwistOf (hD : t ^ 2 - 4 * n ≠ 0) :
    ∃ C : VariableChange K,
      C • E = quadraticTwistOf (quadraticTwistOf E t n) t n :=
  exists_smul_eq_quadraticTwistOf_quadraticTwistOf_of_isUnit E t n
    (isUnit_iff_ne_zero.mpr hD)

/-- Replacing a quadratic generator `θ` by `aθ + b` changes the corresponding twist by an
admissible change of variables. The new trace and norm are `a * t + 2 * b` and
`b ^ 2 + a * b * t + a ^ 2 * n`. -/
theorem exists_smul_quadraticTwistOf_eq {a : K} (b : K) (ha : a ≠ 0) :
    ∃ C : VariableChange K, C • quadraticTwistOf E t n =
      quadraticTwistOf E (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) :=
  exists_smul_quadraticTwistOf_eq_of_isUnit E t n b (isUnit_iff_ne_zero.mpr ha)

end Field

end WeierstrassCurve

end TauCeti
