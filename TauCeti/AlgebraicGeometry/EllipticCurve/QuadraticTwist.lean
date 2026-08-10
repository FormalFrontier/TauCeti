/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# The quadratic twist of a Weierstrass curve: definition and invariants

The quadratic twist `E.quadraticTwistOf t n` of a Weierstrass curve by parameters `(t, n)` — to
be thought of as the trace and norm of a generator `θ` of a separable quadratic extension
`L/K`, with `D := t² - 4n` the discriminant of its minimal polynomial — together with the
behaviour of the standard invariants under twisting, uniformly in the characteristic: over any
commutative ring `b₂, b₄, b₆` scale by `D, D², D³`, `c₄, c₆` by `D², D³`, and `Δ` by `D⁶`, so
the twist of an elliptic curve is elliptic exactly when `D` is a unit — over a field, when
`D ≠ 0` —
with the same `j`-invariant. Twisting by a split quadratic, twisting twice by `(t, n)`, or
changing `(t, n)` to the trace and norm of another generator, all move the twist by an explicit
change of variables, again over any commutative ring in which the relevant parameter is a unit.

## Main definitions

* `WeierstrassCurve.quadraticTwistOf`: the quadratic twist of a Weierstrass curve by `(t, n)`,
  an explicit Weierstrass model over any commutative ring.
* `WeierstrassCurve.Δ_quadraticTwistOf`, `WeierstrassCurve.c₄_quadraticTwistOf`,
  `WeierstrassCurve.c₆_quadraticTwistOf`: the invariants of the twist.
* `WeierstrassCurve.isElliptic_quadraticTwistOf_iff` and its field specialisation
  `WeierstrassCurve.isElliptic_quadraticTwistOf`, and `WeierstrassCurve.j_quadraticTwistOf`: the
  twist of an elliptic curve is elliptic exactly when `t² - 4n` is a unit — over a field, when
  it is nonzero — with equal `j`.
* `WeierstrassCurve.exists_smul_eq_quadraticTwistOf_quadraticTwistOf`,
  `WeierstrassCurve.exists_smul_quadraticTwistOf_eq`: the double twist is isomorphic to the
  original curve, and changing the generator moves the twist by a change of variables.
* `WeierstrassCurve.isElliptic_quadraticTwistOf_trace_norm`,
  `WeierstrassCurve.exists_smul_quadraticTwistOf_trace_norm_eq`: the twist by the trace and norm
  of a generator `θ` of a *separable* quadratic extension `L/K` is elliptic when `E` is, and
  changing the generator moves it by a change of variables — which is what makes the twist by the
  extension well posed.

These are the `quadraticTwistOf` seeds of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5
(twists), pinned in that roadmap's `Suggested.lean`; the extension twist `quadraticTwist E L`
by a separable quadratic extension, the point isomorphism, and the split-multiplicative-
reduction theorem are later milestones of the same layer and build on this file.

The twist by a generator is deliberately **not** given its own constructor here. Such a
definition would accept any field extension, and outside the finite-dimensional case Mathlib's
`Algebra.trace` and `Algebra.norm` are `0` and `1`, so every `θ` would yield the same unrelated
`(0, 1)` twist. The results below instead name `Algebra.trace K L θ` and `Algebra.norm K θ`
directly and carry `[Algebra.IsQuadraticExtension K L]`, where the construction has its intended
meaning.

Adapted from the FLT project's quadratic-twist development (`ImperialCollegeLondon/FLT`,
`FLT/KnownIn1980s/EllipticCurves/QuadraticTwists/QuadraticTwists.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Kevin Buzzard, Claude`, and it has not been touched in FLT since `bc2fe8ff7396`, so
the pin and the working clone (`d18b563029f3`, a later Mathlib bump) agree on it verbatim.
Following this repository's convention for adapted material, the upstream authorship is
credited here rather than in the copyright header.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.§10, X.§2 and X.§5
-/

public section

namespace WeierstrassCurve

section QuadraticTwistOfRing

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by parameters `t`, `n`, to be
thought of as the trace and norm of a generator `θ` of a separable quadratic extension `L/K`
(so that `θ² = tθ - n`, and `D := t² - 4n` is the discriminant of the minimal polynomial of
`θ`). The parameters are arbitrary elements of any commutative ring `A`; the reading of `(t, n)`
as the trace and norm of a generator of a separable quadratic extension, with `D ≠ 0` the
separability criterion, is the field case. Over a general commutative ring the condition that
makes the twist behave — and the hypothesis the results below take — is that `D` be a *unit*.

The construction: writing the equation of `E` as `y² + A(x)y = f(x)` with `A(x) = a₁x + a₃`,
the functions `x` and `Y := (t - 2θ)y - θ·A(x)` on `E` are invariant under the Galois action
twisted by the quadratic character of `L/K`, and satisfy
`Y² + t·A(x)·Y = D·(y² + A(x)y) - n·A(x)²`; clearing denominators via `(x, Y) ↦ (Dx, DY)`
turns this relation into the Weierstrass model below of the twist:

`y² + ta₁·xy + Dta₃·y = x³ + (Da₂ - na₁²)·x² + (D²a₄ - 2Dna₁a₃)·x + (D³a₆ - D²na₃²)`.

Its discriminant is `D⁶·Δ(E)` (`Δ_quadraticTwistOf`), so the twist of an elliptic curve is
elliptic exactly when `D` is a unit (`isElliptic_quadraticTwistOf_iff`) — over a field, when
`D ≠ 0` (`isElliptic_quadraticTwistOf`) — with the same `j`-invariant (`j_quadraticTwistOf`).

Sanity checks. If `char K ≠ 2` we may take `θ = √d`, so `t = 0`, `n = -d`, `D = 4d`; for
`E : y² = x³ + a₂x² + a₄x + a₆` the model is `y² = x³ + 4da₂x² + 16d²a₄x + 64d³a₆`, the
classical twist by `4d ≡ d mod (K^×)²`. If `char K = 2` we may take `θ` with `θ² + θ = d`
(Artin–Schreier), so `t = 1`, `n = -d`, `D = 1`; for ordinary `E : y² + xy = x³ + a₂x² + a₆`
the model is the classical twist `y² + xy = x³ + (a₂ + d)x² + a₆`, and for supersingular
`E : y² + a₃y = x³ + a₄x + a₆` it is `y² + a₃y = x³ + a₄x + (a₆ + da₃²)`. -/
def quadraticTwistOf (t n : A) : WeierstrassCurve A where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

variable (t n : A)

/-- The coefficient `a₁` of the quadratic twist. -/
@[simp] theorem a₁_quadraticTwistOf : (E.quadraticTwistOf t n).a₁ = t * E.a₁ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₂` of the quadratic twist. -/
@[simp] theorem a₂_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₂ = (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2 := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₃` of the quadratic twist. -/
@[simp] theorem a₃_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₃ = (t ^ 2 - 4 * n) * t * E.a₃ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₄` of the quadratic twist. -/
@[simp] theorem a₄_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₄
      = (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃ := by
  simp only [quadraticTwistOf]

/-- The coefficient `a₆` of the quadratic twist. -/
@[simp] theorem a₆_quadraticTwistOf :
    (E.quadraticTwistOf t n).a₆
      = (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2 := by
  simp only [quadraticTwistOf]

/-- Twisting by `(t, n) = (1, 0)` — the split quadratic `x² - x`, with `D = 1` — returns the
curve itself. -/
@[simp] theorem quadraticTwistOf_one_zero : E.quadraticTwistOf 1 0 = E := by
  ext <;>
    simp only [a₁_quadraticTwistOf, a₂_quadraticTwistOf, a₃_quadraticTwistOf,
      a₄_quadraticTwistOf, a₆_quadraticTwistOf] <;>
    ring

/-- The invariant `b₂` of the quadratic twist: `b₂ ↦ Db₂` with `D = t² - 4n`. -/
@[simp] theorem b₂_quadraticTwistOf : (E.quadraticTwistOf t n).b₂ = (t ^ 2 - 4 * n) * E.b₂ := by
  simp only [quadraticTwistOf, b₂]; ring

/-- The invariant `b₄` of the quadratic twist: `b₄ ↦ D²b₄` with `D = t² - 4n`. -/
@[simp] theorem b₄_quadraticTwistOf : (E.quadraticTwistOf t n).b₄ = (t ^ 2 - 4 * n) ^ 2 * E.b₄ := by
  simp only [quadraticTwistOf, b₄]; ring

/-- The invariant `b₆` of the quadratic twist: `b₆ ↦ D³b₆` with `D = t² - 4n`. -/
@[simp] theorem b₆_quadraticTwistOf : (E.quadraticTwistOf t n).b₆ = (t ^ 2 - 4 * n) ^ 3 * E.b₆ := by
  simp only [quadraticTwistOf, b₆]; ring

/-- The invariant `b₈` of the quadratic twist: `b₈ ↦ D⁴b₈` with `D = t² - 4n`. -/
@[simp] theorem b₈_quadraticTwistOf : (E.quadraticTwistOf t n).b₈ = (t ^ 2 - 4 * n) ^ 4 * E.b₈ := by
  simp only [quadraticTwistOf, b₈]; ring

/-- The invariant `c₄` of the quadratic twist: `c₄ ↦ D²c₄` with `D = t² - 4n`. -/
@[simp] theorem c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [c₄, b₂_quadraticTwistOf, b₄_quadraticTwistOf]
  ring

/-- The invariant `c₆` of the quadratic twist: `c₆ ↦ D³c₆` with `D = t² - 4n`. -/
@[simp] theorem c₆_quadraticTwistOf : (E.quadraticTwistOf t n).c₆ = (t ^ 2 - 4 * n) ^ 3 * E.c₆ := by
  simp only [c₆, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf]
  ring

/-- The discriminant of the quadratic twist: `Δ ↦ D⁶Δ` with `D = t² - 4n`. -/
@[simp] theorem Δ_quadraticTwistOf : (E.quadraticTwistOf t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [Δ, b₂_quadraticTwistOf, b₄_quadraticTwistOf, b₆_quadraticTwistOf,
    b₈_quadraticTwistOf]
  ring

/-- The quadratic twist commutes with a ring homomorphism `f` (in particular with base change):
`(E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n)`. -/
@[simp] theorem map_quadraticTwistOf {B : Type*} [CommRing B] (f : A →+* B) :
    (E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n) := by
  ext <;>
    simp only [quadraticTwistOf, map_a₁, map_a₂,
      map_a₃, map_a₄, map_a₆, map_mul, map_sub,
      map_pow, map_ofNat]

/-- Quadratic twisting commutes with extension of scalars: the twist of the base change is the
base change of the twist, by the images of the parameters. -/
@[simp] theorem baseChange_quadraticTwistOf {B : Type*} [CommRing B] [Algebra A B] :
    (E.quadraticTwistOf t n).baseChange B
      = (E.baseChange B).quadraticTwistOf (algebraMap A B t) (algebraMap A B n) := by
  simp only [WeierstrassCurve.baseChange, map_quadraticTwistOf]

/-- The quadratic twist of an elliptic curve is elliptic exactly when the discriminant
`D = t² - 4n` of the twisting parameters is a unit. Over a general commutative ring `D ≠ 0` is
not the right criterion (take `A = ℤ`, `D = 2`); over a field the two coincide, which is
`isElliptic_quadraticTwistOf`. -/
theorem isElliptic_quadraticTwistOf_iff :
    (E.quadraticTwistOf t n).IsElliptic ↔ IsUnit (t ^ 2 - 4 * n) ∧ E.IsElliptic := by
  rw [isElliptic_iff, isElliptic_iff, Δ_quadraticTwistOf]
  refine ⟨fun h ↦ ⟨(isUnit_pow_iff (by norm_num)).mp (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right h⟩, fun ⟨hD, hΔ⟩ ↦ (hD.pow 6).mul hΔ⟩

/-- The `j`-invariant is a twist invariant: `j(E_{t,n}) = j(E)`. -/
theorem j_quadraticTwistOf [E.IsElliptic] (h : (E.quadraticTwistOf t n).IsElliptic) :
    (E.quadraticTwistOf t n).j = E.j := by
  have hΔ : E.Δ * ((E.Δ'⁻¹ : Aˣ) : A) = 1 := by
    rw [← coe_Δ']
    exact E.Δ'.mul_inv
  rw [j, j, Units.inv_mul_eq_iff_eq_mul, c₄_quadraticTwistOf, coe_Δ', Δ_quadraticTwistOf]
  linear_combination (-((t ^ 2 - 4 * n) ^ 6 * E.c₄ ^ 3)) * hΔ

/-- Twisting twice by the same parameters is twisting once by their composite: the quadratic
`x² - t²x + (2t²n - 4n²)` is *split*, with roots `t² - 2n` and `2n` — it represents the trivial
twist, which is why the double twist is isomorphic to `E` whenever `t² - 4n` is a unit. No
hypothesis. -/
theorem quadraticTwistOf_quadraticTwistOf :
    (E.quadraticTwistOf t n).quadraticTwistOf t n
      = E.quadraticTwistOf (t ^ 2) (2 * t ^ 2 * n - 4 * n ^ 2) := by
  ext <;> simp only [quadraticTwistOf] <;> ring

/-- Changing the parameters `(t, n)` — the trace and norm of a generator `θ` of a quadratic
extension — into the trace and norm `(at + 2b, b² + abt + a²n)` of another generator `aθ + b`
changes the quadratic twist by an explicit change of variables. Over a field the hypothesis is
`a ≠ 0` (`isUnit_iff_ne_zero`). -/
theorem exists_smul_quadraticTwistOf_eq {a : A} (b : A) (ha : IsUnit a) :
    ∃ C : VariableChange A, C • E.quadraticTwistOf t n
      = E.quadraticTwistOf (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) := by
  obtain ⟨v, hv⟩ := ha
  have hi : (↑v⁻¹ : A) * (v : A) = 1 := v.inv_mul
  refine ⟨⟨v⁻¹, 0, (↑v⁻¹ : A) * b * E.a₁,
    (↑v⁻¹ : A) * b * (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, ← hv] <;> grobner

/-- Twisting by a **split** quadratic `(x - r)(x - s)` is trivial up to isomorphism: the twist
by its trace and norm `(r + s, rs)` is a change of variables away from `E`, provided the
difference of the roots is a unit (that difference squared is the discriminant). -/
theorem exists_smul_eq_quadraticTwistOf_add_mul (r s : A) (h : IsUnit (s - r)) :
    ∃ C : VariableChange A, C • E = E.quadraticTwistOf (r + s) (r * s) := by
  -- twisting by `(1, 0)` is the identity, and the generator change `a = s - r`, `b = r` sends
  -- its parameters to `(r + s, rs)`; the two agree after polynomial normalisation.
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwistOf_eq 1 0 (a := s - r) r h
  rw [quadraticTwistOf_one_zero] at hC
  exact ⟨C, by convert hC using 2 <;> ring⟩

/-- Twisting twice by the same parameters `(t, n)` gives an isomorphic curve, provided the
discriminant `D = t² - 4n` is a unit. -/
theorem exists_smul_eq_quadraticTwistOf_quadraticTwistOf (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ C : VariableChange A, C • E = (E.quadraticTwistOf t n).quadraticTwistOf t n := by
  -- the split case at roots `t² - 2n` and `2n`: their difference is `-(t² - 4n)`, and their
  -- sum and product are the composite parameters of `quadraticTwistOf_quadraticTwistOf`.
  have hrs : IsUnit (2 * n - (t ^ 2 - 2 * n)) := by convert hD.neg using 1; ring
  obtain ⟨C, hC⟩ := E.exists_smul_eq_quadraticTwistOf_add_mul (t ^ 2 - 2 * n) (2 * n) hrs
  rw [quadraticTwistOf_quadraticTwistOf]
  exact ⟨C, by convert hC using 2 <;> ring⟩

end QuadraticTwistOfRing

section Field

variable {K : Type*} [Field K] (E : WeierstrassCurve K) (t n : K)

/-- Over a field, the quadratic twist of an elliptic curve is elliptic when the discriminant
`D = t² - 4n` of the twisting parameters is nonzero. This is the form the roadmap and the source
state; `isElliptic_quadraticTwistOf_iff` is the ring-level equivalence it specialises. -/
theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : t ^ 2 - 4 * n ≠ 0) :
    (E.quadraticTwistOf t n).IsElliptic :=
  (E.isElliptic_quadraticTwistOf_iff t n).mpr ⟨isUnit_iff_ne_zero.mpr hD, ‹E.IsElliptic›⟩

end Field

section QuadraticTwistBy

open Algebra.IsQuadraticExtension

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (E : WeierstrassCurve K)

variable [Algebra.IsQuadraticExtension K L]

/-- The quadratic twist by a generator `θ` of a quadratic extension `L/K` depends on the choice
of `θ` only up to isomorphism over `K`: all generators give isomorphic twists. This is what
makes the twist by the extension itself well posed. Separability is not needed — only the trace
and norm of `b + aθ`, which any quadratic extension supplies. -/
theorem exists_smul_quadraticTwistOf_trace_norm_eq {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K,
      C • E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)
        = E.quadraticTwistOf (Algebra.trace K L θ') (Algebra.norm K θ') := by
  obtain ⟨a, b, ha, rfl⟩ := exists_eq_algebraMap_add_algebraMap_mul K L hθ hθ'
  simp only [trace_algebraMap_add_algebraMap_mul K L a b θ,
    norm_algebraMap_add_algebraMap_mul K L a b θ]
  exact E.exists_smul_quadraticTwistOf_eq _ _ b (isUnit_iff_ne_zero.mpr ha)

variable [Algebra.IsSeparable K L]

/-- The twist of an elliptic curve by a generator of a separable quadratic extension is
elliptic: the discriminant `t² - 4n` of the generator's minimal polynomial is nonzero. -/
theorem isElliptic_quadraticTwistOf_trace_norm [E.IsElliptic] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    (E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)).IsElliptic :=
  E.isElliptic_quadraticTwistOf _ _ (discrim_ne_zero K L hθ)

end QuadraticTwistBy

end WeierstrassCurve

end
