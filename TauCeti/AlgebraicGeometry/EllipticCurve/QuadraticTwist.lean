/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.FieldTheory.Galois.Basic
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
* `WeierstrassCurve.quadraticTwist`: **the** quadratic twist of `E` by a *separable* quadratic
  extension `L/K`, the twist by the trace and norm of a generator chosen by
  `Algebra.IsQuadraticExtension.exists_discrim_ne_zero`. Separability is required: without it the
  extension could be purely inseparable, where the trace form vanishes and the model is singular
  for every `E`.
* `WeierstrassCurve.exists_quadraticTwist_eq`: elimination — the twist *equals* the twist by the
  trace and norm of some generator, so everything above about `quadraticTwistOf` transfers.
  `WeierstrassCurve.exists_smul_quadraticTwist_eq` adds that any other generator gives the same
  curve up to a change of variables.
* `WeierstrassCurve.isElliptic_quadraticTwist` (an `instance`) and
  `WeierstrassCurve.j_quadraticTwist`: the twist of an elliptic curve is elliptic, with the same
  `j`-invariant.
* `WeierstrassCurve.quadraticTwistOfTraceNormVariableChange`: the explicit change of variables over
  `L` carrying the twist by `θ` back to `E`, with
  `WeierstrassCurve.quadraticTwistOfTraceNormVariableChange_smul_baseChange` saying that it does
  so — the twist is an `L`-form of `E` — and
  `WeierstrassCurve.map_quadraticTwistOfTraceNormVariableChange` giving the Galois cocycle it
  carries:
  conjugating it by the nontrivial `σ ∈ Gal(L/K)` changes it by `negVariableChange`. The witness
  is a definition rather than an existential precisely because the cocycle identity is a
  statement about *this* change of variables and not about an arbitrary one carrying the twist
  to `E`. `WeierstrassCurve.exists_smul_quadraticTwist_baseChange_eq` is the corresponding
  statement for `quadraticTwist` itself, where the generator is the one chosen internally.

These are the `quadraticTwistOf` seeds of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5
(twists), pinned in that roadmap's `Suggested.lean`, together with the extension twist they make
well posed; the point isomorphism and the split-multiplicative-reduction theorem are later
milestones of the same layer and build on this file.

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

/-- The change of variables carrying the twist by the trace and norm of `aθ + b` back to the
twist by those of `θ`. It is the single witness behind every isomorphism in this file:
`exists_smul_quadraticTwistOf_eq` supplies its inverse, and
`quadraticTwistOfTraceNormVariableChange` is its base change at `(t, n) = (1, 0)`.

Stated over any commutative ring, since the identity it satisfies is polynomial; only
invertibility of `a` is needed.

Its four projections are `quadraticTwistOfVariableChange_u/_r/_s/_t`, as `negVariableChange` has
`negVariableChange_u/_r/_s/_t`: the body does not unfold outside this module, and the action
identity below does not pin the value down on its own, since composing with an automorphism of
the twisted curve gives another change of variables satisfying it. -/
def quadraticTwistOfVariableChange (u : Aˣ) (b : A) : VariableChange A :=
  ⟨u, 0, -(b * E.a₁), -((u : A) ^ 2 * b * (t ^ 2 - 4 * n) * E.a₃)⟩

@[simp] lemma quadraticTwistOfVariableChange_u (u : Aˣ) (b : A) :
    (E.quadraticTwistOfVariableChange t n u b).u = u := by
  simp only [quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfVariableChange_r (u : Aˣ) (b : A) :
    (E.quadraticTwistOfVariableChange t n u b).r = 0 := by
  simp only [quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfVariableChange_s (u : Aˣ) (b : A) :
    (E.quadraticTwistOfVariableChange t n u b).s = -(b * E.a₁) := by
  simp only [quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfVariableChange_t (u : Aˣ) (b : A) :
    (E.quadraticTwistOfVariableChange t n u b).t
      = -((u : A) ^ 2 * b * (t ^ 2 - 4 * n) * E.a₃) := by
  simp only [quadraticTwistOfVariableChange]

/-- **The defining identity of `quadraticTwistOfVariableChange`:** it carries the twist by the
transformed parameters `(ut + 2b, b² + ubt + u²n)` — those of the generator `uθ + b` — back to the
twist by `(t, n)` themselves. Every isomorphism in this file is an instance of this one. -/
@[simp]
theorem quadraticTwistOfVariableChange_smul (u : Aˣ) (b : A) :
    E.quadraticTwistOfVariableChange t n u b •
        E.quadraticTwistOf ((u : A) * t + 2 * b)
          (b ^ 2 + (u : A) * b * t + (u : A) ^ 2 * n)
      = E.quadraticTwistOf t n := by
  have hi : (↑u⁻¹ : A) * (u : A) = 1 := u.inv_mul
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOfVariableChange, quadraticTwistOf] <;> grobner

/-- Changing the parameters `(t, n)` — the trace and norm of a generator `θ` of a quadratic
extension — into the trace and norm `(at + 2b, b² + abt + a²n)` of another generator `aθ + b`
changes the quadratic twist by an explicit change of variables. Over a field the hypothesis is
`a ≠ 0` (`isUnit_iff_ne_zero`). -/
theorem exists_smul_quadraticTwistOf_eq {a : A} (b : A) (ha : IsUnit a) :
    ∃ C : VariableChange A, C • E.quadraticTwistOf t n
      = E.quadraticTwistOf (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) :=
  let ⟨v, hv⟩ := ha
  ⟨(E.quadraticTwistOfVariableChange t n v b)⁻¹, by
    rw [inv_smul_eq_iff, ← hv]
    exact (E.quadraticTwistOfVariableChange_smul t n v b).symm⟩

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

variable (K L) in
/-- The generator `quadraticTwist` picks does generate: nonzero discriminant characterises the
generators (`discrim_eq_zero_iff_mem_range_algebraMap`), and the chosen element has nonzero
discriminant. -/
private theorem choose_exists_discrim_notMem_range_algebraMap :
    (exists_discrim_ne_zero K L).choose ∉ Set.range (algebraMap K L) :=
  fun h => (exists_discrim_ne_zero K L).choose_spec
    ((discrim_eq_zero_iff_mem_range_algebraMap K L).mpr h)

/-- **The quadratic twist of `E` by the separable quadratic extension `L/K`**: the twist by the
trace and norm of a generator of `L/K`. The choice of generator is harmless —
`exists_quadraticTwist_eq` names one, and `exists_smul_quadraticTwist_eq` says every other gives
the same curve up to a change of variables over `K`.

Separability is not decoration. On a purely inseparable quadratic extension the trace form
vanishes, so `t = 0` and — in characteristic `2`, the only characteristic where such an extension
exists — the discriminant `D = t² - 4n` is `0`, and the model is singular for every `E` and
barely depends on `E`. This is a different failure from the one the module docstring gives for
refusing a twist-by-a-generator constructor, which is `(t, n) = (0, 1)` and so `D = -4`: there
the parameters cease to reflect the extension but the twist stays generically nonsingular. The
two coincide only in characteristic `2`. Choosing the generator by
`Algebra.IsQuadraticExtension.exists_discrim_ne_zero` rules this case out, so the *twist
parameters* never degenerate. That is all it can rule out: `E` is arbitrary here, so a singular
`E` still gives a singular twist. Nonsingularity of the result needs `E` elliptic too, which is
`isElliptic_quadraticTwist`. -/
noncomputable def quadraticTwist (E : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] : WeierstrassCurve K :=
  E.quadraticTwistOf (Algebra.trace K L (exists_discrim_ne_zero K L).choose)
    (Algebra.norm K (exists_discrim_ne_zero K L).choose)

variable (L) in
/-- **Elimination for `quadraticTwist`.** The twist *is* the twist by the trace and norm of some
generator of `L/K` — an equation, not merely an isomorphism, so everything proved about
`quadraticTwistOf` (the coefficients, `Δ`, `c₄`, `c₆`) transfers to `quadraticTwist`. Use it to
discharge a `quadraticTwist` goal. `L` is explicit because it occurs only inside the
existential. -/
theorem exists_quadraticTwist_eq :
    ∃ θ : L, θ ∉ Set.range (algebraMap K L) ∧
      E.quadraticTwist L = E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ) :=
  ⟨_, choose_exists_discrim_notMem_range_algebraMap K L, by simp only [quadraticTwist]⟩

/-- The twist of an elliptic curve by a separable quadratic extension is elliptic. Registered as
an instance so that downstream statements needing `[(E.quadraticTwist L).IsElliptic]` discharge it
by typeclass inference. -/
instance isElliptic_quadraticTwist [E.IsElliptic] : (E.quadraticTwist L).IsElliptic := by
  obtain ⟨θ, hθ, h⟩ := E.exists_quadraticTwist_eq L
  rw [h]
  exact E.isElliptic_quadraticTwistOf_trace_norm hθ

variable (L) in
/-- Twisting does not change the `j`-invariant. -/
@[simp]
theorem j_quadraticTwist [E.IsElliptic] : (E.quadraticTwist L).j = E.j := by
  obtain ⟨θ, hθ, h⟩ := E.exists_quadraticTwist_eq L
  -- `j` takes the `IsElliptic` instance of its argument, so `rw [h]` is a dependent rewrite and
  -- fails; `simp_rw` transfers the instance, as Mathlib's `WeierstrassCurve.j` docstring
  -- prescribes.
  simp_rw [h]
  exact E.j_quadraticTwistOf _ _ (E.isElliptic_quadraticTwistOf_trace_norm hθ)

/-- The twist by the extension agrees, up to a change of variables over `K`, with the twist by
*any* generator `θ`: the arbitrary choice in `quadraticTwist` is harmless. -/
theorem exists_smul_quadraticTwist_eq {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwist L
      = E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ) := by
  obtain ⟨θ', hθ', h⟩ := E.exists_quadraticTwist_eq L
  rw [h]
  exact E.exists_smul_quadraticTwistOf_trace_norm_eq hθ' hθ

/-- The change of variables over `L` that carries the twist by `θ` back to `E`. It rescales by
`σ θ - θ`, a square root of the discriminant of `θ`'s minimal polynomial, and shears and
translates by the amounts that clear the twisted model's `a₁` and `a₃` terms.

This is the witness of `quadraticTwistOfTraceNormVariableChange_smul_baseChange`; it is a
definition rather than an existential because `map_quadraticTwistOfTraceNormVariableChange` is a
statement about *this* change of variables, and does not hold of an arbitrary one carrying the
twist to `E` — two such differ by an automorphism of `E`, which the cocycle identity does not
tolerate. -/
def quadraticTwistOfTraceNormVariableChange {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : VariableChange L :=
  (E.baseChange L).quadraticTwistOfVariableChange 1 0
    (Units.mk0 (σ θ - θ) (Algebra.IsQuadraticExtension.apply_sub_self_ne_zero K L hσ hθ)) θ

@[simp] lemma quadraticTwistOfTraceNormVariableChange_u {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistOfTraceNormVariableChange hθ hσ).u
      = Units.mk0 (σ θ - θ) (Algebra.IsQuadraticExtension.apply_sub_self_ne_zero K L hσ hθ) := by
  simp only [quadraticTwistOfTraceNormVariableChange, quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfTraceNormVariableChange_r {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistOfTraceNormVariableChange hθ hσ).r = 0 := by
  simp only [quadraticTwistOfTraceNormVariableChange, quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfTraceNormVariableChange_s {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistOfTraceNormVariableChange hθ hσ).s = -(θ * (E.baseChange L).a₁) := by
  simp only [quadraticTwistOfTraceNormVariableChange, quadraticTwistOfVariableChange]

@[simp] lemma quadraticTwistOfTraceNormVariableChange_t {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistOfTraceNormVariableChange hθ hσ).t
      = -((σ θ - θ) ^ 2 * θ * (E.baseChange L).a₃) := by
  simp only [quadraticTwistOfTraceNormVariableChange, quadraticTwistOfVariableChange,
    Units.val_mk0]
  ring

/-- **The twist becomes isomorphic to `E` over `L`**, by the explicit change of variables
`quadraticTwistOfTraceNormVariableChange`. Over a field, isomorphisms of Weierstrass curves are
exactly the admissible changes of variables, acting via `•`. -/
-- not `@[simp]`: `baseChange_quadraticTwistOf` is itself a simp lemma and rewrites this
-- left-hand side first, so `simpNF` reports the statement is not in simp-normal form and the
-- lemma could never fire. Consumers rewrite with it explicitly, as
-- `exists_smul_quadraticTwist_baseChange_eq` does.
theorem quadraticTwistOfTraceNormVariableChange_smul_baseChange {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    E.quadraticTwistOfTraceNormVariableChange hθ hσ •
        (E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)).baseChange L
      = E.baseChange L := by
  have hT : algebraMap K L (Algebra.trace K L θ) = θ + σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ θ
  have hN : algebraMap K L (Algebra.norm K θ) = θ * σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul K L hσ θ
  -- the twist parameters of `θ` are those of the generator `(σ θ - θ) · 1 + θ`,
  -- taken at `(t, n) = (1, 0)`, where the twist is `E` itself
  have h := (E.baseChange L).quadraticTwistOfVariableChange_smul 1 0
    (Units.mk0 (σ θ - θ) (Algebra.IsQuadraticExtension.apply_sub_self_ne_zero K L hσ hθ)) θ
  rw [quadraticTwistOf_one_zero] at h
  rw [baseChange_quadraticTwistOf, hT, hN]
  convert h using 3 <;> first | rfl | (simp only [Units.val_mk0]; ring)

/-- **The Galois cocycle carried by that isomorphism.** Conjugating
`quadraticTwistOfTraceNormVariableChange` by the nontrivial `σ ∈ Gal(L/K)` changes it by
`negVariableChange`, the change of variables `[-1]`: this is the cocycle identity for
`H¹(Gal(L/K), Aut E)`.

It does **not** say the class is nontrivial. `E` here is an arbitrary Weierstrass curve, and when
`negVariableChange = 1` — a singular curve in characteristic 2 with `a₁ = a₃ = 0`, say — the
identity below is plain equivariance. Nontriviality needs hypotheses this statement does not
carry. -/
@[simp]
theorem map_quadraticTwistOfTraceNormVariableChange {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistOfTraceNormVariableChange hθ hσ).map (σ : L →+* L)
      = (E.baseChange L).negVariableChange * E.quadraticTwistOfTraceNormVariableChange hθ hσ := by
  have hσσ : σ (σ θ) = θ := by
    rw [← AlgEquiv.mul_apply, Algebra.IsQuadraticExtension.algEquiv_mul_self K L σ,
      AlgEquiv.one_apply]
  ext <;>
    -- a `public section` leaves `negVariableChange`'s body unexposed here, so the proof goes
    -- through its accessor lemmas rather than unfolding the definition
    simp only [quadraticTwistOfTraceNormVariableChange, quadraticTwistOfVariableChange,
      VariableChange.map, VariableChange.mul_def,
      negVariableChange_u, negVariableChange_r, negVariableChange_s, negVariableChange_t,
      Units.coe_map, Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0,
      MonoidHom.coe_coe, RingHom.coe_coe,
      map_neg, map_mul, map_pow, map_sub, map_zero, map_one, map_a₁, map_a₃, baseChange,
      σ.commutes, hσσ] <;>
    ring

variable (L) in
/-- **The quadratic twist becomes isomorphic to `E` after base change to `L`.** Over a field,
isomorphisms of Weierstrass curves are exactly the admissible changes of variables
`WeierstrassCurve.VariableChange`, acting via `•`. -/
theorem exists_smul_quadraticTwist_baseChange_eq :
    ∃ C : VariableChange L, C • (E.quadraticTwist L).baseChange L = E.baseChange L := by
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L
  -- bridge the generator chosen inside `quadraticTwist` to `θ`, base changed to `L`
  obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq hθ
  exact ⟨E.quadraticTwistOfTraceNormVariableChange hθ hσ * C₀.baseChange L, by
    rw [mul_smul, baseChange_smul_baseChange, hC₀,
      E.quadraticTwistOfTraceNormVariableChange_smul_baseChange hθ hσ]⟩

end QuadraticTwistBy

end WeierstrassCurve

end
