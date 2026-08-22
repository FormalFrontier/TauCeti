/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Aut
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial
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
* `WeierstrassCurve.nodePolynomial_coeff_zero_quadraticTwistOf`: the constant coefficient of
  `nodePolynomial` is the one quantity here that does **not** simply scale by a power of
  `t² - 4n`; it acquires `+ D² n a₁² c₄`. Splitting of the node polynomial is not determined by
  this coefficient alone, so this is a record of how it transforms, not a reduction statement.
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
* `WeierstrassCurve.quadraticTwistVariableChange`: the same change of variables in the other
  direction, carrying `E` to the twist, at the generator `quadraticTwist` chooses internally —
  the inverse of the previous one, with `WeierstrassCurve.quadraticTwistVariableChange_smul` and the
  cocycle `WeierstrassCurve.map_quadraticTwistVariableChange`, where the `negVariableChange` factor
  sits on the right because inverting a product reverses it.
* `WeierstrassCurve.not_exists_smul_quadraticTwist_eq` and
  `WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist`: **the classification**, for
  `j ∉ {0, 1728}`. The twist is not `K`-isomorphic to `E`, and any curve becoming isomorphic to
  `E` over `L` is `K`-isomorphic to one of the two. This is where the cocycle is used: forms are
  classified by `H¹(Gal(L/K), Aut Eᴸ) = Hom(ℤ/2, {±1})`, of order two, and the two branches of
  the proof are its two classes.

These are the `quadraticTwistOf` seeds of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5
(twists), pinned in that roadmap's `Suggested.lean`, together with the extension twist they make
well posed, the classification of the `L`-forms that the cocycle delivers, and the point
isomorphism `quadraticTwistPointEquiv` that `quadraticTwistVariableChange` induces; the
split-multiplicative-reduction theorem is a later milestone of the same layer and builds on this
file.

## The point isomorphism

Over any field `M` in a tower `K ⊆ L ⊆ M`, the base change of `quadraticTwistVariableChange`
carries `E` to its twist (`quadraticTwistVariableChange_smul_baseChange`) and satisfies the
cocycle identity (`map_quadraticTwistVariableChange_baseChange`). Transporting along it gives
`quadraticTwistPointEquiv : ((E.quadraticTwist L)⁄M).Point ≃+ (E⁄M).Point`, with
`quadraticTwistPointEquiv_some` the coordinate equation a consumer needs. It is natural in `M`
(`quadraticTwistPointEquiv_map`) and **anti-equivariant** for the Galois elements that move `L`
(`quadraticTwistPointEquiv_map_eq_neg_map_of_not_fixed`): that sign is what makes the twist a
twist. `quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map` packages the two cases as
`φ(σP) = χ(σ|_L) • σ(φP)`, uniformly in `σ`, where `χ` is
`Algebra.IsQuadraticExtension.quadraticCharacter` — the
`Gal(L/K) →* ℤˣ` sending the nontrivial automorphism to `-1`. That is the canonical form of the
statement: the isomorphism is defined over `L` rather than over `K`, and `χ` measures precisely
that failure.

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

/-- **The constant coefficient of the node polynomial, under twisting.** Unlike `b₂`, `b₄`, `b₆`,
`c₄`, `c₆` and `Δ`, which all simply scale by a power of `D = t² - 4n`, this coefficient picks up
an extra `+ D² n a₁² c₄`. That term vanishes when any of `a₁`, `n`, `c₄` or `D` does — and, over a
general commutative ring, it can vanish from zero divisors without any factor being zero.

Whether the node polynomial splits over the residue field is what distinguishes split from
non-split multiplicative reduction, so a twist can change that behaviour — but splitting is not
determined by this coefficient alone, and this lemma establishes no reduction statement by itself.
It records the coefficient's transformation, which such an argument would use (for instance in the
characteristic-two Artin–Schreier calculation), and nothing more. -/
@[simp]
theorem nodePolynomial_coeff_zero_quadraticTwistOf :
    (E.quadraticTwistOf t n).nodePolynomial.coeff 0
      = (t ^ 2 - 4 * n) ^ 3 * E.nodePolynomial.coeff 0
        + (t ^ 2 - 4 * n) ^ 2 * n * E.a₁ ^ 2 * E.c₄ := by
  simp only [nodePolynomial_coeff_zero, b₆_quadraticTwistOf, b₂_quadraticTwistOf,
    b₄_quadraticTwistOf, c₄_quadraticTwistOf, a₂_quadraticTwistOf]
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
  obtain ⟨a, b, ha, rfl⟩ := exists_ne_zero_eq_algebraMap_add_algebraMap_mul K L hθ hθ'
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

variable (L) in
/-- **The change of variables over `L` carrying `E` to its quadratic twist.** It is the inverse of
`quadraticTwistOfTraceNormVariableChange`, taken at the generator `quadraticTwist` chooses
internally, so no bridging change of variables is needed: at that generator the twist *is*
`quadraticTwistOf` of its trace and norm, by definition.

Naming an explicit witness rather than an existential is what makes the cocycle identity
`map_quadraticTwistVariableChange` statable: that identity is false of an arbitrary change of
variables
carrying `E` to the twist, since two such differ by an automorphism of the twist. -/
noncomputable def quadraticTwistVariableChange : VariableChange L :=
  (E.quadraticTwistOfTraceNormVariableChange
    (choose_exists_discrim_notMem_range_algebraMap K L)
    (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec)⁻¹

variable (L) in
/-- **`quadraticTwistVariableChange` does carry `E` to the twist**, after base change to `L`. -/
@[simp]
theorem quadraticTwistVariableChange_smul :
    E.quadraticTwistVariableChange L • E.baseChange L = (E.quadraticTwist L).baseChange L := by
  rw [quadraticTwistVariableChange, inv_smul_eq_iff]
  exact (E.quadraticTwistOfTraceNormVariableChange_smul_baseChange _ _).symm

variable (L) in
/-- **The defining cocycle of the quadratic twist.** The nontrivial `σ ∈ Gal(L/K)` conjugates
`quadraticTwistVariableChange` by the automorphism `[-1]` of `E`. This is the mirror of
`map_quadraticTwistOfTraceNormVariableChange`, and the factor lands on the *right* here because
inverting a product reverses it and `[-1]` is its own inverse (`negVariableChange_inv`).

As there, this is the cocycle identity and not a nontriviality claim. -/
@[simp]
theorem map_quadraticTwistVariableChange {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistVariableChange L).map (σ : L →+* L)
      = E.quadraticTwistVariableChange L * (E.baseChange L).negVariableChange := by
  set σ₀ := (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose with hσ₀def
  have hσ₀ : σ₀ ≠ 1 := (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec
  -- `Gal(L/K)` has order two, so `σ` is the automorphism chosen inside
  -- `quadraticTwistVariableChange`
  obtain rfl : σ = σ₀ :=
    (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ₀ σ).resolve_left hσ
  rw [quadraticTwistVariableChange, VariableChange.map_inv,
    E.map_quadraticTwistOfTraceNormVariableChange,
    mul_inv_rev,
    (E.baseChange L).negVariableChange_inv]

section Classification

variable [E.IsElliptic]

variable (L) in
/-- **The quadratic twist is not isomorphic to `E` over `K`**, when `j(E) ∉ {0, 1728}`. Twisting is
a genuinely nontrivial operation: this is what `map_quadraticTwistOfTraceNormVariableChange`
deliberately stopped short of claiming, and the `j`-hypotheses are exactly what it lacked.

What the `j`-hypotheses buy is `Aut(Eᴸ) = {±1}`
(`eq_one_or_eq_negVariableChange_map`). At `j ∈ {0, 1728}` the automorphism group can be
strictly larger, and the statement is not claimed there; nor is a counterexample asserted. -/
theorem not_exists_smul_quadraticTwist_eq (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    ¬∃ C : VariableChange K, C • E.quadraticTwist L = E := by
  rintro ⟨CK, hCK⟩
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  have hinj := FaithfulSMul.algebraMap_injective K L
  -- needed by `negVariableChange_ne_one` at the end
  have : (E.baseChange L).IsElliptic := inferInstanceAs ((E.map (algebraMap K L)).IsElliptic)
  -- `b := CKᴸ · T` fixes `Eᴸ`, where `T` is the change of variables carrying `Eᴸ` to the twist
  set b := CK.baseChange L * E.quadraticTwistVariableChange L with hb
  have haut : b • E.baseChange L = E.baseChange L := by
    rw [hb, mul_smul, E.quadraticTwistVariableChange_smul L, baseChange_smul_baseChange, hCK]
  -- `σ` fixes the base change of a `K`-change and multiplies `T` by `[-1]`, so `σb = b · [-1]`
  have hCKmap : (CK.baseChange L).map (σ : L →+* L) = CK.baseChange L :=
    VariableChange.map_baseChange (C := CK) (σ : L →ₐ[K] L)
  have hnegmap : (E.baseChange L).negVariableChange.map (σ : L →+* L)
      = (E.baseChange L).negVariableChange :=
    E.negVariableChange_baseChange_map L (σ : L →ₐ[K] L)
  have hbmap : b.map (σ : L →+* L) = b * (E.baseChange L).negVariableChange := by
    rw [hb, VariableChange.map_mul, hCKmap, E.map_quadraticTwistVariableChange L hσ, mul_assoc]
  -- both values the dichotomy allows for `b` force `[-1] = 1`
  apply (E.baseChange L).negVariableChange_ne_one
  -- the dichotomy is stated for `E.map (algebraMap K L)`, which is `E.baseChange L` by definition
  have hEL : E.map (algebraMap K L) = E.baseChange L := rfl
  rcases E.eq_one_or_eq_negVariableChange_map (f := algebraMap K L) hinj hj₀ hj₁₇₂₈ haut with
    hcase | hcase
  on_goal 2 => rw [hEL] at hcase
  · rw [hcase, VariableChange.map_one, one_mul] at hbmap
    exact hbmap.symm
  · rw [hcase, hnegmap, (E.baseChange L).negVariableChange_mul_self] at hbmap
    exact hbmap

omit [E.IsElliptic] in
/-- **An `L`-isomorphism `E'ᴸ ≅ Eᴸ` whose Galois conjugate differs from it by `[-1]` makes `E'`
`K`-isomorphic to the quadratic twist of `E`.** -/
private theorem exists_smul_eq_quadraticTwist_of_map_eq_negVariableChange_mul
    {E' : WeierstrassCurve K} {ρ : VariableChange L}
    (hρ : ρ • E'.baseChange L = E.baseChange L) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (hρmap : ρ.map (σ : L →+* L) = (E.baseChange L).negVariableChange * ρ) :
    ∃ C : VariableChange K, C • E' = E.quadraticTwist L := by
  -- the twist's own change of variables carries the opposite cocycle, so `T · ρ` is
  -- `σ`-invariant and descends to `K`
  have hχiso : (E.quadraticTwistVariableChange L * ρ) • E'.baseChange L
      = (E.quadraticTwist L).baseChange L := by
    rw [mul_smul, hρ, E.quadraticTwistVariableChange_smul L]
  have hχinv : (E.quadraticTwistVariableChange L * ρ).map (σ : L →+* L)
      = E.quadraticTwistVariableChange L * ρ := by
    rw [VariableChange.map_mul, E.map_quadraticTwistVariableChange L hσ, hρmap, mul_assoc,
      ← mul_assoc (E.baseChange L).negVariableChange,
      (E.baseChange L).negVariableChange_mul_self, one_mul]
  obtain ⟨χK, hχK⟩ := VariableChange.exists_baseChange_eq_of_map_eq L hσ hχinv
  exact ⟨χK, smul_eq_of_baseChange_smul_eq L (FaithfulSMul.algebraMap_injective K L) χK
    (by rw [hχK]; exact hχiso)⟩

variable (L) in
/-- **Classification of the forms of `E` split by `L/K`, for `j(E) ∉ {0, 1728}`.** A curve over `K`
that becomes isomorphic to `E` over `L` is isomorphic over `K` either to `E` or to its quadratic
twist by `L` — and, by `not_exists_smul_quadraticTwist_eq`, those two alternatives are distinct.

There are exactly two alternatives because such forms are classified by
`H¹(Gal(L/K), Aut Eᴸ) = Hom(ℤ/2, {±1})`, a group of order two. The `j`-hypotheses are what give
`Aut Eᴸ = {±1}` (`eq_one_or_eq_negVariableChange_map`); for the excluded `j` the
automorphism group can be larger and there can be more forms. -/
theorem exists_smul_eq_or_exists_smul_eq_quadraticTwist (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728)
    (E' : WeierstrassCurve K)
    (h : ∃ C : VariableChange L, C • E'.baseChange L = E.baseChange L) :
    (∃ C : VariableChange K, C • E' = E) ∨
      ∃ C : VariableChange K, C • E' = E.quadraticTwist L := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  have hinj := FaithfulSMul.algebraMap_injective K L
  -- the Galois conjugate of `ρ` is again an isomorphism `E'ᴸ ≅ Eᴸ`, so `σρ · ρ⁻¹` fixes `Eᴸ`
  have hσρ : (ρ.map (σ : L →+* L)) • E'.baseChange L = E.baseChange L :=
    map_smul_baseChange_eq L (σ : L →ₐ[K] L) hρ
  have hρinv : ρ⁻¹ • E.baseChange L = E'.baseChange L := by rw [← hρ, inv_smul_smul]
  have hb : (ρ.map (σ : L →+* L) * ρ⁻¹) • E.baseChange L = E.baseChange L := by
    rw [mul_smul, hρinv, hσρ]
  rcases E.eq_one_or_eq_negVariableChange_map (f := algebraMap K L) hinj hj₀ hj₁₇₂₈ hb with
    hbcase | hbcase
  · -- trivial cocycle: `ρ` is `σ`-invariant, so it descends and `E' ≅ E` over `K`
    left
    obtain ⟨ρK, hρK⟩ :=
      VariableChange.exists_baseChange_eq_of_map_eq L hσ (mul_inv_eq_one.mp hbcase)
    exact ⟨ρK, smul_eq_of_baseChange_smul_eq L hinj ρK (by rw [hρK]; exact hρ)⟩
  · -- nontrivial cocycle: `E'` is the twist
    exact .inr (E.exists_smul_eq_quadraticTwist_of_map_eq_negVariableChange_mul hρ hσ
      (mul_inv_eq_iff_eq_mul.mp hbcase))

end Classification

/-! ### The isomorphism on points and its Galois anti-equivariance -/

section PointEquiv

/-! The curve-level identity below is about base change alone, so it asks only for a commutative
`L`-algebra. Everything after it — the Galois cocycle, the isomorphism on points, and the
equivariance statements — genuinely needs `M` to be a field, and lives in the section after. -/

section BaseChange

variable (M : Type*) [CommRing M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

variable (L) in
/-- **The change of variables carries `E` to its twist over every commutative `L`-algebra `M`**,
not just over `L`: `quadraticTwistVariableChange_smul` base changed along `L → M`. -/
theorem quadraticTwistVariableChange_smul_baseChange :
    (E.quadraticTwistVariableChange L).baseChange M • E.baseChange M
      = (E.quadraticTwist L).baseChange M := by
  have hb : ∀ W : WeierstrassCurve K, (W.baseChange L).baseChange M = W.baseChange M :=
    fun W ↦ by simpa [baseChange] using W.map_baseChange (IsScalarTower.toAlgHom K L M)
  rw [← hb E, baseChange_smul_baseChange, quadraticTwistVariableChange_smul, hb]

end BaseChange

-- `M` is any extension field of `L` compatible with the `K`-algebra tower; e.g. `L` itself.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **The twist's defining cocycle over `M`.** Applying any `σ ∈ Aut(M/K)` that does not fix `L`
pointwise multiplies the base change of `quadraticTwistVariableChange` on the right by the
automorphism `[-1]` of `E`.
This is `map_quadraticTwistVariableChange` base changed to `M`: `σ` restricts to the nontrivial
element of `Gal(L/K)` precisely because it moves `L`, which is what
`AlgEquiv.restrictNormal_eq_one_iff_algebraMap` records. -/
theorem map_quadraticTwistVariableChange_baseChange {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    ((E.quadraticTwistVariableChange L).baseChange M).map (σ : M →+* M)
      = (E.quadraticTwistVariableChange L).baseChange M * (E.baseChange M).negVariableChange := by
  obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
  have hres : σ.restrictNormal L = σ₀ :=
    (algEquiv_eq_one_or_eq K L hσ₀ _).resolve_left
      (fun h ↦ hσ ((AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M σ).mp h))
  have hcomp : (σ : M →+* M).comp (algebraMap L M) = (algebraMap L M).comp (σ₀ : L →+* L) := by
    ext l
    have h := (AlgEquiv.restrictNormal_commutes σ L l).symm
    rw [hres] at h
    simpa using h
  have hb : ∀ W : WeierstrassCurve K, (W.baseChange L).map (algebraMap L M) = W.baseChange M :=
    fun W ↦ by simpa using W.map_baseChange (IsScalarTower.toAlgHom K L M)
  rw [VariableChange.baseChange, VariableChange.map_map, hcomp, ← VariableChange.map_map,
    map_quadraticTwistVariableChange (E := E) (L := L) hσ₀, VariableChange.map_mul,
    ← VariableChange.baseChange,
    ← negVariableChange_map, hb]

variable [E.IsElliptic] [DecidableEq M]

variable (L) in
/-- **The isomorphism `Eᴸ(M) ≅ E(M)` on `M`-points**, for any field `M` in a tower `K ⊆ L ⊆ M`:
the base change to `M` of the change of variables carrying `E` to its twist over `L`. It is
natural in `M` (`quadraticTwistPointEquiv_map`) and anti-equivariant for the Galois elements that
move `L` (`quadraticTwistPointEquiv_map_eq_neg_map_of_not_fixed`);
`quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map` bundles those two branches into a
single statement, uniform in `σ`, twisted by the quadratic character of `L/K`.

Like the twist itself this is well defined only up to an `L`-automorphism of `E` — generically up
to sign — and this definition makes one arbitrary choice, consistently across all `M`. -/
noncomputable def quadraticTwistPointEquiv :
    ((E.quadraticTwist L).baseChange M).toAffine.Point ≃+ (E.baseChange M).toAffine.Point :=
  have : (E.baseChange M).IsElliptic := inferInstanceAs (E.map (algebraMap K M)).IsElliptic
  (AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.toAffine.Point)
      (E.quadraticTwistVariableChange_smul_baseChange L M).symm).trans
    (Affine.Point.equivVariableChange (E.baseChange M)
      ((E.quadraticTwistVariableChange L).baseChange M))

variable (L) in
/-- **What the isomorphism does to a point given by coordinates.** The change of variables acting
is `quadraticTwistVariableChange` base changed to `M`. -/
@[simp] lemma quadraticTwistPointEquiv_some {x y : M}
    (h : ((E.quadraticTwist L).baseChange M).toAffine.Nonsingular x y) :
    E.quadraticTwistPointEquiv L M (.some x y h)
      = .some ((((E.quadraticTwistVariableChange L).baseChange M).u : M) ^ 2 * x
            + ((E.quadraticTwistVariableChange L).baseChange M).r)
          ((((E.quadraticTwistVariableChange L).baseChange M).u : M) ^ 3 * y
            + (((E.quadraticTwistVariableChange L).baseChange M).u : M) ^ 2
              * ((E.quadraticTwistVariableChange L).baseChange M).s * x
            + ((E.quadraticTwistVariableChange L).baseChange M).t)
          ((Affine.variableChange_nonsingular (E.baseChange M)
            ((E.quadraticTwistVariableChange L).baseChange M) x y).mpr
              ((E.quadraticTwistVariableChange_smul_baseChange L M).symm ▸ h)) := by
  rw [quadraticTwistPointEquiv, AddEquiv.trans_apply, Affine.Point.cast_some,
    Affine.Point.equivVariableChange_some]

/-- **What the inverse isomorphism does to a point given by coordinates.** It is the map induced
by the inverse of the base-changed change of variables. -/
@[simp] lemma quadraticTwistPointEquiv_symm_some {x y : M}
    (h : (E.baseChange M).toAffine.Nonsingular x y) :
    (E.quadraticTwistPointEquiv L M).symm (.some x y h)
      = .some (((((E.quadraticTwistVariableChange L).baseChange M)⁻¹).u : M) ^ 2 * x
            + (((E.quadraticTwistVariableChange L).baseChange M)⁻¹).r)
          (((((E.quadraticTwistVariableChange L).baseChange M)⁻¹).u : M) ^ 3 * y
            + ((((E.quadraticTwistVariableChange L).baseChange M)⁻¹).u : M) ^ 2
              * (((E.quadraticTwistVariableChange L).baseChange M)⁻¹).s * x
            + (((E.quadraticTwistVariableChange L).baseChange M)⁻¹).t)
          (by
            rw [← E.quadraticTwistVariableChange_smul_baseChange L M]
            exact (Affine.variableChange_nonsingular
              (((E.quadraticTwistVariableChange L).baseChange M) • E.baseChange M)
              (((E.quadraticTwistVariableChange L).baseChange M)⁻¹) x y).mpr
                ((inv_smul_smul ((E.quadraticTwistVariableChange L).baseChange M)
                  (E.baseChange M)).symm ▸ h)) := by
  rw [AddEquiv.symm_apply_eq, quadraticTwistPointEquiv, AddEquiv.trans_apply,
    Affine.Point.cast_some, Affine.Point.equivVariableChange_some, Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩ <;>
    simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val] <;> field

/-- **Naturality of `quadraticTwistPointEquiv` in `M`.** The isomorphisms on `M`-points over
varying `M ⊇ L` all come from one isomorphism of curves over `L`, so they commute with the maps on
points induced by any `L`-algebra homomorphism. -/
@[simp]
theorem quadraticTwistPointEquiv_map {N : Type*} [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N] [DecidableEq N] (f : M →ₐ[L] N)
    (P : ((E.quadraticTwist L).baseChange M).toAffine.Point) :
    E.quadraticTwistPointEquiv L N (Affine.Point.map f P)
      = Affine.Point.map f (E.quadraticTwistPointEquiv L M P) := by
  have hu : (((E.quadraticTwistVariableChange L).baseChange N).u : N)
      = f (((E.quadraticTwistVariableChange L).baseChange M).u : M) := by
    simp only [VariableChange.baseChange, VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact (f.commutes _).symm
  have hr : ((E.quadraticTwistVariableChange L).baseChange N).r
      = f ((E.quadraticTwistVariableChange L).baseChange M).r := (f.commutes _).symm
  have hs : ((E.quadraticTwistVariableChange L).baseChange N).s
      = f ((E.quadraticTwistVariableChange L).baseChange M).s := (f.commutes _).symm
  have ht : ((E.quadraticTwistVariableChange L).baseChange N).t
      = f ((E.quadraticTwistVariableChange L).baseChange M).t := (f.commutes _).symm
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv_some, Affine.Point.map_some,
      Affine.Point.some.injEq]
    constructor
    · simp only [map_add, map_mul, map_pow, hu, hr]
    · simp only [map_add, map_mul, map_pow, hu, hs, ht]


variable (L) in
/-- **Anti-equivariance**: if `σ ∈ Aut(M/K)` does not fix `L` pointwise, transporting its action
through `Eᴸ(M) ≅ E(M)` gives minus its action. -/
@[simp]
theorem quadraticTwistPointEquiv_map_eq_neg_map_of_not_fixed {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x)
    (P : ((E.quadraticTwist L).baseChange M).toAffine.Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P)
      = -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  have hM := map_quadraticTwistVariableChange_baseChange (E := E) (L := L) (M := M) hσ
  -- the four components of the cocycle identity, read off by `mul_negVariableChange_u/_r/_s/_t`
  have hu : σ.toAlgHom (((E.quadraticTwistVariableChange L).baseChange M).u : M)
      = -(((E.quadraticTwistVariableChange L).baseChange M).u : M) := by
    simpa using congrArg (fun C ↦ (VariableChange.u C : M)) hM
  have hr : σ.toAlgHom ((E.quadraticTwistVariableChange L).baseChange M).r
      = ((E.quadraticTwistVariableChange L).baseChange M).r := by
    simpa using congrArg VariableChange.r hM
  have hs : σ.toAlgHom ((E.quadraticTwistVariableChange L).baseChange M).s
      = -((E.quadraticTwistVariableChange L).baseChange M).s - (E.baseChange M).a₁ := by
    simpa using congrArg VariableChange.s hM
  have ht : σ.toAlgHom ((E.quadraticTwistVariableChange L).baseChange M).t
      = -((E.quadraticTwistVariableChange L).baseChange M).t
        - ((E.quadraticTwistVariableChange L).baseChange M).r * (E.baseChange M).a₁
        - (E.baseChange M).a₃ := by
    simpa using congrArg VariableChange.t hM
  rcases P with _ | ⟨x, y, hns⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv_some, Affine.Point.map_some, Affine.Point.neg_some,
      Affine.Point.some.injEq]
    refine ⟨?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, hu, hr]; ring
    · simp only [Affine.negY, map_add, map_mul, map_pow, hu, hr, hs, ht]; ring

variable (L) in
/-- **Galois equivariance of the point isomorphism, twisted by the quadratic character.** For
*every* `σ ∈ Aut(M/K)`, transporting the action of `σ` through `Eᴸ(M) ≅ E(M)` multiplies it by
`χ(σ|_L) = ±1`, the quadratic character of `L/K`. This is the uniform statement that
`quadraticTwistPointEquiv_map` (the `σ|_L = 1` branch, where the isomorphism is `L`-linear) and
`quadraticTwistPointEquiv_map_eq_neg_map_of_not_fixed` (the moved branch, where it is
anti-equivariant) together assert: the isomorphism is defined over `L`, not over `K`, and the
character measures exactly that failure. -/
theorem quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map (σ : M ≃ₐ[K] M)
    (P : ((E.quadraticTwist L).baseChange M).toAffine.Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P)
      = (Algebra.IsQuadraticExtension.quadraticCharacter K L (σ.restrictNormal L) : ℤ) •
          Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  by_cases hσ : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x
  · -- `σ` fixes `L` pointwise, so it *is* an `L`-algebra map and naturality applies verbatim
    have key := quadraticTwistPointEquiv_map (E := E) (L := L) (M := M) (N := M)
      (f := ({ σ.toAlgHom.toRingHom with commutes' := hσ } : M →ₐ[L] M)) (P := P)
    rw [(AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M σ).2 hσ, map_one]
    exact_mod_cast key
  · rw [Algebra.IsQuadraticExtension.quadraticCharacter_eq_neg_one_of_ne_one _ _
      fun h ↦ hσ ((AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M σ).1 h)]
    simpa using quadraticTwistPointEquiv_map_eq_neg_map_of_not_fixed
      (E := E) (L := L) (M := M) (σ := σ) hσ P

end PointEquiv

end QuadraticTwistBy

end WeierstrassCurve

end
