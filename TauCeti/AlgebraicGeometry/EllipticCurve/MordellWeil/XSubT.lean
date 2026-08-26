/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.LinearCombination
public import TauCeti.Algebra.Group.MapMulMulEqOne
public import TauCeti.Algebra.Polynomial.LinearFactor
public import TauCeti.RingTheory.AdjoinRoot

/-!
# The `x - T` map of an elliptic curve into its étale algebra

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, and let `A := K[X]⧸⟨f⟩` be the étale algebra of `f`. The **descent map**,
or `x - T` map, sends a point of `W` to the square class of `x - T` in `A`, where `T` is the
class of `X`. It is the engine of the descent computing `E(K)/2E(K)`: its kernel is exactly
`2E(K)`, so `E(K)/2E(K)` embeds into a group of square classes, which is finite under the
finiteness hypotheses of the weak Mordell-Weil theorem.

The subtlety is at the `2`-torsion. If `f x ≠ 0` then `x - T` is already a unit of `A`, but at a
root `x` of `f` the element `x - T` is a zero divisor, and the map instead returns the class of
the corrected representative `x - T + fCofactor x`. Adding `fCofactor x` changes nothing modulo
`fCofactor x`, where the element still agrees with `x - T`; at the remaining factor, where
`x - T` vanishes, it takes the value `f' x`, which is nonzero because `f` is separable. That is
what makes the corrected element a unit. Both branches are packaged in `μX`, and `μ₀` extends
`μX` by sending the point at infinity to `1`.

## Main definitions

* `WeierstrassCurve.Affine.μX`, `WeierstrassCurve.Affine.μ₀`: the `x - T` map, first on
  `x`-coordinates and then on points, as a plain function.
* `WeierstrassCurve.Affine.μ`: the same map upgraded to a group homomorphism
  `Multiplicative W.Point →* W.M`.

## Main results

* `WeierstrassCurve.Affine.μ₀_mul_mul_eq_one_of_add_add_eq_zero`: the square classes of three
  collinear points multiply to `1`. This is the substance of the file, and the multiplicativity
  that makes `μ` a homomorphism; it is proved by exhibiting an explicit square root in each of
  the ways the three points can meet the `2`-torsion.
* `WeierstrassCurve.Affine.exists_eq_two_smul_iff`: a point is divisible by `2` exactly when an
  explicit polynomial identity has a solution. This is the bridge from the `x - T` map to the
  kernel computation below.
* `WeierstrassCurve.Affine.ker_μ_eq`: **the kernel of `μ` is exactly `2 • W(K)`**. This is the
  injectivity half of the descent, and the reason `W(K)/2W(K)` embeds into `W.M`. A point in the
  kernel is exhibited as `2 • P` by solving the identity of `exists_eq_two_smul_iff` from a square
  root of `x - T`, in two cases according to whether the `x`-coordinate is a root of `f`; the
  point-wise statement is `WeierstrassCurve.Affine.eq_two_smul_of_μ_eq_one`.

`WeierstrassCurve.Affine.A` is the étale algebra and `WeierstrassCurve.Affine.M` its group of
square classes of units; `M` is spelled as a quotient of `W.Aˣ` by the range of Mathlib's
`powMonoidHom 2`, which is the same spelling that `TauCeti/GroupTheory/Finiteness.lean` already
uses for square classes.

## Namespace

These declarations extend Mathlib's own `WeierstrassCurve.Affine` namespace rather than sitting
under `TauCeti`. That is forced by dot notation: `Affine` is a reducible abbreviation for
`WeierstrassCurve`, so `W.f` is resolved by a direct lookup on the structure's namespace and a
`TauCeti.`-prefixed copy is never found. Writing `f W` throughout instead would diverge from the
source for no gain. `TauCeti/RingTheory/AdjoinRoot.lean` sets the same precedent for a file whose
whole content extends a Mathlib namespace.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`), `EllipticCurves/WeakMordellWeil.lean`
lines 60-798, which are that file's Steps 2 and 3, the divisibility criterion opening its Step 4,
and Step 4 itself — the kernel computation. The source is written against Lean `v4.32.0`; this is
a forward port.

Two changes were made against the source. Stoll defines the square classes through a local
abbreviation `Units.modPow`; here they are the quotient by `(powMonoidHom 2).range` directly, so
that TauCeti carries a single spelling of square classes. In the kernel proofs this replaces the
source's `Units.modPow.unit_eq_one_iff` step by `WeierstrassCurve.Affine.M.mk_eq_one_iff`, which
says the same thing about this spelling. And the two lemmas computing the norm of
`x - T` are not part of this file: they belong to the source's Step 5, which the finiteness result
does not use.

This advances `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (README:790-838), whose
description of this route is "the `x - θ` map into the étale algebra `A = K[X]/(f)`".
-/

public section

open Polynomial

/-!
### Commutative-ring and polynomial identities

These encode the multiplicativity of the `x - T` map on the level of coordinates, and are used
only in the proof that `μ` is a homomorphism. The polynomial ones are sign normalisations: the
representatives are naturally written `C x - X`, while `f` factors into `X - C x`, and each
rewriting step below turns one into the other.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product of `b * c - a`
and its two analogues. -/
private lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  grobner

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root of
`(d - a) * b * c`. -/
private lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

/-- `(a * b) ^ 2`, regrouped so that a single factor `b` is split off in front. -/
private lemma sq_mul_eq_mul_sq_mul (a b : R) : (a * b) ^ 2 = b * (a ^ 2 * b) := by
  ring

/-- A corrected representative `C a - X + p`, with its linear part written as `X - C a`. -/
private lemma C_sub_X_add_eq_sub_X_sub_C (a : R) (p : R[X]) :
    C a - X + p = p - (X - C a) := by
  ring

/-- A product of three representatives `C x - X`, with every factor written as `X - C x`. -/
private lemma C_sub_X_mul_mul_eq_neg (a b c : R) :
    (C a - X) * (C b - X) * (C c - X) = -((X - C a) * (X - C b) * (X - C c)) := by
  ring

/-- A corrected representative times two plain ones, with every linear part written as
`X - C x`. -/
private lemma C_sub_X_add_mul_mul_eq_sub_mul_mul (a b c : R) (p : R[X]) :
    (C a - X + p) * (C b - X) * (C c - X) = (p - (X - C a)) * (X - C b) * (X - C c) := by
  ring

end CommRing

namespace WeierstrassCurve

namespace Affine

variable {K : Type*} [Field K] (W : Affine K)

lemma ringChar_ne_two [W.IsElliptic] [W.IsCharNeTwoNF] : ringChar K ≠ 2 := by
  have h := W.isUnit_Δ.ne_zero
  contrapose! h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  rw [Δ_of_isCharNeTwoNF W]
  linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

/-!
### The étale algebra `A`
-/

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

/-- A polynomial of degree at most `2` has degree less than that of `f`, which has degree `3`.
Supplies the degree side conditions of `AdjoinRoot.mk_eq_mk_iff_of_degree_lt` for the relator
`f`. -/
lemma degree_lt_degree_f {p : K[X]} (hp : p.natDegree ≤ 2) : p.degree < W.f.degree :=
  degree_lt_degree <| by rw [natDegree_f]; lia

/-- The derivative of `f`. Its values at the roots of `f` are what makes the corrected
representative a unit; see `deriv_f_ne_zero`. -/
lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring

lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [separable_def', W.derivative_f, f]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄ - 96 * W.a₂ ^ 2) * X
      + C (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (32 * W.a₂ ^ 2 - 96 * W.a₄) * X ^ 2
      + C (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * X
      + C (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)), ?_⟩
  rw [mul_assoc, mul_assoc (C (W.Δ)⁻¹), ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isCharNeTwoNF]
  simp only [C_eq_algebraMap]
  algebra

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

/-- In a normal form for characteristic `≠ 2`, the negation involution on `y`-coordinates is
`y ↦ -y`.

Not a `simp` lemma: the default `simp` set already reduces `negY` through the normal-form
values of `a₁` and `a₃`. -/
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

/-- On a point of `W`, the value `f x` is a square, so it vanishes exactly when `y` does. -/
lemma y_ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]

/-- The synthetic cofactor of `f` at `x`, defined for every `x` by the coefficients of synthetic
division: it satisfies `fCofactor x * (X - C x) = f - C (f.eval x)` (`fCofactor_mul_eq`). It is
the quotient of `f` by `X - x` exactly when `x` is a root of `f`, which is the case
`f_eq_mul_of_eval_eq_zero` records. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

/-- A polynomial of degree at most `1` has degree less than that of `fCofactor x`, which has
degree `2`. Supplies the degree side conditions of `AdjoinRoot.mk_eq_mk_iff_of_degree_lt` for the
relator `fCofactor x`. -/
lemma degree_lt_degree_fCofactor (x : K) {p : K[X]} (hp : p.natDegree ≤ 1) :
    p.degree < (W.fCofactor x).degree :=
  degree_lt_degree <| by rw [natDegree_fCofactor]; lia

lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp only [fCofactor, f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow,
    map_mul, add_sub_add_right_eq_sub]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point whose `x`-coordinate is a root of `f` is divisible by `2`. This
is the `2`-torsion half of `ker_μ_eq`, in the shape `exists_eq_two_smul_iff'` asks for. -/
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr]
  simp only [C_eq_algebraMap]
  algebra

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  rw [eval_f] at hx
  have := W.Δ_of_isCharNeTwoNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  linear_combination ((288 * W.a₄ - 96 * W.a₂ ^ 2) * x
      + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) * hx
    + ((32 * W.a₂ ^ 2 - 96 * W.a₄) * x ^ 2 + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * x
      + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) * this

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

/-- **Every class in `W.A` is represented by a polynomial of degree at most `2`.** The bound is
`natDegree f - 1 = 2`; this is the normal form the kernel computation reduces to before
multiplying by a linear class. -/
lemma exists_mk_quadratic_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

/-- **Multiplying a quadratic representative with a nonzero leading coefficient by a suitable
linear class lowers its degree to `1`.** This is the reduction step of the kernel computation: it
trades the quadratic normal form of `exists_mk_quadratic_eq` for a linear one, at the cost of a
factor `X - C ξ` whose `ξ` the statement produces. -/
lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  conv => enter [1, ξ, 1, l, 1, m]; rw [← map_mul, ← sub_eq_zero, ← map_sub]
  have H (ξ l m : K) : (X - C ξ) * (C r * X ^ 2 + C s * X + C t) - (C l * X + C m) =
      C r * W.f + (C (-ξ * r + s - W.a₂ * r) * X ^ 2 + C (-ξ * s - l - W.a₄ * r + t) * X
        + C (-ξ * t - m - W.a₆ * r)) := by
    simp only [f, C_eq_algebraMap]
    algebra
  conv =>
    enter [1, ξ, 1, l, 1, m]
    rw [H, map_add, map_mul]
    enter [1, 1, 2]
    rw [AdjoinRoot.mk_self]
  simp only [mul_zero, zero_add]
  suffices ∃ ξ l m, -ξ * r + s - W.a₂ * r = 0 ∧ -ξ * s - l - W.a₄ * r + t = 0 ∧
      -ξ * t - m - W.a₆ * r = 0 by
    obtain ⟨ξ, l, m, h₂, h₁, h₀⟩ := this
    refine ⟨ξ, l, m, ?_⟩
    rw [h₂, h₁, h₀]
    simp
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_, ?_, ?_⟩ <;> field

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

/-- **Every class in `W.A' x` is represented by a polynomial of degree at most `1`.** This is
`exists_mk_quadratic_eq` for the cofactor, where the bound is `natDegree (fCofactor x) - 1 = 1`. -/
lemma exists_mk_linear_eq {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]⧸cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  (rfl)

/-- Two classes in `W.A` agree exactly when they agree in both factors of the Chinese Remainder
decomposition at a root of `f`. This is not a corollary of `AdjoinRoot.mk_eq_mk`, which reads the
equality as a divisibility by `f`: here the point is that the divisibility is detected by the two
factors separately. -/
lemma mk_eq_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    AdjoinRoot.mk W.f p = AdjoinRoot.mk W.f q ↔
      p.eval x = q.eval x ∧ AdjoinRoot.mk (W.fCofactor x) p = AdjoinRoot.mk (W.fCofactor x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivProdA' hx]
  simpa only [equivProdA'_apply] using Prod.mk_inj

lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  have hcof : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  have key : (C x - X) * (C (W.f.eval x)⁻¹ * W.fCofactor x) = 1 - C (W.f.eval x)⁻¹ * W.f := by
    rw [mul_left_comm, hcof, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]
  rw [← map_mul, key, map_sub, map_one, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <|
    C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))) =
      C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * ·) using
      mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp

/-- The point `(x, 0)` at a root of `f` lies on the curve. -/
lemma nonsingular_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.Nonsingular x 0 :=
  (equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp
    (by rw [equation_iff_eval_f_eq_sq, hx]; ring)

end

/-!
### The square classes `M`, and the map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := W.Aˣ ⧸ (powMonoidHom 2 : W.Aˣ →* W.Aˣ).range

/-- **The square classes of `W.A` form a commutative group.** This is the target of the descent
map: `μ` lands in `W.M`, and `M.sq_eq_one` says every element squares to `1` (equivalently
`M.inv_eq_self`: every element is its own inverse), so `W.M` is an elementary abelian `2`-group.

The instance is stated rather than left to `inferInstance`: the latter succeeds on the spot, but
instance search does not find it at the use sites below (e.g. for `mul_right_comm` in
`μX_mul_mul_eq_one`) unless it is declared here. -/
noncomputable instance M.instCommGroup : CommGroup W.M := inferInstance

/-- The class of a unit of `W.A` is trivial exactly when the unit is a square in `W.A`. -/
lemma M.mk_eq_one_iff {a : W.A} (ha : IsUnit a) :
    (ha.unit : W.M) = 1 ↔ ∃ z, z ^ 2 = a := by
  rw [QuotientGroup.eq_one_iff]
  simp only [MonoidHom.mem_range, powMonoidHom_apply]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u, ?_⟩, fun ⟨z, hz⟩ ↦ ?_⟩
  · rw [← ha.unit_spec, ← hu]
    push_cast
    ring
  · have hzz : IsUnit (z * z) := by rw [← sq, hz]; exact ha
    have hz' : IsUnit z := isUnit_of_mul_isUnit_left hzz
    exact ⟨hz'.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hz'.unit_spec, hz, ha.unit_spec])⟩

/-- The product of the classes of three units of `W.A` is trivial exactly when their product is a
square in `W.A`. This is the shape in which multiplicativity of the `x - T` map is proved: each
case exhibits an explicit square root of the product of the three representatives. -/
lemma M.mk_mul_mk_mul_mk_eq_one_iff {a b c : W.A} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) :
    (ha.unit : W.M) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ 2 = a * b * c := by
  simp only [← QuotientGroup.mk_mul, ← IsUnit.unit_mul]
  exact M.mk_eq_one_iff ((ha.mul hb).mul hc)

@[simp]
lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective m
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

@[simp] lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

@[simp] lemma M.inv_eq_self (m : W.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (M.mul_self m)

variable [W.IsCharNeTwoNF]

section μX

variable [W.IsElliptic]

open Classical in
/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of `x - T`
if `f x ≠ 0`, and otherwise to the square class of the corrected representative
`x - T + fCofactor x`, which is a unit even though `x - T` is not.

`Classical` decidability is used for the branch: `μX` is noncomputable regardless, so requiring
`DecidableEq K` here would buy nothing. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

/-- The value of `μX` on the branch where `x` is a root of `f`, namely the square class of the
corrected representative `x - T + fCofactor x`.

Not a `simp` lemma: the right-hand side mentions the hypothesis proof `hx`, so it cannot serve
as a rewrite rule. Every use site names it explicitly. -/
lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dite_eq_left hx]

/-- The value of `μX` on the branch where `x` is not a root of `f`, namely the square class of
`x - T`.

Not a `simp` lemma, for the same reason as `μX_of_eval_f_eq_zero`. -/
lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dite_eq_right hx]

end μX

/- `DecidableEq K` enters here and not before: it is what Mathlib's `AddCommGroup W.Point`
instance requires, so every declaration below that mentions `W.Point` needs it. The
coordinate-level `μX` above does not mention `W.Point` and does not take it. Declared at the
outer level so that it stays in scope past the section below. -/
variable [DecidableEq K]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

omit [DecidableEq K] in
/-- The descent map sends the point at infinity to the trivial square class. -/
@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := (rfl)

omit [DecidableEq K] in
/-- On an affine point the descent map is the coordinate-level map `μX` applied to the
`x`-coordinate: it does not see `y`. -/
@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := (rfl)

end μ₀

/-!
### Step 3: `μ` is a homomorphism

Multiplicativity is the statement that the square classes of three collinear points multiply to
`1`. The proof splits on how many of the three `x`-coordinates are roots of `f`, i.e. on how many
of the points are `2`-torsion, and in each case exhibits an explicit square root of the product of
the three representatives.
-/

/-- **Three collinear points cut `f` down to a square.** If three affine points sum to `0`, the
product of the three linear factors `X - C x` is `f` minus the square of a polynomial of degree
at most `1`, namely the line through them. -/
lemma Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero
    {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ :=
    Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ :=
      Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

omit [DecidableEq K] in
/-- **The descent map takes negation to inversion.** Since `μ₀ P` and `μ₀ (-P)` are computed from
the same `x`-coordinate, this is the statement that each square class is its own inverse. -/
lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    M.mk_mul_mk_mul_mk_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR, C_sub_X_add_eq_sub_X_sub_C]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    M.mk_mul_mk_mul_mk_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ :=
    Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    sq_mul_eq_mul_sq_mul (C γ) (X - C xP), ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [C_sub_X_add_mul_mul_eq_sub_mul_mul xP xQ xR (W.fCofactor xP), map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

/-- **Multiplicativity at the level of `x`-coordinates.** If three affine points sum to `0`, the
product of the three square classes is trivial. This is the coordinate-level heart of the proof
that `μ` is a homomorphism; the case split is on how many of the three points are `2`-torsion. -/
lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    M.mk_mul_mk_mul_mk_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ :=
    Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub, C_sub_X_mul_mul_eq_neg]
  simp

end μ₀_helper_lemmas

/-- **Multiplicativity of the descent map on collinear triples.** `μX_mul_mul_eq_one` lifted from
`x`-coordinates to points, including the degenerate cases where one of the three is `0`. This is
exactly the hypothesis `MonoidHom.ofMapMulMulEqOne` needs to build `μ`. -/
lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- **The descent, or `x - T`, map as a group homomorphism.** -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

/-- The homomorphism `μ` agrees with the underlying map `μ₀`. This is the characteristic lemma
for `μ`, and the `simp` normal form: use sites rewrite with it rather than unfolding the
`MonoidHom.ofMapMulMulEqOne` that defines `μ`. -/
@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := by
  simp [μ]

/-- **The descent map kills doubled points.** Consequently `μ` factors through the quotient of
`W.Point` by its doubled points, which is what makes it a descent map: the image of `μ` can only
detect a point up to adding `2 • Q`. -/
@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]

/-!
### The divisibility criterion

What belongs here is the criterion the kernel computation runs on, namely that divisibility by
`2` is equivalent to an explicit polynomial identity. `exists_eq_two_smul_iff'` restates it inside
`W.A`, which is the form the square-class argument consumes; the section below runs that argument
and concludes in `ker_μ_eq`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  have hy₀ : l * ξ + m ≠ 0 := by
    have hΔ := W.isUnit_Δ.ne_zero
    rw [Δ_of_isCharNeTwoNF W] at hΔ
    contrapose! hΔ
    -- the Bézout certificate for `Δ`, evaluated at `ξ`, where `f ξ = (lξ+m)²` and
    -- `f' ξ = 2l(lξ+m)` vanish by `hΔ` and the coefficient identities
    linear_combination
      (((288 * W.a₄ - 96 * W.a₂ ^ 2) * ξ + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) *
          ((l * ξ + m) * hΔ + ξ ^ 2 * H₂ - ξ * H₁ + H₀))
        + (((32 * W.a₂ ^ 2 - 96 * W.a₄) * ξ ^ 2
            + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * ξ
            + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) *
          (2 * l * hΔ + 2 * ξ * H₂ - H₁))
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
    rw [negY_of_isCharNeTwoNF]
    grind
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    simp only [slope_of_Y_ne rfl hy, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
      negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
    rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
    field_simp
    grobner
  have heq : W.Equation ξ (l * ξ + m) := by
    rw [equation_iff_eval_f_eq_sq, eval_f]
    linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-- **A nonsingular affine point is divisible by `2` exactly when an explicit polynomial identity
has a solution.** -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))

/-- The criterion of `exists_eq_two_smul_iff` restated as an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

/-!
### The kernel of the `x - T` map

Both inclusions of `ker_μ_eq`. That `2 • P` is killed is `μ₀_two_nsmul`; the converse is trivial at
the point at infinity and, at an affine point, splits on whether `f` vanishes at the `x`-coordinate.
Each affine branch feeds the criterion of the previous section a square root extracted from
`μ (some x y h) = 1`.
-/

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, M.mk_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_quadratic_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro rfl
    simp only [map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk_iff_of_degree_lt W.monic_f
      (W.degree_lt_degree_f (by compute_degree!))
      (W.degree_lt_degree_f (by compute_degree!))] at hz
    apply_fun natDegree at hz
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz
    lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, M.mk_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_linear_eq (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| dvd_trans ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩ hz
  rw [map_pow, hrs, map_add _ _ (W.fCofactor x), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [map_zero, zero_mul, zero_add, ← map_pow,
      AdjoinRoot.mk_eq_mk_iff_of_degree_lt (W.monic_fCofactor x)
        (W.degree_lt_degree_fCofactor x (by compute_degree!))
        (W.degree_lt_degree_fCofactor x (by compute_degree!))] at hz'
    apply_fun natDegree at hz'
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz'
    lia
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

/-- **A nonsingular affine point killed by the `x - T` map is divisible by `2`.** -/
lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P :=
  (eq_or_ne (W.f.eval x) 0).elim (eq_two_smul_of_μ_eq_one_of_eq h hμ)
    (eq_two_smul_of_μ_eq_one_of_ne h hμ)

end kernel

/-- **The kernel of the `x - T` map is exactly `2 • W(K)`.** This is the injectivity half of the
descent: it is what makes `W(K)/2W(K)` embed into the group of square classes `W.M`. -/
lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h =>
      exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h (by rwa [μ_apply])).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q

end Affine

end WeierstrassCurve

end
