/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The coordinate ring of an elliptic curve is a Dedekind domain

For a Weierstrass curve `W` over a field `F` the coordinate ring `F[W] = F[X, Y]/(W(X, Y))` is a
free `F[X]`-module of rank two, so it is noetherian of dimension at most one for free. The content
of this file is the remaining, and only nontrivial, Dedekind axiom: `F[W]` is **integrally closed**
whenever `W` is elliptic.

The proof is the quadratic-extension calculation, run at one prime at a time. Writing
`s = a₁X + a₃` and `c = X³ + a₂X² + a₄X + a₆`, the coordinate ring carries the conjugation
`y ↦ -y - s` — the coordinate-ring form of Mathlib's `WeierstrassCurve.Affine.negY` — and an
element `z` of the function field integral over `F[X]` may be written `(p + qy)/d`. Its trace
`(2p - qs)/d` and its norm `(p² - pqs - q²c)/d²` again lie in `F(X)` and are again integral, so
`F[X]` being integrally closed forces `d ∣ 2p - qs` and `d² ∣ p² - pqs - q²c`. That divisibility
input alone forces `d ∣ p` and `d ∣ q`, which says exactly `z ∈ F[W]`.

The last step is where the curve enters, and it is a genuine use of nonsingularity rather than a
discriminant computation, so no characteristic is special. Suppose a prime `π` divides `d` but not
`q`, and let `k = F[X]/(π)`. Choosing `g` with `p ≡ gq` modulo `π`, the two divisibilities say that
`π²` divides `H = g² - gs - c` and that `π` divides `2g - s`. Then `π ∣ H` and `π ∣ H'`, and
reading `H' = g'(2g - s) - a₁g - c'` modulo `π` turns those into

* `(x₀, β)` lies on `W` over `k`, where `x₀` is the image of `X` and `β` the image of `-g`;
* `W_Y(x₀, β) = 2β + a₁x₀ + a₃ = 0`, which is `π ∣ 2g - s`;
* `W_X(x₀, β) = a₁β - (3x₀² + 2a₂x₀ + a₄) = 0`, which is `π ∣ a₁g + c'`.

That is a singular point of an elliptic curve, which is absurd. The argument is uniform in the
characteristic, unlike the familiar route through `Squarefree (4X³ + b₂X² + 2b₄X + b₆)`: in
characteristic two that polynomial is the square `(a₁X + a₃)²`.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.conj`: the conjugation involution of `R[W]` over
  `R[X]`, sending `y` to `-y - (a₁X + a₃)`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.mul_conj`: `x * conj x` is the norm of `x`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.add_negPolynomial_smul_basis`: the expanded
  conjugation formula computes the trace on the basis `{1, Y}`.
* `TauCeti.WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`: the coordinate ring of an
  elliptic curve over a field is integrally closed.
* `TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`: it is a Dedekind domain.

The integral closedness is the seeded milestone `isIntegrallyClosed_coordinateRing` of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 1, where it is named as the normality input to
the induced map on points `Isogeny.toPointHom`; the Dedekind statement is the "worthwhile lemma"
that Layer 0 asks for, on which the identification of the affine places with the maximal ideals of
the coordinate ring rests.

## Provenance

Not ported; this is a direct proof. Mathlib knows the coordinate ring, its `R[X]`-basis `{1, Y}`
and the norm of `p • 1 + q • Y` (`WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`), all of
which are used here, but has no normality or Dedekind statement about it.
-/

public section

open Polynomial Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve.Affine

open _root_.WeierstrassCurve.Affine _root_.WeierstrassCurve.Affine.CoordinateRing

namespace CoordinateRing

/-! ## Conjugation on the coordinate ring -/

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R)

/-- Substituting `-Y - (a₁X + a₃)` for `Y` leaves the Weierstrass polynomial unchanged: the two
roots of `W(X, ·)` are `y` and its conjugate `-y - (a₁X + a₃)`. -/
lemma eval₂_negPolynomial_polynomial :
    W.polynomial.eval₂ (C : R[X] →+* R[X][Y]) W.negPolynomial = W.polynomial := by
  rw [polynomial, negPolynomial]
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
  ring1

/-- `AdjoinRoot.mk_C` in the `algebraMap` spelling that the rewrites below want. -/
private lemma mk_C_eq_algebraMap (r : R[X]) :
    mk W (C r) = algebraMap R[X] W.CoordinateRing r := by
  simp [AdjoinRoot.algebraMap_eq]

private lemma smul_mk_eq_mk (p q : R[X]) (f : R[X][Y]) :
    p • (1 : W.CoordinateRing) + q • mk W f = mk W (C p + C q * f) := by
  simp only [smul, mul_one, ← map_mul, ← map_add]

private noncomputable def conjHom : W.CoordinateRing →ₐ[R[X]] W.CoordinateRing :=
  AdjoinRoot.liftAlgHom W.polynomial (Algebra.ofId R[X] W.CoordinateRing)
    (mk W W.negPolynomial) <| by
      have h := Polynomial.hom_eval₂ W.polynomial (C : R[X] →+* R[X][Y]) (mk W) W.negPolynomial
      rw [eval₂_negPolynomial_polynomial, AdjoinRoot.mk_self] at h
      exact h.symm

@[simp]
private lemma conjHom_mk_Y : conjHom W (AdjoinRoot.root W.polynomial) = mk W W.negPolynomial :=
  AdjoinRoot.liftAlgHom_root ..

@[simp]
private lemma conjHom_mk_C (r : R[X]) :
    conjHom W (AdjoinRoot.of W.polynomial r) = mk W (C r) := by
  simpa only [AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C] using (conjHom W).commutes r

private lemma conjHom_conjHom (x : W.CoordinateRing) : conjHom W (conjHom W x) = x := by
  have h : (conjHom W).comp (conjHom W) = AlgHom.id R[X] W.CoordinateRing := by
    refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply, conjHom_mk_Y, negPolynomial]
    simp only [map_sub, map_neg, AdjoinRoot.mk_X, AdjoinRoot.mk_C, conjHom_mk_Y,
      conjHom_mk_C, negPolynomial]
    ring
  exact congrArg (fun f : W.CoordinateRing →ₐ[R[X]] W.CoordinateRing => f x) h

/-- The conjugation involution of the coordinate ring `R[W]` over `R[X]`, sending `y` to
`-y - (a₁X + a₃)`. It is the coordinate-ring form of `WeierstrassCurve.Affine.negY`: the pullback
of the involution `(x, y) ↦ (x, -y - a₁x - a₃)` of the curve. -/
noncomputable def conj : W.CoordinateRing ≃ₐ[R[X]] W.CoordinateRing :=
  AlgEquiv.ofAlgHom (conjHom W) (conjHom W) (by ext; exact conjHom_conjHom W _)
    (by ext; exact conjHom_conjHom W _)

@[simp]
private lemma conj_apply (x : W.CoordinateRing) : conj W x = conjHom W x := by
  simp [conj]

/-- Conjugation sends the coordinate `y` to `-y - (a₁X + a₃)`. -/
@[simp]
lemma conj_mk_Y : conj W (AdjoinRoot.root W.polynomial) = mk W W.negPolynomial := by
  rw [conj_apply, conjHom_mk_Y]

/-- Conjugation fixes the coefficient ring `R[X]`. -/
@[simp]
lemma conj_mk_C (r : R[X]) : conj W (AdjoinRoot.of W.polynomial r) = mk W (C r) := by
  rw [conj_apply, conjHom_mk_C]

/-- Conjugation is an involution. -/
@[simp]
lemma conj_conj (x : W.CoordinateRing) : conj W (conj W x) = x :=
  by simpa only [conj_apply] using conjHom_conjHom W x

/-- In the basis `{1, Y}`, conjugation sends the element with coordinates `(p, q)` to the
polynomial representative `p + q * W.negPolynomial`. -/
lemma conj_smul_basis (p q : R[X]) :
    conj W (p • (1 : W.CoordinateRing) + q • mk W Y) = mk W (C p + C q * W.negPolynomial) := by
  rw [smul_mk_eq_mk]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, conj_mk_C, conj_mk_Y]

/-- The sum of an element of the coordinate ring and its conjugate is its trace `2p - qs`. -/
@[simp]
lemma add_negPolynomial_smul_basis (p q : R[X]) :
    p • (1 : W.CoordinateRing) + q • AdjoinRoot.root W.polynomial +
        (p • 1 + AdjoinRoot.mk W.polynomial (q • W.negPolynomial)) =
      algebraMap R[X] W.CoordinateRing (2 * p - q * (C W.a₁ * X + C W.a₃)) := by
  rw [← AdjoinRoot.mk_X, ← AdjoinRoot.smul_mk, smul_mk_eq_mk, smul_mk_eq_mk,
    ← map_add, ← mk_C_eq_algebraMap]
  congr 1
  rw [negPolynomial]
  simp only [map_sub, map_mul, map_ofNat]
  ring1

/-- The product of an element of the coordinate ring and its conjugate is its norm. -/
@[simp]
lemma mul_conj (x : W.CoordinateRing) :
    x * conj W x = algebraMap R[X] W.CoordinateRing (Algebra.norm R[X] x) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq x
  rw [conj_smul_basis, ← mk_C_eq_algebraMap, AdjoinRoot.mk_C, coe_norm_smul_basis,
    smul_mk_eq_mk, ← map_mul, negPolynomial]

end CoordinateRing

/-! ## The divisibility core -/

section Field

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- Over a field, a prime dividing the trace `2p - qs` and whose square divides the norm
`p² - pqs - q²c` divides both `p` and `q`. This is where the curve enters: the alternative is a
singular point of `W` over the residue field of the prime. -/
private theorem dvd_and_dvd_of_prime [W.IsElliptic] {π p q : F[X]} (hπ : Prime π)
    (ht : π ∣ 2 * p - q * (C W.a₁ * X + C W.a₃))
    (hn : π ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
      q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :
    π ∣ p ∧ π ∣ q := by
  have hq : π ∣ q := by
    by_contra hq
    have : Fact (Irreducible π) := ⟨hπ.irreducible⟩
    have hqk : AdjoinRoot.mk π q ≠ 0 := fun h => hq (AdjoinRoot.mk_eq_zero.mp h)
    -- choose `g` with `p ≡ g * q` modulo `π`
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (AdjoinRoot.mk π p / AdjoinRoot.mk π q)
    obtain ⟨p₁, hp₁⟩ : π ∣ p - g * q := AdjoinRoot.mk_eq_zero.mp <| by
      rw [map_sub, map_mul, hg, div_mul_cancel₀ _ hqk, sub_self]
    -- transport the two divisibilities to `g`
    obtain ⟨f, hf⟩ : π ∣ 2 * g - (C W.a₁ * X + C W.a₃) := by
      have hprod : π ∣ q * (2 * g - (C W.a₁ * X + C W.a₃)) := by
        obtain ⟨t₁, ht₁⟩ := ht
        exact ⟨t₁ - 2 * p₁, by linear_combination ht₁ - 2 * hp₁⟩
      refine (hπ.dvd_or_dvd hprod).resolve_left hq
    have hm : π ^ 2 ∣ g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
      refine hπ.pow_dvd_of_dvd_mul_left (a := q ^ 2) 2 (fun h => hq (hπ.dvd_of_dvd_pow h)) ?_
      obtain ⟨n₁, hn₁⟩ := hn
      exact ⟨n₁ - p₁ * q * f - p₁ ^ 2, by
        linear_combination hn₁ -
          (p + g * q + π * p₁ - q * (C W.a₁ * X + C W.a₃)) * hp₁ - π * p₁ * q * hf⟩
    -- `π ∣ H` and `π ∣ H'`, the latter read through `H' = g'(2g - s) - (a₁g + c')`
    have hH₁ : π ∣ C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄) := by
      have hd : derivative (g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
          (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) =
          derivative g * (2 * g - (C W.a₁ * X + C W.a₃)) -
            (C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄)) := by
        simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add, derivative_C,
          derivative_X, map_ofNat, Nat.cast_ofNat]
        ring1
      have hd' : π ∣ derivative g * (2 * g - (C W.a₁ * X + C W.a₃)) -
          (C W.a₁ * g + (3 * X ^ 2 + 2 * C W.a₂ * X + C W.a₄)) := by
        rw [← hd]
        simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hm
      simpa using dvd_sub (Dvd.dvd.mul_left ⟨f, hf⟩ (derivative g)) hd'
    -- the three vanishings, read in the residue field
    have hev : ∀ r : F[X], π ∣ r → aeval (AdjoinRoot.root π) r = 0 := fun r hr => by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.mpr hr
    have h₁ := hev (g ^ 2 - g * (C W.a₁ * X + C W.a₃) -
      (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))
        ((dvd_pow_self π two_ne_zero).trans hm)
    have h₂ := hev (2 * g - (C W.a₁ * X + C W.a₃)) ⟨f, hf⟩
    have h₃ := hev _ hH₁
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_C, aeval_X] at h₁ h₂ h₃
    have key : (W.map (algebraMap F (AdjoinRoot π))).Nonsingular (AdjoinRoot.root π)
        (-aeval (AdjoinRoot.root π) g) := equation_iff_nonsingular.mp <| by
      rw [equation_iff']
      simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
        _root_.WeierstrassCurve.map_a₃, _root_.WeierstrassCurve.map_a₄,
        _root_.WeierstrassCurve.map_a₆]
      linear_combination h₁
    rw [nonsingular_iff'] at key
    refine key.2.elim (fun h => h ?_) fun h => h ?_
    · simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
        _root_.WeierstrassCurve.map_a₄]
      linear_combination -h₃
    · simp only [_root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₃]
      linear_combination -h₂
  refine ⟨?_, hq⟩
  obtain ⟨q₁, rfl⟩ := hq
  refine hπ.dvd_of_dvd_pow (n := 2) ?_
  obtain ⟨n₁, hn₁⟩ := dvd_trans (dvd_pow_self π two_ne_zero) hn
  exact ⟨n₁ + p * q₁ * (C W.a₁ * X + C W.a₃) +
    π * q₁ ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆), by linear_combination hn₁⟩

/-- The divisibility core: a denominator dividing the trace and whose square divides the norm
divides both coordinates. -/
private theorem dvd_and_dvd [W.IsElliptic] (d : F[X]) : ∀ p q : F[X], d ≠ 0 →
    d ∣ 2 * p - q * (C W.a₁ * X + C W.a₃) →
    d ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
      q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) →
    d ∣ p ∧ d ∣ q := by
  refine UniqueFactorizationMonoid.induction_on_prime d (fun p q hd => absurd rfl hd)
    (fun u hu p q _ _ _ => ⟨hu.dvd, hu.dvd⟩) fun a π ha hπ ih p q _ ht hn => ?_
  obtain ⟨hp, hq⟩ := dvd_and_dvd_of_prime W hπ ((dvd_mul_right π a).trans ht)
    (dvd_trans (pow_dvd_pow_of_dvd (dvd_mul_right π a) 2) hn)
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  have ht' : a ∣ 2 * p' - q' * (C W.a₁ * X + C W.a₃) := by
    refine (mul_dvd_mul_iff_left hπ.ne_zero).mp ?_
    have htrace : π * (2 * p' - q' * (C W.a₁ * X + C W.a₃)) =
        2 * (π * p') - π * q' * (C W.a₁ * X + C W.a₃) := by ring
    rw [htrace]
    exact ht
  have hn' : a ^ 2 ∣ p' ^ 2 - p' * q' * (C W.a₁ * X + C W.a₃) -
      q' ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero 2 hπ.ne_zero)).mp ?_
    have hnorm : π ^ 2 * (p' ^ 2 - p' * q' * (C W.a₁ * X + C W.a₃) -
        q' ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) =
        (π * p') ^ 2 - π * p' * (π * q') * (C W.a₁ * X + C W.a₃) -
          (π * q') ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by ring
    rw [hnorm, ← mul_pow]
    exact hn
  obtain ⟨hp', hq'⟩ := ih p' q' ha ht' hn'
  exact ⟨mul_dvd_mul_left π hp', mul_dvd_mul_left π hq'⟩

end Field

/-! ## Integral closedness -/

section IntegrallyClosed

/-- An element of a field extension of `A` that is a quotient of elements of `A` and is integral
over `A` has its numerator divisible by its denominator, when `A` is integrally closed. -/
private theorem dvd_of_isIntegral_div {A L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L] [Algebra A L] [FaithfulSMul A L] {a d : A} (hd : d ≠ 0)
    (h : IsIntegral A (algebraMap A L a / algebraMap A L d)) : d ∣ a := by
  have hinj : Function.Injective (algebraMap A L) := FaithfulSMul.algebraMap_injective A L
  let f : FractionRing A →ₐ[A] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A L) hinj
  have hf : Function.Injective f := (f : FractionRing A →+* L).injective
  have hdF : algebraMap A (FractionRing A) d ≠ 0 := fun h' =>
    hd (IsFractionRing.injective A (FractionRing A) (by rw [h', map_zero]))
  have hw : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d) =
      algebraMap A L a / algebraMap A L d := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes]
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algHom_iff f hf).mp (hw ▸ h))
  refine ⟨e, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, he, mul_div_cancel₀ _ hdF]

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

private lemma module_finite_coordinateRing : Module.Finite F[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

/-- The conjugation involution of the function field `F(W)` over `F(X)`. -/
private noncomputable def conjFunctionField :
    W.FunctionField ≃ₐ[F[X]] W.FunctionField :=
  IsFractionRing.algEquivOfAlgEquiv (CoordinateRing.conj W)

/-- Every element of the function field of an elliptic curve that is integral over `F[X]` already
lies in the coordinate ring. -/
private theorem exists_algebraMap_eq [W.IsElliptic] {z : W.FunctionField}
    (hz : IsIntegral F[X] z) :
    ∃ b : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField b = z := by
  set σ := conjFunctionField W with hσ
  -- write `z = b / d` with `b` in the coordinate ring and `d` in `F[X]`
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hb₂0 : b₂ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₂
  have hcb₂0 : CoordinateRing.conj W b₂ ≠ 0 := fun h =>
    hb₂0 <| (CoordinateRing.conj W).injective (by rw [h, map_zero])
  set b : W.CoordinateRing := b₁ * CoordinateRing.conj W b₂ with hb
  set d : F[X] := Algebra.norm F[X] b₂
  have hdB : algebraMap F[X] W.CoordinateRing d = b₂ * CoordinateRing.conj W b₂ :=
    (CoordinateRing.mul_conj W b₂).symm
  have hd0 : d ≠ 0 := fun h => (mul_ne_zero hb₂0 hcb₂0) (by rw [← hdB, h, map_zero])
  have hinjB : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    FaithfulSMul.algebraMap_injective _ _
  have hmap : ∀ r : F[X], algebraMap F[X] W.FunctionField r =
      algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing r) := fun r =>
    IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField r
  have hinjK : Function.Injective (algebraMap F[X] W.FunctionField) := by
    rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField]
    exact hinjB.comp (FaithfulSMul.algebraMap_injective _ _)
  have hdK : algebraMap F[X] W.FunctionField d ≠ 0 := fun h =>
    hd0 (hinjK (h.trans (map_zero _).symm))
  have hcb₂K : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.conj W b₂) ≠ 0 :=
    fun h => hcb₂0 (hinjB (h.trans (map_zero _).symm))
  have hzeq : algebraMap W.CoordinateRing W.FunctionField b₁ /
      algebraMap W.CoordinateRing W.FunctionField b₂ =
      algebraMap W.CoordinateRing W.FunctionField b / algebraMap F[X] W.FunctionField d := by
    rw [hmap, hdB, hb, map_mul, map_mul, mul_div_mul_right _ _ hcb₂K]
  rw [hzeq] at hz ⊢
  -- the trace and the norm of `z`
  obtain ⟨p, q, hpq⟩ := exists_smul_basis_eq b
  have hσz : σ (algebraMap W.CoordinateRing W.FunctionField b /
      algebraMap F[X] W.FunctionField d) =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.conj W b) /
        algebraMap F[X] W.FunctionField d := by
    rw [map_div₀, hσ, conjFunctionField, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
      AlgEquiv.commutes]
  have hσzi : IsIntegral F[X] (σ (algebraMap W.CoordinateRing W.FunctionField b /
      algebraMap F[X] W.FunctionField d)) := hz.map (σ : W.FunctionField →ₐ[F[X]] W.FunctionField)
  have htr : d ∣ 2 * p - q * (C W.a₁ * X + C W.a₃) := by
    refine dvd_of_isIntegral_div (L := W.FunctionField) hd0 ?_
    have hadd : p • (1 : W.CoordinateRing) + q • mk W Y +
        CoordinateRing.conj W (p • 1 + q • mk W Y) =
        algebraMap F[X] W.CoordinateRing (2 * p - q * (C W.a₁ * X + C W.a₃)) := by
      simpa only [AdjoinRoot.mk_X, map_add, map_smul, map_one, CoordinateRing.conj_mk_Y,
        AdjoinRoot.smul_mk] using CoordinateRing.add_negPolynomial_smul_basis W p q
    have : algebraMap F[X] W.FunctionField (2 * p - q * (C W.a₁ * X + C W.a₃)) /
        algebraMap F[X] W.FunctionField d =
        algebraMap W.CoordinateRing W.FunctionField b / algebraMap F[X] W.FunctionField d +
          σ (algebraMap W.CoordinateRing W.FunctionField b /
            algebraMap F[X] W.FunctionField d) := by
      rw [hσz, ← add_div, ← map_add, hmap, ← hpq, hadd]
    rw [this]
    exact hz.add hσzi
  have hnm : d ^ 2 ∣ p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
      q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
    refine dvd_of_isIntegral_div (L := W.FunctionField) (pow_ne_zero 2 hd0) ?_
    have hnorm : Algebra.norm F[X] b = p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) := by
      rw [← hpq, norm_smul_basis]
    have : algebraMap F[X] W.FunctionField (p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) /
        algebraMap F[X] W.FunctionField (d ^ 2) =
        (algebraMap W.CoordinateRing W.FunctionField b / algebraMap F[X] W.FunctionField d) *
          σ (algebraMap W.CoordinateRing W.FunctionField b /
            algebraMap F[X] W.FunctionField d) := by
      rw [hσz, div_mul_div_comm, ← map_mul, ← hnorm, CoordinateRing.mul_conj, ← hmap,
        map_pow, pow_two]
    rw [this]
    exact hz.mul hσzi
  -- conclude
  obtain ⟨hdp, hdq⟩ := dvd_and_dvd W d p q hd0 htr hnm
  obtain ⟨p', rfl⟩ := hdp
  obtain ⟨q', rfl⟩ := hdq
  refine ⟨p' • 1 + q' • mk W Y, ?_⟩
  rw [eq_div_iff hdK, hmap, ← map_mul, ← hpq]
  congr 1
  simp only [smul, ← CoordinateRing.mk_C_eq_algebraMap, map_mul]
  ring1

/-- **The coordinate ring of an elliptic curve is integrally closed.** This is the normality half
of the statement that it is a Dedekind domain, and the input that the induced map on points of an
isogeny consumes. -/
theorem isIntegrallyClosed_coordinateRing [W.IsElliptic] : IsIntegrallyClosed W.CoordinateRing := by
  have := module_finite_coordinateRing W
  have : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  have : IsIntegrallyClosedIn W.CoordinateRing W.FunctionField :=
    isIntegrallyClosedIn_iff.mpr ⟨FaithfulSMul.algebraMap_injective _ _,
      fun hx => exists_algebraMap_eq W (isIntegral_trans _ hx)⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn W.CoordinateRing W.FunctionField

/-- **The coordinate ring of an elliptic curve is a Dedekind domain.** -/
theorem isDedekindDomain_coordinateRing [W.IsElliptic] : IsDedekindDomain W.CoordinateRing := by
  have := module_finite_coordinateRing W
  have : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  have := isIntegrallyClosed_coordinateRing W
  exact { __ := Ring.DimensionLEOne.of_isIntegral F[X] W.CoordinateRing }

end IntegrallyClosed

end WeierstrassCurve.Affine

end TauCeti
