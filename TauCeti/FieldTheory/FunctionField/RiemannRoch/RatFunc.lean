/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# Divisors, Riemann–Roch spaces and the genus of the rational function field

The rational function field `k(x)` is the base case of the theory of algebraic function fields,
and this file carries out its divisor-level calculations: the divisor of `x`, the Riemann–Roch
spaces of the multiples of the place at infinity, and the resulting value `0` of the genus.  It
completes the rational-function-field thread begun in
`TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic`, where the places of `k(x)` are
classified, and is Stichtenoth, *Algebraic Function Fields and Codes*, Example 1.4.18.

The computation of `L(n · P_∞)` runs on one observation: a rational function is a polynomial
exactly when it has no pole at any finite place, because the finite places are the height-one
primes of `k[X]` and a Dedekind domain is the intersection of its localizations at them.  Given
that, `L(n · P_∞)` is cut out inside `k[X]` by the single remaining condition
`ord_∞ p = -deg p ≥ -n`, so it is the space of polynomials of degree at most `n` and
`ℓ(n · P_∞) = n + 1`.  This is proved by hand, with no appeal to Riemann–Roch; feeding it into
Riemann's theorem — which is therefore sharp here at every `n` — gives `g(k(x)) = 0`.

## Main results

* `TauCeti.Place.forall_ord_adicOfIrreducible_nonneg_iff`: the functions regular at every finite
  place of `k(x)` are the polynomials.
* `TauCeti.Divisor.principal_X`: `div x = P_(X) - P_∞`.
* `TauCeti.mem_riemannRochSpace_nsmul_ofPoint_infty_iff` and
  `TauCeti.riemannRochSpace_nsmul_ofPoint_infty`: `L(n · P_∞)` is the space of polynomials of
  degree at most `n`.
* `TauCeti.Divisor.dim_nsmul_ofPoint_infty`: `ℓ(n · P_∞) = n + 1`.
* `TauCeti.genus_ratFunc`: **the rational function field has genus zero**
  (Stichtenoth, Example 1.4.18).
* `TauCeti.Divisor.degree_poles_eq_max_natDegree`: the pole divisor of a nonconstant `z ∈ k(x)`
  has degree `max (deg z.num) (deg z.denom)`, the degree of `k(x) / k(z)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.2 and I.4.
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### Functions regular away from infinity -/

namespace Place

/-- **A rational function is a polynomial exactly when it has no pole at any finite place.**  The
finite places of `k(x)` are the places of the height-one primes of `k[X]`, so this is the
Dedekind-domain fact that `k[X]` is the intersection of its localizations at them
(`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`), read in place
vocabulary. -/
theorem forall_ord_adicOfIrreducible_nonneg_iff {f : RatFunc k} :
    (∀ (q : k[X]) (hq : Irreducible q), 0 ≤ (adicOfIrreducible hq).ord f) ↔
      ∃ p : k[X], algebraMap k[X] (RatFunc k) p = f := by
  constructor
  · intro h
    refine RingHom.mem_range.mp (HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := k[X]) (RatFunc k) f fun v ↦ ?_)
    obtain ⟨q, ⟨-, hqi, hspan⟩, -⟩ := v.existsUnique_monic_irreducible_span
    rw [show v = HeightOneSpectrum.ofIrreducible hqi from HeightOneSpectrum.ext
        (hspan.trans (HeightOneSpectrum.ofIrreducible_asIdeal hqi).symm),
      ← valuation_adicOfIrreducible hqi, ← (adicOfIrreducible hqi).mem_integers_iff,
      (adicOfIrreducible hqi).mem_integers_iff_ord_nonneg]
    exact h q hqi
  · rintro ⟨p, rfl⟩ q hq
    rw [adicOfIrreducible_def]
    exact ord_algebraMap_adic_nonneg k (RatFunc k) _ p

end Place

/-! ### The divisor of `x` -/

/-- **The divisor of `x`**: `div x = P_(X) - P_∞`.  The function `x` has a simple zero at the
place of the polynomial `X`, a simple pole at infinity, and no other zeros or poles. -/
theorem Divisor.principal_X :
    Divisor.principal (IsFunctionField.ratFunc k)
        (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible (irreducible_X (R := k))) -
        WeilDivisor.ofPoint (Place.infty k) := by
  classical
  refine WeilDivisor.ext fun P ↦ ?_
  rw [Divisor.coeff_principal, WeilDivisor.coeff_sub, Units.val_mk0]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · rw [Place.ord_infty, RatFunc.intDegree_X, WeilDivisor.coeff_ofPoint_self,
      WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty _).symm]
    ring
  · rw [Place.ord_adicOfIrreducible_X hq,
      WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq)]
    by_cases hqX : Associated q X
    · have hplace : Place.adicOfIrreducible hq = Place.adicOfIrreducible (irreducible_X (R := k)) :=
        (Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq irreducible_X).mpr hqX
      rw [ite_eq_left hqX, hplace, WeilDivisor.coeff_ofPoint_self]
      ring
    · rw [ite_eq_right hqX, WeilDivisor.coeff_ofPoint_of_ne fun h ↦
        hqX ((Place.adicOfIrreducible_eq_adicOfIrreducible_iff hq irreducible_X).mp h)]
      ring

/-! ### The Riemann–Roch spaces of the multiples of `P_∞` -/

/-- **`L(n · P_∞)` is the space of polynomials of degree at most `n`** (Stichtenoth,
Example 1.4.18), in membership form: the functions with no finite pole are the polynomials, and
the remaining condition `ord_∞ p ≥ -n` says exactly that `deg p ≤ n`. -/
theorem mem_riemannRochSpace_nsmul_ofPoint_infty_iff {n : ℕ} {f : RatFunc k} :
    f ∈ riemannRochSpace (n • WeilDivisor.ofPoint (Place.infty k)) ↔
      ∃ p : k[X], p.degree ≤ n ∧ algebraMap k[X] (RatFunc k) p = f := by
  -- the two coefficients of `n · P_∞`
  have hself : ((n • WeilDivisor.ofPoint (Place.infty k) : Divisor k (RatFunc k))).coeff
      (Place.infty k) = n := by simp
  have hadic : ∀ (q : k[X]) (hq : Irreducible q),
      ((n • WeilDivisor.ofPoint (Place.infty k) : Divisor k (RatFunc k))).coeff
        (Place.adicOfIrreducible hq) = 0 := fun q hq ↦ by
    simp [Place.adicOfIrreducible_ne_infty hq]
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨fun _ ↦ ⟨0, by simp, map_zero _⟩, fun _ ↦ Submodule.zero_mem _⟩
  rw [mem_riemannRochSpace_iff_neg_le_ord hf0]
  constructor
  · intro h
    obtain ⟨p, rfl⟩ := Place.forall_ord_adicOfIrreducible_nonneg_iff.mp fun q hq ↦ by
      simpa [hadic q hq] using h (Place.adicOfIrreducible hq)
    have hp := h (Place.infty k)
    rw [hself, Place.ord_infty_algebraMap] at hp
    exact ⟨p, natDegree_le_iff_degree_le.mp (by omega), rfl⟩
  · rintro ⟨p, hp, rfl⟩ P
    rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
    · rw [hself, Place.ord_infty_algebraMap]
      have := natDegree_le_iff_degree_le.mpr hp
      omega
    · rw [hadic q hq, neg_zero]
      exact Place.forall_ord_adicOfIrreducible_nonneg_iff.mpr ⟨p, rfl⟩ q hq

/-- **`L(n · P_∞)` is the space of polynomials of degree at most `n`** (Stichtenoth,
Example 1.4.18), as an equality of `k`-subspaces of `k(x)`. -/
theorem riemannRochSpace_nsmul_ofPoint_infty (n : ℕ) :
    riemannRochSpace (n • WeilDivisor.ofPoint (Place.infty k)) =
      (degreeLE k n).map (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap := by
  ext f
  rw [mem_riemannRochSpace_nsmul_ofPoint_infty_iff, Submodule.mem_map]
  simp [mem_degreeLE]

/-- **`ℓ(n · P_∞) = n + 1`** (Stichtenoth, Example 1.4.18): the polynomials of degree at most `n`
form a `k`-space of dimension `n + 1`. -/
@[simp]
theorem Divisor.dim_nsmul_ofPoint_infty (n : ℕ) :
    Divisor.dim (n • WeilDivisor.ofPoint (Place.infty k)) = n + 1 := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap :=
    FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
  rw [Divisor.dim_def, riemannRochSpace_nsmul_ofPoint_infty,
    ← (Submodule.equivMapOfInjective _ hinj (degreeLE k n)).finrank_eq,
    ← degreeLT_succ_eq_degreeLE, Module.finrank_eq_card_basis (degreeLT.basis k (n + 1)),
    Fintype.card_fin]

/-! ### The genus -/

/-- The degree of `n · P_∞` is `n`, the place at infinity being rational. -/
@[simp]
theorem Divisor.degree_nsmul_ofPoint_infty (n : ℕ) :
    Divisor.degree (n • WeilDivisor.ofPoint (Place.infty k)) = n := by
  rw [map_nsmul, Divisor.degree_ofPoint, Place.degree_infty, nsmul_eq_mul]
  norm_num

/-- **The rational function field has genus zero** (Stichtenoth, Example 1.4.18).  Riemann's
theorem gives `ℓ(D) = deg D + 1 - g` for every divisor of large enough degree; the divisors
`n · P_∞` have degree `n` and `ℓ(n · P_∞) = n + 1`, so `g = 0`. -/
@[simp]
theorem genus_ratFunc : genus k (RatFunc k) = 0 := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc
  have hn : c ≤ ((c.toNat : ℕ) : ℤ) := Int.self_le_toNat c
  have h := hc (c.toNat • WeilDivisor.ofPoint (Place.infty k))
    (by rwa [Divisor.degree_nsmul_ofPoint_infty])
  rw [Divisor.dim_nsmul_ofPoint_infty, Divisor.degree_nsmul_ofPoint_infty] at h
  push_cast at h
  omega

/-! ### The degree of a rational map -/

/-- **Stichtenoth, Theorem 1.4.11 on `ℙ¹`**: the pole divisor of a nonconstant rational function
`z` has degree `max (deg z.num) (deg z.denom)`, which is `[k(x) : k(z)]`, the degree of the
covering `ℙ¹ → ℙ¹` that `z` defines.  A rational function is transcendental over `k` exactly when
it is not a constant, by `RatFunc.transcendental_of_ne_C`. -/
theorem Divisor.degree_poles_eq_max_natDegree (z : (RatFunc k)ˣ)
    (hz : Transcendental k (z : RatFunc k)) :
    Divisor.degree (Divisor.poles (IsFunctionField.ratFunc k) z) =
      max (z : RatFunc k).num.natDegree (z : RatFunc k).denom.natDegree := by
  rw [Divisor.degree_poles _ _ hz, RatFunc.finrank_eq_max_natDegree]

end TauCeti
