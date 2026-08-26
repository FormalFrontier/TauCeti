/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# The Riemann–Roch spaces and the genus of the rational function field

The rational function field `k(x)` is the base case of the theory, and its Riemann–Roch spaces
can be written down by hand, long before the Riemann–Roch theorem is available.  A rational
function lies in `L(n · P_∞)` exactly when it is a polynomial of degree at most `n`: having no
pole at any finite place makes it a polynomial, and `ord_∞ f = -deg f` turns the remaining
condition into the degree bound.  Hence

`ℓ(n · P_∞) = n + 1 = deg (n · P_∞) + 1`,

and comparing this with Riemann's theorem in large degree gives **`g(k(x)) = 0`**: the rational
function field has genus zero, and Riemann's inequality `ℓ(D) ≥ deg D + 1 - g` is sharp at every
`n · P_∞`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Example 1.4.18 (with
Proposition 1.4.9 for the description of `L(n · P_∞)`).

The polynomiality step is Mathlib's
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` applied to the Dedekind
domain `k[X]`, read through the place vocabulary by
`TauCeti.Place.eq_infty_or_exists_eq_adic`: the places of `k(x)` are the height-one primes of
`k[X]` together with `P_∞`, so the two conditions defining `L(n · P_∞)` split exactly along that
classification.

## Main results

* `TauCeti.mem_riemannRochSpace_zsmul_ofPoint_infty_iff` and
  `TauCeti.riemannRochSpace_zsmul_ofPoint_infty`: `L(n · P_∞)` is the space of polynomials of
  degree at most `n`, in membership form and as an equality of `k`-subspaces of `k(x)`.
* `TauCeti.Divisor.dim_zsmul_ofPoint_infty`: `ℓ(n · P_∞) = n + 1`, the model computation of
  Example 1.4.18; `TauCeti.Divisor.dim_zsmul_ofPoint_infty_eq_toNat` completes it to negative
  multiples, where the space is trivial.
* `TauCeti.genus_ratFunc`: **the rational function field has genus zero**.
* `TauCeti.Divisor.degree_add_one_le_dim_ratFunc`: Riemann's theorem on `k(x)`, with the genus
  evaluated: `ℓ(D) ≥ deg D + 1` for every divisor `D` of `k(x)`.

## Provenance

The mathematics is Stichtenoth's and the Lean development is independent, as in
`TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus`.  The roadmap's coordination section
records that `vaca22/riemann-roch-function-fields` (Guanghao Li, Apache-2.0) carries a complete
function-field Riemann–Roch by the same Stichtenoth route, and that this roadmap specifies the
mathematics rather than that code; no code is copied or adapted from it here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Example 1.4.18.
* The polynomials of bounded degree and their basis of monomials are
  `Mathlib/RingTheory/Polynomial/Basic.lean` and `Mathlib/RingTheory/Polynomial/DegreeLT.lean`
  (Anne Baanen, Kenny Lau); the criterion for a fraction to be integral at every height-one
  prime is `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`
  (María Inés de Frutos-Fernández).
-/

public section

noncomputable section

open scoped WithZero

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### The divisor `n · P_∞` -/

/-- The divisor `n · P_∞` has coefficient `n` at the place at infinity. -/
private lemma coeff_zsmul_ofPoint_infty_self (n : ℤ) :
    WeilDivisor.coeff (n • WeilDivisor.ofPoint (Place.infty k)) (Place.infty k) = n := by
  rw [← WeilDivisor.single_eq_zsmul_ofPoint]
  simp [WeilDivisor.coeff]

/-- The divisor `n · P_∞` has coefficient `0` at every place other than infinity. -/
private lemma coeff_zsmul_ofPoint_infty_of_ne (n : ℤ) {P : Place k (RatFunc k)}
    (hP : P ≠ Place.infty k) :
    WeilDivisor.coeff (n • WeilDivisor.ofPoint (Place.infty k)) P = 0 := by
  rw [← WeilDivisor.single_eq_zsmul_ofPoint]
  simp [WeilDivisor.coeff, hP]

/-- The place at infinity is rational, so `deg (n · P_∞) = n`. -/
theorem Divisor.degree_zsmul_ofPoint_infty (k : Type*) [Field k] (n : ℤ) :
    Divisor.degree (n • WeilDivisor.ofPoint (Place.infty k)) = n := by
  simp

/-- A negative multiple of the place at infinity is a negative divisor. -/
private lemma zsmul_ofPoint_infty_lt_zero {n : ℤ} (hn : n < 0) :
    (n • WeilDivisor.ofPoint (Place.infty k) : Divisor k (RatFunc k)) < 0 := by
  refine lt_of_le_of_ne (WeilDivisor.le_iff.mpr fun P => ?_) fun hzero => ?_
  · rcases eq_or_ne P (Place.infty k) with rfl | hP
    · rw [coeff_zsmul_ofPoint_infty_self, WeilDivisor.coeff_zero]
      exact hn.le
    · rw [coeff_zsmul_ofPoint_infty_of_ne _ hP, WeilDivisor.coeff_zero]
  · have hcoeff := coeff_zsmul_ofPoint_infty_self (k := k) n
    rw [hzero, WeilDivisor.coeff_zero] at hcoeff
    omega

/-! ### `L(n · P_∞)` is the space of polynomials of degree at most `n` -/

/-- **The Riemann–Roch spaces of `k(x)` at infinity** (Stichtenoth, Example 1.4.18): a rational
function lies in `L(n · P_∞)` exactly when it is a polynomial of degree at most `n`.

Regularity at the finite places is exactly polynomiality, by Mathlib's
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` for `k[X]`; the remaining
condition at infinity is `deg f ≤ n`, because `ord_∞` is minus the degree. -/
theorem mem_riemannRochSpace_zsmul_ofPoint_infty_iff {n : ℕ} {f : RatFunc k} :
    f ∈ riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint (Place.infty k)) ↔
      ∃ q : k[X], q.degree ≤ (n : WithBot ℕ) ∧ algebraMap k[X] (RatFunc k) q = f := by
  rw [mem_riemannRochSpace_iff]
  constructor
  · intro hf
    have hfin : ∀ p : HeightOneSpectrum (k[X]), (p.valuation (RatFunc k)) f ≤ 1 := fun p => by
      have h := hf (Place.adic k (RatFunc k) p)
      rwa [coeff_zsmul_ofPoint_infty_of_ne _ (Place.adic_ne_infty k p), WithZero.exp_zero,
        Place.valuation_adic] at h
    obtain ⟨q, rfl⟩ :=
      RingHom.mem_range.mp (HeightOneSpectrum.mem_integers_of_valuation_le_one (RatFunc k) f hfin)
    refine ⟨q, ?_, rfl⟩
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    have h := hf (Place.infty k)
    rw [coeff_zsmul_ofPoint_infty_self,
      Place.valuation_infty_apply (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial,
      WithZero.exp_le_exp] at h
    exact natDegree_le_iff_degree_le.mp (by exact_mod_cast h)
  · rintro ⟨q, hq, rfl⟩ P
    rcases Place.eq_infty_or_exists_eq_adic P with rfl | ⟨p, rfl⟩
    · rw [coeff_zsmul_ofPoint_infty_self]
      rcases eq_or_ne q 0 with rfl | hq0
      · simp
      rw [Place.valuation_infty_apply (RatFunc.algebraMap_ne_zero hq0),
        RatFunc.intDegree_polynomial, WithZero.exp_le_exp]
      exact_mod_cast natDegree_le_iff_degree_le.mpr hq
    · rw [coeff_zsmul_ofPoint_infty_of_ne _ (Place.adic_ne_infty k p), WithZero.exp_zero,
        Place.valuation_adic]
      exact p.valuation_le_one q

/-- **The Riemann–Roch spaces of `k(x)` at infinity**, as an equality of `k`-subspaces of `k(x)`:
`L(n · P_∞)` is the image of the polynomials of degree at most `n`. -/
theorem riemannRochSpace_zsmul_ofPoint_infty (k : Type*) [Field k] (n : ℕ) :
    riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      (degreeLE k (n : WithBot ℕ)).map
        (IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap := by
  ext f
  rw [mem_riemannRochSpace_zsmul_ofPoint_infty_iff, Submodule.mem_map]
  exact ⟨fun ⟨q, hq, hf⟩ => ⟨q, mem_degreeLE.mpr hq, hf⟩,
    fun ⟨q, hq, hf⟩ => ⟨q, mem_degreeLE.mp hq, hf⟩⟩

/-- **`ℓ(n · P_∞) = n + 1`** (Stichtenoth, Example 1.4.18): the polynomials of degree at most `n`
form a `k`-space of dimension `n + 1`, with basis `1, x, …, xⁿ`. -/
theorem Divisor.dim_zsmul_ofPoint_infty (k : Type*) [Field k] (n : ℕ) :
    Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint (Place.infty k)) = n + 1 := by
  have hinj : Function.Injective
      ⇑(IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap :=
    IsFractionRing.injective k[X] (RatFunc k)
  have hmap : Module.finrank k
      (riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint (Place.infty k))) =
      Module.finrank k (degreeLE k (n : WithBot ℕ)) := by
    rw [riemannRochSpace_zsmul_ofPoint_infty]
    exact (Submodule.equivMapOfInjective _ hinj (degreeLE k (n : WithBot ℕ))).finrank_eq.symm
  have hLT : Module.finrank k (degreeLT k (n + 1)) =
      Module.finrank k (degreeLE k (n : WithBot ℕ)) :=
    (LinearEquiv.ofEq (degreeLT k (n + 1)) (degreeLE k (n : WithBot ℕ))
      degreeLT_succ_eq_degreeLE).finrank_eq
  rw [Divisor.dim_def, hmap, ← hLT, Module.finrank_eq_card_basis (degreeLT.basis k (n + 1)),
    Fintype.card_fin]

/-- `L(n · P_∞)` is trivial for `n < 0`: a nonzero function in it would have no pole at all,
hence be a constant, and a nonzero constant does not vanish at infinity.  This is the
negative-degree half of the computation of `ℓ(n · P_∞)`. -/
theorem riemannRochSpace_zsmul_ofPoint_infty_eq_bot_of_neg {n : ℤ} (hn : n < 0) :
    riemannRochSpace (n • WeilDivisor.ofPoint (Place.infty k)) = ⊥ :=
  riemannRochSpace_eq_bot_of_lt_zero (IsFunctionField.ratFunc k)
    (zsmul_ofPoint_infty_lt_zero hn)

/-- **`ℓ(n · P_∞)` for every integer `n`**: it is `n + 1` for `n ≥ 0`, and `0` once `n < 0`. -/
@[simp]
theorem Divisor.dim_zsmul_ofPoint_infty_eq_toNat (k : Type*) [Field k] (n : ℤ) :
    Divisor.dim (n • WeilDivisor.ofPoint (Place.infty k)) = (n + 1).toNat := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [Divisor.dim_def, riemannRochSpace_zsmul_ofPoint_infty_eq_bot_of_neg hn, finrank_bot]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    rw [Divisor.dim_zsmul_ofPoint_infty]
    omega

/-! ### The genus is zero -/

/-- **The rational function field has genus zero** (Stichtenoth, Example 1.4.18).

Riemann's theorem gives a degree beyond which `ℓ(D) = deg D + 1 - g`; evaluating it at
`D = n · P_∞` for large `n` and comparing with `ℓ(n · P_∞) = n + 1 = deg (n · P_∞) + 1`
forces `g = 0`. -/
@[simp]
theorem genus_ratFunc (k : Type*) [Field k] : genus k (RatFunc k) = 0 := by
  obtain ⟨c, hc⟩ :=
    exists_forall_dim_eq_degree_add_one_sub_genus (IsFunctionField.ratFunc k) inferInstance
  have h := hc ((c.toNat : ℤ) • WeilDivisor.ofPoint (Place.infty k))
    (by rw [Divisor.degree_zsmul_ofPoint_infty]; exact Int.self_le_toNat c)
  rw [Divisor.dim_zsmul_ofPoint_infty, Divisor.degree_zsmul_ofPoint_infty] at h
  omega

/-- **Riemann's theorem on `k(x)`**, with the genus evaluated: every divisor `D` of the rational
function field satisfies `ℓ(D) ≥ deg D + 1`.  Equality holds at `D = n · P_∞` by
`TauCeti.Divisor.dim_zsmul_ofPoint_infty`, so Riemann's inequality is sharp on `k(x)`. -/
theorem Divisor.degree_add_one_le_dim_ratFunc (D : Divisor k (RatFunc k)) :
    Divisor.degree D + 1 ≤ Divisor.dim D := by
  have h := Divisor.degree_add_one_sub_genus_le_dim (IsFunctionField.ratFunc k) D
  rw [genus_ratFunc] at h
  omega

end TauCeti
