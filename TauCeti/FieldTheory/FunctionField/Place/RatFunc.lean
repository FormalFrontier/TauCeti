/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RatFunc.Ostrowski
public import TauCeti.FieldTheory.FunctionField.Place.Adic

/-!
# The places of the rational function field

The rational function field `k(x)` is the base case of the theory of algebraic function fields,
and this file determines all of its places. Besides the finite places `P_p` coming from the
height-one primes of `k[X]` — supplied in general by
`TauCeti.FieldTheory.FunctionField.Place.Adic` — there is exactly one further place, the place at
infinity `P_∞`, packaged here from Mathlib's `RatFunc.inftyValuation`. Its order function is
`ord_∞ f = -f.intDegree`, its residue field is `k`, and the finite place attached to a monic
irreducible polynomial `q` has residue field `k[X] / (q)`, hence degree `q.natDegree`.

That these are *all* the places is Mathlib's Ostrowski theorem for `k(X)`,
`RatFunc.valuation_isEquiv_infty_or_adic`, read in place vocabulary: because the valuation of a
place is normalized, equivalence of valuations is equality of places, and the `Xor` of Ostrowski
becomes the bijection `TauCeti.Place.ratFuncEquiv`.

## Main definitions

* `TauCeti.Place.infty`: the place at infinity of `k(x)`.
* `TauCeti.Place.ratFuncEquiv`: the classification of the places of `k(x)`.

## Main results

* `TauCeti.Place.ord_infty`: `ord_∞ f = -f.intDegree`.
* `TauCeti.Place.degree_infty`: the place at infinity is rational, `deg P_∞ = 1`
  (Stichtenoth, Proposition 1.2.1(c)).
* `TauCeti.Place.existsUnique_monic_irreducible_span` and
  `TauCeti.Place.degree_adic_eq_natDegree`: the finite places are indexed by the monic
  irreducible polynomials, and `deg P_q = q.natDegree` (Stichtenoth, Proposition 1.2.1(a)).
* `TauCeti.Place.eq_infty_or_exists_eq_adic` and `TauCeti.Place.ratFuncEquiv`: these are all the
  places of `k(x)`, and they are pairwise distinct (Stichtenoth, Theorem 1.2.2).

That `k` is the exact field of constants of `k(x)` — Proposition 1.2.1(d) — is
`TauCeti.algebraicClosure_ratFunc`.

## Implementation notes

`RatFunc.inftyValuation` is stated for a fixed `DecidableEq (RatFunc k)` instance. The place at
infinity fixes that instance to `Classical.decEq`, and `TauCeti.Place.valuation_infty` transports
the identification to any other instance, all such instances being equal.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.2.
-/

public section

noncomputable section

open scoped WithZero

open IsDedekindDomain Polynomial

namespace TauCeti

namespace Place

variable (k : Type*) [Field k]

/-! ### The place at infinity -/

/-- The **place at infinity** of the rational function field: the normalized valuation with
`v_∞ f = exp (f.intDegree)`, for which `x⁻¹` is a prime element (Stichtenoth,
Proposition 1.2.1(b)). -/
def infty : Place k (RatFunc k) :=
  letI := Classical.decEq (RatFunc k)
  { valuation := RatFunc.inftyValuation k
    valuation_surjective := by
      intro γ
      rcases eq_or_ne γ 0 with rfl | hγ
      · exact ⟨0, map_zero _⟩
      · exact ⟨RatFunc.X ^ (WithZero.log γ), by
          rw [RatFunc.inftyValuation.X_zpow, WithZero.exp_log hγ]⟩
    isTrivialOn := inferInstance }

theorem valuation_infty [inst : DecidableEq (RatFunc k)] :
    (infty k).valuation = RatFunc.inftyValuation k := by
  cases Subsingleton.elim inst (Classical.decEq (RatFunc k))
  exact (rfl)

variable {k}

theorem valuation_infty_apply {f : RatFunc k} (hf : f ≠ 0) :
    (infty k).valuation f = WithZero.exp f.intDegree := by
  classical
  rw [valuation_infty, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := k) hf]

/-- The order function of the place at infinity is minus the degree. The junk values
`ord_∞ 0 = 0` and `RatFunc.intDegree 0 = 0` match, so no nonvanishing hypothesis is needed. -/
@[simp]
theorem ord_infty (f : RatFunc k) : (infty k).ord f = -f.intDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Place.ord_def, valuation_infty_apply hf, WithZero.log_exp]

theorem valuation_infty_lt_one_iff {f : RatFunc k} (hf : f ≠ 0) :
    (infty k).valuation f < 1 ↔ f.intDegree < 0 := by
  rw [valuation_infty_apply hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]

/-! ### The residue field at infinity -/

/-- A rational function that is regular at infinity agrees there, to first order, with a
constant: if `deg f ≤ 0` then some `c : k` has `deg (f - c) < 0`. This is the surjectivity of the
constants onto the residue field at infinity, in valuation form. -/
theorem exists_valuation_infty_sub_lt_one {x : RatFunc k} (hx : (infty k).valuation x ≤ 1) :
    ∃ c : k, (infty k).valuation (x - algebraMap k (RatFunc k) c) < 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  rw [valuation_infty_apply hx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact ⟨0, by simpa [valuation_infty_lt_one_iff hx0] using hlt⟩
  set P := x.num with hP
  set Q := x.denom with hQ
  have hP0 : P ≠ 0 := RatFunc.num_ne_zero hx0
  have hQ0 : Q ≠ 0 := x.denom_ne_zero
  have hdeg : P.natDegree = Q.natDegree := by
    have h := heq
    simp only [RatFunc.intDegree, ← hP, ← hQ] at h
    omega
  set c : k := P.leadingCoeff / Q.leadingCoeff with hc
  have hc0 : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.2 hP0) (leadingCoeff_ne_zero.2 hQ0)
  set S : k[X] := P - Polynomial.C c * Q with hS
  refine ⟨c, ?_⟩
  have hxc : x - algebraMap k (RatFunc k) c
      = algebraMap k[X] (RatFunc k) S / algebraMap k[X] (RatFunc k) Q := by
    rw [hS, map_sub, sub_div, RatFunc.num_div_denom, map_mul, RatFunc.algebraMap_C,
      mul_div_assoc, div_self (by simpa using hQ0), mul_one, ← RatFunc.algebraMap_eq_C]
  rcases eq_or_ne S 0 with hS0 | hS0
  · rw [hxc, hS0, map_zero, zero_div, map_zero]
    exact zero_lt_one
  have hSdeg : S.natDegree < Q.natDegree := by
    rw [← hdeg]
    refine natDegree_lt_natDegree hS0 (degree_sub_lt_left ?_ hP0 ?_)
    · rw [degree_C_mul hc0, degree_eq_natDegree hP0, degree_eq_natDegree hQ0, hdeg]
    · rw [leadingCoeff_mul, leadingCoeff_C, hc, div_mul_cancel₀]
      exact leadingCoeff_ne_zero.2 hQ0
  have hxc0 : x - algebraMap k (RatFunc k) c ≠ 0 := by
    rw [hxc]
    exact div_ne_zero (by simpa using hS0) (by simpa using hQ0)
  rw [valuation_infty_lt_one_iff hxc0, hxc,
    RatFunc.intDegree_div (by simpa using hS0) (by simpa using hQ0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  omega

variable (k)

/-- The constants exhaust the residue field of the place at infinity. -/
theorem algebraMap_residueField_infty_surjective :
    Function.Surjective (algebraMap k (infty k).ResidueField) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := exists_valuation_infty_sub_lt_one (((infty k).mem_integers_iff).mp x.2)
  refine ⟨c, ?_⟩
  have h : IsLocalRing.residue _ (algebraMap k (infty k).integers c)
      = algebraMap k (infty k).ResidueField c :=
    (IsScalarTower.algebraMap_apply k (infty k).integers (infty k).ResidueField c).symm
  rw [← h, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    (infty k).mem_maximalIdeal_iff_valuation_lt_one]
  exact hc

/-- **The place at infinity is rational**: its residue field is `k`, so `deg P_∞ = 1`
(Stichtenoth, Proposition 1.2.1(c)). -/
@[simp]
theorem degree_infty : (infty k).degree = 1 := by
  have hbij : Function.Bijective (algebraMap k (infty k).ResidueField) :=
    ⟨(algebraMap k (infty k).ResidueField).injective,
      algebraMap_residueField_infty_surjective k⟩
  rw [degree_eq_finrank,
    ← (AlgEquiv.ofBijective (Algebra.ofId k (infty k).ResidueField) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-! ### The finite places -/

variable {k}

/-- **Each height-one prime of `k[X]` is generated by a unique monic irreducible polynomial**, so
the finite places of `k(x)` are indexed by the monic irreducible polynomials (Stichtenoth,
Proposition 1.2.1(a)). -/
theorem existsUnique_monic_irreducible_span (p : HeightOneSpectrum (k[X])) :
    ∃! q : k[X], q.Monic ∧ Irreducible q ∧ p.asIdeal = Ideal.span {q} := by
  classical
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal p.asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot (by simpa using hg)
  have hspan : p.asIdeal = Ideal.span {g} := by rw [hg, Ideal.submodule_span_eq]
  have hprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hspan ▸ p.isPrime)
  refine ⟨normalize g, ⟨monic_normalize hg0, ((associated_normalize g).prime hprime).irreducible,
    by rw [hspan, Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize g)]⟩, ?_⟩
  rintro q ⟨hqm, -, hqs⟩
  refine eq_of_monic_of_associated hqm (monic_normalize hg0)
    (Ideal.span_singleton_eq_span_singleton.mp ?_)
  rw [← hqs, hspan, Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize g)]

/-- The residue field of a finite place of `k(x)` is `k[X] / (q)` for a generator `q` of its
prime, so its degree is the degree of `q` (Stichtenoth, Proposition 1.2.1(a)). -/
theorem degree_adic_eq_natDegree (p : HeightOneSpectrum (k[X])) {q : k[X]}
    (h : p.asIdeal = Ideal.span {q}) :
    (adic k (RatFunc k) p).degree = q.natDegree := by
  rw [degree_adic, ← finrank_quotient_span_eq_natDegree (K := k) (f := q),
    (Ideal.quotientEquivAlgOfEq k h).toLinearEquiv.finrank_eq]

theorem degree_adic_pos (p : HeightOneSpectrum (k[X])) :
    0 < (adic k (RatFunc k) p).degree := by
  obtain ⟨q, ⟨-, hirr, hspan⟩, -⟩ := existsUnique_monic_irreducible_span p
  exact degree_adic_eq_natDegree p hspan ▸ hirr.natDegree_pos

/-! ### The classification -/

variable (k)

/-- No finite place of `k(x)` is the place at infinity. -/
theorem adic_ne_infty (p : HeightOneSpectrum (k[X])) : adic k (RatFunc k) p ≠ infty k := by
  classical
  intro h
  refine RatFunc.adicValuation_ne_inftyValuation p ?_
  rw [← valuation_adic k (RatFunc k) p, h, valuation_infty]

variable {k}

/-- **Every place of the rational function field is either the place at infinity or the place of
a monic irreducible polynomial** (Stichtenoth, Theorem 1.2.2). This repackages Mathlib's
Ostrowski theorem `RatFunc.valuation_isEquiv_infty_or_adic`: normalization turns its equivalences
of valuations into equalities of places. -/
theorem eq_infty_or_exists_eq_adic (P : Place k (RatFunc k)) :
    P = infty k ∨ ∃ p : HeightOneSpectrum (k[X]), P = adic k (RatFunc k) p := by
  classical
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := P.valuation)).or with h | ⟨p, hp, -⟩
  · exact Or.inl (eq_of_isEquiv (by rwa [valuation_infty]))
  · exact Or.inr ⟨p, eq_of_isEquiv (by rwa [valuation_adic])⟩

variable (k)

/-- **The places of the rational function field** (Stichtenoth, Theorem 1.2.2): they are the
height-one primes of `k[X]`, which by `TauCeti.Place.existsUnique_monic_irreducible_span` are
the monic irreducible polynomials, together with one further point, the place at infinity. -/
def ratFuncEquiv : Option (HeightOneSpectrum (k[X])) ≃ Place k (RatFunc k) :=
  Equiv.ofBijective (fun p => p.elim (infty k) (adic k (RatFunc k)))
    ⟨by
      rintro (_ | p) (_ | q) h
      · rfl
      · exact absurd h.symm (adic_ne_infty k q)
      · exact absurd h (adic_ne_infty k p)
      · exact congrArg some (adic_injective k (RatFunc k) h), by
      intro P
      rcases eq_infty_or_exists_eq_adic P with rfl | ⟨p, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some p, rfl⟩⟩

@[simp]
theorem ratFuncEquiv_none : ratFuncEquiv k none = infty k := (rfl)

@[simp]
theorem ratFuncEquiv_some (p : HeightOneSpectrum (k[X])) :
    ratFuncEquiv k (some p) = adic k (RatFunc k) p := (rfl)

end Place

end TauCeti
