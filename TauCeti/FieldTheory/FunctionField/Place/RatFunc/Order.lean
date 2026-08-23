/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# Orders at the finite places of the rational function field

This file computes the order of a rational function at the finite place associated to an
irreducible polynomial. For `q : k[X]` irreducible and nonzero `f : k(X)`, the answer is the
exponent of `q` in the numerator of `f` minus its exponent in the denominator. This complements
`TauCeti.Place.ord_infty` and is the concrete finite-place calculation used by divisors on the
rational function field.

## Main results

* `TauCeti.Place.ord_adicOfIrreducible_algebraMap`: the order of a nonzero polynomial at `P_q`
  is its multiplicity of `q`.
* `TauCeti.Place.ord_adicOfIrreducible`: the order of a nonzero rational function at `P_q` is the
  difference of the multiplicities in its numerator and denominator.
* `TauCeti.Place.ord_adicOfIrreducible_pos_iff` and
  `TauCeti.Place.ord_adicOfIrreducible_neg_iff`: the zeros and poles at `P_q` are detected by
  divisibility of the reduced numerator and denominator by `q`.
* `TauCeti.Place.ord_adicOfIrreducible_X`: among the finite places, `X` has order one at `P_X`
  and order zero everywhere else.
* `TauCeti.Place.mem_integers_adicOfIrreducible_iff` and
  `TauCeti.Place.residue_adicOfIrreducible_eq_zero_iff`: regularity and vanishing in the residue
  field are detected by the denominator and numerator respectively.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.2.1(a).
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti.Place

variable {k : Type*} [Field k]

/-- The order at the finite place associated to `q` of a nonzero polynomial `r` is the
multiplicity of `q` in `r`. -/
theorem ord_adicOfIrreducible_algebraMap {q r : k[X]} (hq : Irreducible q) (hr : r ≠ 0) :
    (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) r) = multiplicity q r := by
  rw [adicOfIrreducible_def, ord_algebraMap_adic _ _ _ hr,
    HeightOneSpectrum.ofIrreducible_asIdeal]
  exact_mod_cast multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span

/-- An irreducible polynomial has order one at the finite place it defines. -/
@[simp]
theorem ord_adicOfIrreducible_self {q : k[X]} (hq : Irreducible q) :
    (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) q) = 1 := by
  rw [ord_adicOfIrreducible_algebraMap hq hq.ne_zero, multiplicity_self]
  norm_num

open scoped Classical in
/-- Among the finite places, `X` has order one at the place defined by a polynomial associated to
`X` and order zero at every other place. -/
theorem ord_adicOfIrreducible_X {q : k[X]} (hq : Irreducible q) :
    (adicOfIrreducible hq).ord (RatFunc.X : RatFunc k) =
      if Associated q X then 1 else 0 := by
  rw [← RatFunc.algebraMap_X, ord_adicOfIrreducible_algebraMap hq Polynomial.X_ne_zero]
  split_ifs with h
  · rw [← multiplicity_eq_of_associated_left h, multiplicity_self]
    norm_num
  · norm_num
    rw [multiplicity_eq_zero]
    exact fun hdiv ↦ h (hq.associated_of_dvd irreducible_X hdiv)

/-- The order of a nonzero rational function at the finite place associated to `q` is the
multiplicity of `q` in its numerator minus its multiplicity in its denominator. -/
theorem ord_adicOfIrreducible {q : k[X]} (hq : Irreducible q) {f : RatFunc k} (hf : f ≠ 0) :
    (adicOfIrreducible hq).ord f =
      (multiplicity q f.num : ℤ) - multiplicity q f.denom := by
  calc
    (adicOfIrreducible hq).ord f =
        (adicOfIrreducible hq).ord
          (algebraMap k[X] (RatFunc k) f.num / algebraMap k[X] (RatFunc k) f.denom) :=
      congrArg (adicOfIrreducible hq).ord (RatFunc.num_div_denom f).symm
    _ = (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) f.num) -
          (adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) f.denom) :=
      (adicOfIrreducible hq).ord_div (by simpa using RatFunc.num_ne_zero hf)
        (by simpa using RatFunc.denom_ne_zero f)
    _ = (multiplicity q f.num : ℤ) - multiplicity q f.denom := by
      rw [ord_adicOfIrreducible_algebraMap hq (RatFunc.num_ne_zero hf),
        ord_adicOfIrreducible_algebraMap hq (RatFunc.denom_ne_zero f)]

private theorem not_dvd_right_of_dvd_left {q a b : k[X]} (hq : Irreducible q)
    (hab : IsCoprime a b) (ha : q ∣ a) : ¬q ∣ b := by
  intro hb
  exact hq.not_isUnit (hab.isUnit_of_dvd' ha hb)

/-- A nonzero rational function has a zero at `P_q` exactly when `q` divides its reduced
numerator. -/
@[simp]
theorem ord_adicOfIrreducible_pos_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k}
    (hf : f ≠ 0) :
    0 < (adicOfIrreducible hq).ord f ↔ q ∣ f.num := by
  rw [ord_adicOfIrreducible hq hf]
  constructor
  · intro h
    apply multiplicity_ne_zero.mp
    omega
  · intro hnum
    have hnum' : multiplicity q f.num ≠ 0 := multiplicity_ne_zero.mpr hnum
    have hden : multiplicity q f.denom = 0 :=
      multiplicity_eq_zero.mpr
        (not_dvd_right_of_dvd_left hq f.isCoprime_num_denom hnum)
    omega

/-- A nonzero rational function has a pole at `P_q` exactly when `q` divides its reduced
denominator. -/
@[simp]
theorem ord_adicOfIrreducible_neg_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k}
    (hf : f ≠ 0) :
    (adicOfIrreducible hq).ord f < 0 ↔ q ∣ f.denom := by
  rw [ord_adicOfIrreducible hq hf]
  constructor
  · intro h
    apply multiplicity_ne_zero.mp
    omega
  · intro hden
    have hnum : multiplicity q f.num = 0 :=
      multiplicity_eq_zero.mpr
        (not_dvd_right_of_dvd_left hq f.isCoprime_num_denom.symm hden)
    have hden' : multiplicity q f.denom ≠ 0 := multiplicity_ne_zero.mpr hden
    omega

/-- A nonzero rational function is a unit at `P_q` exactly when `q` divides neither its reduced
numerator nor its reduced denominator. -/
@[simp]
theorem ord_adicOfIrreducible_eq_zero_iff {q : k[X]} (hq : Irreducible q) {f : RatFunc k}
    (hf : f ≠ 0) :
    (adicOfIrreducible hq).ord f = 0 ↔ ¬q ∣ f.num ∧ ¬q ∣ f.denom := by
  constructor
  · intro hord
    constructor
    · intro hnum
      have : 0 < (adicOfIrreducible hq).ord f :=
        (ord_adicOfIrreducible_pos_iff hq hf).mpr hnum
      omega
    · intro hden
      have : (adicOfIrreducible hq).ord f < 0 :=
        (ord_adicOfIrreducible_neg_iff hq hf).mpr hden
      omega
  · rintro ⟨hnum, hden⟩
    have hnpos : ¬0 < (adicOfIrreducible hq).ord f :=
      mt (ord_adicOfIrreducible_pos_iff hq hf).mp hnum
    have hnneg : ¬(adicOfIrreducible hq).ord f < 0 :=
      mt (ord_adicOfIrreducible_neg_iff hq hf).mp hden
    omega

/-! ### The valuation ring and residue field -/

/-- A rational function is regular at the finite place `P_q` exactly when `q` does not divide
its reduced denominator. This statement includes the zero rational function. -/
theorem mem_integers_adicOfIrreducible_iff {q : k[X]} (hq : Irreducible q) (f : RatFunc k) :
    f ∈ (adicOfIrreducible hq).integers ↔ ¬q ∣ f.denom := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [zero_mem, RatFunc.denom_zero, true_iff]
    exact hq.not_dvd_one
  · rw [(adicOfIrreducible hq).mem_integers_iff_ord_nonneg, ← not_lt,
      ord_adicOfIrreducible_neg_iff hq hf]

/-- The valuation at `P_q` is at most one exactly when `q` does not divide the reduced
denominator. This is the simp-normal form of `mem_integers_adicOfIrreducible_iff`. -/
@[simp]
theorem valuation_adicOfIrreducible_le_one_iff {q : k[X]} (hq : Irreducible q)
    (f : RatFunc k) :
    (HeightOneSpectrum.ofIrreducible hq).valuation (RatFunc k) f ≤ 1 ↔
      ¬q ∣ f.denom := by
  rw [← valuation_adicOfIrreducible hq, ← (adicOfIrreducible hq).mem_integers_iff,
    mem_integers_adicOfIrreducible_iff hq]

/-- A function regular at `P_q` has zero residue exactly when `q` divides its reduced numerator. -/
theorem residue_adicOfIrreducible_eq_zero_iff {q : k[X]} (hq : Irreducible q)
    (f : (adicOfIrreducible hq).integers) :
    IsLocalRing.residue (adicOfIrreducible hq).integers f = 0 ↔
      q ∣ (f : RatFunc k).num := by
  rcases eq_or_ne (f : RatFunc k) 0 with hf | hf
  · have : f = 0 := Subtype.ext hf
    subst f
    simp [RatFunc.num_zero]
  · rw [(adicOfIrreducible hq).residue_eq_zero_iff_ord_pos hf,
      ord_adicOfIrreducible_pos_iff hq hf]

/-- An element of the valuation ring at `P_q` is a nonunit exactly when `q` divides its reduced
numerator. This is the simp-normal form of `residue_adicOfIrreducible_eq_zero_iff`. -/
@[simp]
theorem not_isUnit_integers_adicOfIrreducible_iff {q : k[X]} (hq : Irreducible q)
    (f : (adicOfIrreducible hq).integers) :
    ¬IsUnit f ↔ q ∣ (f : RatFunc k).num := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    ← IsLocalRing.residue_eq_zero_iff, residue_adicOfIrreducible_eq_zero_iff hq]

end TauCeti.Place
