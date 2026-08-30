/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# Totally ramified places, and the Eisenstein criterion

Let `F' / k'` be a finite extension of the field extension `F / k`. A place `P'` of `F' / k'` is
**totally ramified** over `F` when its ramification index is as large as the fundamental
inequality allows, `e(P' ∣ P) = [F' : F]`. The inequality then forces the rest of the picture:
the relative degree is `1` and `P'` is the *only* place of `F'` lying over `P`, which is
Stichtenoth's Definition 3.1.13 read at `P`.

The criterion that produces totally ramified places is Eisenstein's. Call `φ ∈ F[X]`
*Eisenstein at a place `P` of `F / k`* when its leading coefficient is a unit of `𝒪_P`, every
coefficient below the leading one vanishes at `P`, and the constant coefficient vanishes to
order exactly one — the three conditions of Mathlib's `Polynomial.IsEisensteinAt` at the maximal
ideal of `𝒪_P`, read off the order function so that a polynomial over `F` may be tested. If `y`
generates `F'` over `F` and its minimal polynomial is Eisenstein at `P`, then every place `P'`
of `F'` over `P` is totally ramified and `y` is a prime element at `P'`.

The proof is the Newton-polygon computation, run with the strict triangle inequality. Write
`n = deg φ`, `e = e(P' ∣ P)` and `m = ord_{P'} y`, and expand `0 = φ(y)` as the sum of its
`n + 1` terms. The term of index `i < n` has order at least `e + i·m` because its coefficient
vanishes at `P`, the term of index `0` has order exactly `e`, and the leading term has order
`n·m`. If any one of the terms had order strictly smaller than all the others, the strict
triangle inequality would make the sum nonzero; so neither the leading term nor the constant
term can dominate, and comparing the two possibilities gives `n·m = e` — first for `m ≤ 0`,
where the leading term would dominate, and then for the two ways `n·m` and `e` could differ.
Since `e ≤ [F' : F] = n` and `m ≥ 1`, this forces `e = n` and `m = 1`.

## Main definitions

* `TauCeti.Place.IsTotallyRamified`: `e(P' ∣ P) = [F' : F]` (Stichtenoth, Definition 3.1.13).
* `TauCeti.Place.IsEisensteinAt`: a polynomial over `F` is Eisenstein at a place of `F / k`.

## Main results

* `TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified` and
  `TauCeti.Place.eq_of_isTotallyRamified`: a totally ramified place has relative degree `1` and
  is the only place lying over the place below it, packaged as
  `TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified`.
* `TauCeti.Place.IsEisensteinAt.natDegree_pos`: an Eisenstein polynomial has positive degree.
* `TauCeti.Place.natDegree_mul_ord_eq_ramificationIdx`: the order of a root of an Eisenstein
  polynomial, `n · ord_{P'} y = e(P' ∣ P)`.
* `TauCeti.Place.isTotallyRamified_of_isEisensteinAt` and
  `TauCeti.Place.ord_eq_one_of_isEisensteinAt`: **the Eisenstein criterion** (Stichtenoth,
  Proposition 3.1.15).
* `TauCeti.Place.isEisensteinAt_map`: a polynomial over `𝒪_P` that is Eisenstein at the maximal
  ideal of `𝒪_P` in the sense of Mathlib's `Polynomial.IsEisensteinAt` is Eisenstein at `P` in
  the sense used here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section TotallyRamified

variable (F)

/-- A place `P'` of `F' / k'` is **totally ramified** over `F` when its ramification index is
the full degree `[F' : F]`. By the fundamental inequality this is the largest value the
ramification index can take, and it forces the relative degree to be `1`
(`TauCeti.Place.relativeDegree_eq_one_of_isTotallyRamified`) and `P'` to be the only place of
`F'` over the place of `F` below it (`TauCeti.Place.eq_of_isTotallyRamified`): the situation
Stichtenoth's Definition 3.1.13 calls total ramification of that place of `F`. -/
def IsTotallyRamified (P' : Place k' F') : Prop :=
  ramificationIdx F P' = Module.finrank F F'

/-- Total ramification unfolds to its defining equality of the ramification index with the
degree. -/
theorem isTotallyRamified_iff {P' : Place k' F'} :
    IsTotallyRamified F P' ↔ ramificationIdx F P' = Module.finrank F F' := Iff.rfl

variable (k) [FiniteDimensional F F']

/-- **A totally ramified place has relative degree one**: the fundamental inequality has no room
left for a residue field extension. -/
@[simp]
theorem relativeDegree_eq_one_of_isTotallyRamified {P' : Place k' F'}
    (h : IsTotallyRamified F P') : relativeDegree k F P' = 1 := by
  have hle := ramificationIdx_mul_relativeDegree_le_finrank k F P'
  rw [h] at hle
  have hpos : 0 < Module.finrank F F' := Module.finrank_pos
  have h1 := one_le_relativeDegree k F P'
  nlinarith

/-- **A totally ramified place is the only place over the place below it**: a second place in
the fibre would contribute at least `1` more to the fundamental inequality. -/
theorem eq_of_isTotallyRamified {P' Q' : Place k' F'} (h : IsTotallyRamified F P')
    (hQ : Q'.restrict k F = P'.restrict k F) : Q' = P' := by
  classical
  by_contra hne
  have hle := sum_ramificationIdx_mul_relativeDegree_le_finrank k F (P'.restrict k F)
    {P', Q'} (by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · rfl
      · exact hQ)
  rw [Finset.sum_pair (Ne.symm hne), h] at hle
  have h1 := one_le_relativeDegree k F P'
  have h2 := ramificationIdx_pos F Q'
  have h3 := one_le_relativeDegree k F Q'
  nlinarith

/-- The fibre of `TauCeti.Place.restrict` over the place below a totally ramified place is a
single point. -/
@[simp]
theorem setOf_restrict_eq_eq_singleton_of_isTotallyRamified {P' : Place k' F'}
    (h : IsTotallyRamified F P') :
    {Q' : Place k' F' | Q'.restrict k F = P'.restrict k F} = {P'} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun _ hQ => eq_of_isTotallyRamified k F h hQ⟩

end TotallyRamified

section Eisenstein

/-- A polynomial over `F` is **Eisenstein at a place `P` of `F / k`** when its leading
coefficient is a unit of `𝒪_P`, every coefficient below the leading one vanishes at `P`, and the
constant coefficient vanishes to order exactly one. For a polynomial with coefficients in `𝒪_P`
these are the three conditions of Mathlib's `Polynomial.IsEisensteinAt` at the maximal ideal of
`𝒪_P`; see `TauCeti.Place.isEisensteinAt_map`. The conditions are stated through the valuation
and the order function rather than through membership in the maximal ideal, so that a polynomial
over `F` — for instance a minimal polynomial — may be tested directly; the junk value
`ord_P 0 = 0` is avoided by using the valuation in the condition that admits zero coefficients. -/
structure IsEisensteinAt (P : Place k F) (φ : F[X]) : Prop where
  /-- The leading coefficient is a unit of `𝒪_P`; monic polynomials qualify. -/
  ord_leadingCoeff : P.ord φ.leadingCoeff = 0
  /-- Every coefficient below the leading one lies in the maximal ideal of `𝒪_P`. -/
  valuation_coeff_lt_one : ∀ i < φ.natDegree, P.valuation (φ.coeff i) < 1
  /-- The constant coefficient vanishes to order exactly one. -/
  ord_coeff_zero : P.ord (φ.coeff 0) = 1

/-- An Eisenstein polynomial has positive degree: in degree zero the leading coefficient *is*
the constant coefficient, and the two order conditions contradict each other. -/
theorem IsEisensteinAt.natDegree_pos {P : Place k F} {φ : F[X]} (h : P.IsEisensteinAt φ) :
    0 < φ.natDegree := by
  rcases Nat.eq_zero_or_pos φ.natDegree with h0 | h0
  · have hl := h.ord_leadingCoeff
    rw [Polynomial.leadingCoeff, h0, h.ord_coeff_zero] at hl
    exact absurd hl (by decide)
  · exact h0

/-- An element of `𝒪_P` of order at least two lies in the square of the maximal ideal: a prime
element `t` for `P` factors it as `t · t · u` with `u ∈ 𝒪_P`. -/
private theorem mem_maximalIdeal_sq_of_two_le_ord (P : Place k F) {f : P.integers}
    (h : 2 ≤ P.ord (f : F)) : f ∈ IsLocalRing.maximalIdeal P.integers ^ 2 := by
  rcases eq_or_ne (f : F) 0 with hf0 | hf0
  · have hf : f = 0 := Subtype.ext hf0
    rw [hf]
    exact Submodule.zero_mem _
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at ht
    exact absurd ht (by decide)
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hu : (f : F) / (t * t) ∈ P.integers := by
    refine P.mem_integers_iff_ord_nonneg.mpr ?_
    rw [P.ord_div hf0 (mul_ne_zero ht0 ht0), P.ord_mul ht0 ht0, ht]
    omega
  have hcoe : ((⟨t, htmem⟩ : P.integers) : F) = t := rfl
  have hmem : (⟨t, htmem⟩ : P.integers) ∈ IsLocalRing.maximalIdeal P.integers :=
    (P.mem_maximalIdeal_iff_ord_pos (by rw [hcoe]; exact ht0)).mpr (by rw [hcoe, ht]; omega)
  have hfeq : f = ⟨t, htmem⟩ * ⟨t, htmem⟩ * ⟨(f : F) / (t * t), hu⟩ := by
    refine Subtype.ext ?_
    push_cast
    field_simp
  rw [hfeq, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hmem hmem)

/-- **Mathlib's Eisenstein condition is this one**: a polynomial over `𝒪_P` of positive degree
which is Eisenstein at the maximal ideal of `𝒪_P` in the sense of `Polynomial.IsEisensteinAt`
becomes, read in `F[X]`, a polynomial Eisenstein at `P`. No monicity is needed: the
`Polynomial.IsEisensteinAt.leading` field already puts the leading coefficient outside the
maximal ideal, hence makes it a unit of `𝒪_P`. The `Polynomial.IsEisensteinAt.notMem` field is
what pins the order of the constant coefficient down to exactly one. -/
theorem isEisensteinAt_map (P : Place k F) {ψ : Polynomial P.integers}
    (hdeg : 0 < ψ.natDegree) (h : ψ.IsEisensteinAt (IsLocalRing.maximalIdeal P.integers)) :
    P.IsEisensteinAt (ψ.map (algebraMap P.integers F)) := by
  have hinj : Function.Injective (algebraMap P.integers F) := fun a b hab =>
    Subtype.ext (by simpa [ValuationSubring.algebraMap_apply] using hab)
  have hnat : (ψ.map (algebraMap P.integers F)).natDegree = ψ.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj ψ
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · have hlc : (ψ.map (algebraMap P.integers F)).leadingCoeff = (ψ.leadingCoeff : F) := by
      rw [Polynomial.leadingCoeff_map_of_injective hinj, ValuationSubring.algebraMap_apply]
    have hlcne : ψ.leadingCoeff ≠ 0 := fun h0 =>
      h.leading (by rw [h0]; exact Submodule.zero_mem _)
    have hlc0 : (ψ.leadingCoeff : F) ≠ 0 := fun h0 => hlcne (Subtype.ext h0)
    have hnonneg : 0 ≤ P.ord (ψ.leadingCoeff : F) :=
      P.mem_integers_iff_ord_nonneg.mp ψ.leadingCoeff.2
    have hnotpos : ¬0 < P.ord (ψ.leadingCoeff : F) := fun hp =>
      h.leading ((P.mem_maximalIdeal_iff_ord_pos hlc0).mpr hp)
    rw [hlc]
    omega
  · rw [hnat] at hi
    rw [Polynomial.coeff_map, ValuationSubring.algebraMap_apply]
    exact P.mem_maximalIdeal_iff_valuation_lt_one.mp (h.mem hi)
  · have hne : ((ψ.coeff 0 : P.integers) : F) ≠ 0 := by
      intro h0
      have hz : ψ.coeff 0 = 0 := Subtype.ext h0
      exact h.notMem (by rw [hz]; exact Submodule.zero_mem _)
    have hpos : 0 < P.ord ((ψ.coeff 0 : P.integers) : F) :=
      (P.mem_maximalIdeal_iff_ord_pos hne).mp (h.mem hdeg)
    have hlt : ¬2 ≤ P.ord ((ψ.coeff 0 : P.integers) : F) := fun hh =>
      h.notMem (mem_maximalIdeal_sq_of_two_le_ord P hh)
    rw [Polynomial.coeff_map, ValuationSubring.algebraMap_apply]
    omega

variable {P' : Place k' F'}

/-- Comparison of valuations from a comparison of orders, with the junk value `ord_P 0 = 0`
guarded: the zero element has valuation `0`, below the valuation of any nonzero element. -/
private theorem valuation_lt_of_ord_lt {a b : F'} (hb : b ≠ 0)
    (h : a ≠ 0 → P'.ord b < P'.ord a) : P'.valuation a < P'.valuation b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]
    exact zero_lt_iff.mpr (P'.valuation.ne_zero_iff.mpr hb)
  · rw [P'.valuation_eq_exp_neg_ord ha, P'.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]
    have := h ha
    omega

/-- **The strict triangle inequality for a finite sum**: a sum with a strictly dominant term is
nonzero. -/
private theorem sum_ne_zero_of_forall_valuation_lt (Q' : Place k' F') {ι : Type*} {s : Finset ι}
    {T : ι → F'} {j : ι} (hj : j ∈ s) (hTj : T j ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → Q'.valuation (T i) < Q'.valuation (T j)) :
    ∑ i ∈ s, T i ≠ 0 := by
  classical
  intro hsum
  have hval := Q'.valuation.map_sum_eq_of_lt hj fun i hi => by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact hlt i hi.1 hi.2
  rw [hsum, map_zero] at hval
  exact (Q'.valuation.ne_zero_iff.mpr hTj) hval.symm

variable (k F) [Algebra.IsIntegral F F']

/-- **The order of a root of an Eisenstein polynomial** (Stichtenoth, Proposition 3.1.15): if
`φ ∈ F[X]` of degree `n` is Eisenstein at the place of `F / k` below `P'`, then a root `y ∈ F'`
of `φ` satisfies `n · ord_{P'} y = e(P' ∣ P)`. In particular `n` divides the ramification index,
which is the whole content of the criterion. -/
theorem natDegree_mul_ord_eq_ramificationIdx {φ : F[X]}
    (hφ : (P'.restrict k F).IsEisensteinAt φ)
    {y : F'} (hy : aeval y φ = 0) :
    (φ.natDegree : ℤ) * P'.ord y = ramificationIdx F P' := by
  classical
  have hdeg : 0 < φ.natDegree := hφ.natDegree_pos
  set P := P'.restrict k F with hPdef
  set n := φ.natDegree with hndef
  set e : ℤ := (ramificationIdx F P' : ℤ) with hedef
  have he0 : 0 < e := by
    rw [hedef]
    exact_mod_cast ramificationIdx_pos F P'
  have hord0 := hφ.ord_coeff_zero
  have hc0 : φ.coeff 0 ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hord0
    exact absurd hord0 (by decide)
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h : algebraMap F F' (φ.coeff 0) = 0 := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero] using hy
    exact hc0 ((map_eq_zero (algebraMap F F')).mp h)
  set m := P'.ord y with hmdef
  set T : ℕ → F' := fun i => algebraMap F F' (φ.coeff i) * y ^ i with hTdef
  have hsum : ∑ i ∈ Finset.range (n + 1), T i = 0 := by
    rw [← hy, Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
  have hTne : ∀ i, φ.coeff i ≠ 0 → T i ≠ 0 := fun i hci =>
    mul_ne_zero (by simpa using hci) (pow_ne_zero i hy0)
  have hordT : ∀ i, φ.coeff i ≠ 0 → P'.ord (T i) = e * P.ord (φ.coeff i) + i * m := by
    intro i hci
    have h1 : algebraMap F F' (φ.coeff i) ≠ 0 := by simpa using hci
    rw [hTdef]
    simp only
    rw [P'.ord_mul h1 (pow_ne_zero i hy0), P'.ord_pow, ord_algebraMap_restrict k F P']
  have hφ0 : φ ≠ 0 := fun h => by simp [h, hndef] at hdeg
  have hcoeff_n : φ.coeff n = φ.leadingCoeff := by rw [hndef, Polynomial.coeff_natDegree]
  have hcn0 : φ.coeff n ≠ 0 := by
    rw [hcoeff_n]
    exact Polynomial.leadingCoeff_ne_zero.mpr hφ0
  have hTn0 : T n ≠ 0 := hTne n hcn0
  have hT00 : T 0 ≠ 0 := hTne 0 hc0
  have hordTn : P'.ord (T n) = n * m := by
    rw [hordT n hcn0, hcoeff_n, hφ.ord_leadingCoeff, mul_zero, zero_add]
  have hordT0 : P'.ord (T 0) = e := by
    rw [hordT 0 hc0, hord0, mul_one, Nat.cast_zero, zero_mul, add_zero]
  have hlow : ∀ i, i < n → φ.coeff i ≠ 0 → e + i * m ≤ P'.ord (T i) := by
    intro i hi hci
    have hpos : 0 < P.ord (φ.coeff i) :=
      (P.valuation_lt_one_iff_ord_pos hci).mp (hφ.valuation_coeff_lt_one i hi)
    have hge : e ≤ e * P.ord (φ.coeff i) := le_mul_of_one_le_right he0.le hpos
    rw [hordT i hci]
    linarith
  -- Step 1: the root has positive order, else the leading term dominates.
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have hm0 : m ≤ 0 := by omega
    refine sum_ne_zero_of_forall_valuation_lt P' (Finset.self_mem_range_succ n) hTn0 ?_ hsum
    intro i hi hne
    refine valuation_lt_of_ord_lt hTn0 fun hi0 => ?_
    have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
    have hilt : i < n := by
      rw [Finset.mem_range] at hi
      omega
    have hle : (n : ℤ) * m ≤ (i : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by exact_mod_cast hilt.le) hm0
    have := hlow i hilt hci
    rw [hordTn]
    linarith
  -- Step 2: neither the leading term nor the constant term may dominate.
  have hkey : (n : ℤ) * m = e := by
    rcases lt_trichotomy ((n : ℤ) * m) e with hlt | heq | hgt
    · refine absurd hsum (sum_ne_zero_of_forall_valuation_lt P'
        (Finset.self_mem_range_succ n) hTn0 ?_)
      intro i hi hne
      refine valuation_lt_of_ord_lt hTn0 fun hi0 => ?_
      have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
      have hilt : i < n := by
        rw [Finset.mem_range] at hi
        omega
      have hnn : (0 : ℤ) ≤ (i : ℤ) * m := mul_nonneg (Int.natCast_nonneg i) (by omega)
      have := hlow i hilt hci
      rw [hordTn]
      linarith
    · exact heq
    · refine absurd hsum (sum_ne_zero_of_forall_valuation_lt P'
        (Finset.mem_range.mpr (by omega)) hT00 ?_)
      intro i hi hne
      refine valuation_lt_of_ord_lt hT00 fun hi0 => ?_
      have hci : φ.coeff i ≠ 0 := fun h => hi0 (by rw [hTdef]; simp [h])
      rw [hordT0]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) with rfl | hilt
      · rw [hordTn]
        linarith
      · have hi1 : 1 ≤ (i : ℤ) := by
          have : 0 < i := Nat.pos_of_ne_zero hne
          exact_mod_cast this
        have hnn : (1 : ℤ) ≤ (i : ℤ) * m := one_le_mul_of_one_le_of_one_le hi1 hm1
        have := hlow i hilt hci
        linarith
  rw [hkey]

variable [FiniteDimensional F F']

private theorem ramificationIdx_eq_and_ord_eq_one {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    IsTotallyRamified F P' ∧ P'.ord y = 1 := by
  have hint : IsIntegral F y := IsIntegral.of_finite F y
  have hfr : Module.finrank F F' = (minpoly F y).natDegree := by
    rw [← IntermediateField.finrank_top' (F := F) (E := F'), ← htop,
      IntermediateField.adjoin.finrank hint]
  have hdeg : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have hkey := natDegree_mul_ord_eq_ramificationIdx k F hφ (minpoly.aeval F y)
  have hle : ramificationIdx F P' ≤ Module.finrank F F' := ramificationIdx_le_finrank F P'
  rw [hfr] at hle
  have hle' : (ramificationIdx F P' : ℤ) ≤ ((minpoly F y).natDegree : ℤ) := by
    exact_mod_cast hle
  have he0 : (0 : ℤ) < (ramificationIdx F P' : ℤ) := by exact_mod_cast ramificationIdx_pos F P'
  have hn0 : (0 : ℤ) < ((minpoly F y).natDegree : ℤ) := by exact_mod_cast hdeg
  have hm1 : 1 ≤ P'.ord y := by nlinarith
  have hm : P'.ord y = 1 := by nlinarith
  refine ⟨?_, hm⟩
  have : (ramificationIdx F P' : ℤ) = (Module.finrank F F' : ℤ) := by
    rw [hfr, ← hkey, hm, mul_one]
  exact_mod_cast this

/-- **The Eisenstein criterion** (Stichtenoth, Proposition 3.1.15): if `F' = F(y)` and the
minimal polynomial of `y` over `F` is Eisenstein at the place of `F / k` below `P'`, then `P'`
is totally ramified over `F`. Together with
`TauCeti.Place.setOf_restrict_eq_eq_singleton_of_isTotallyRamified` this says that the place
below `P'` is totally ramified in `F' / F`: it has exactly one extension, of ramification index
`[F' : F]` and relative degree `1`. -/
theorem isTotallyRamified_of_isEisensteinAt {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    IsTotallyRamified F P' :=
  (ramificationIdx_eq_and_ord_eq_one k F htop hφ).1

/-- **A generator with an Eisenstein minimal polynomial is a prime element** (Stichtenoth,
Proposition 3.1.15). -/
theorem ord_eq_one_of_isEisensteinAt {y : F'}
    (htop : IntermediateField.adjoin F {y} = ⊤)
    (hφ : (P'.restrict k F).IsEisensteinAt (minpoly F y)) :
    P'.ord y = 1 :=
  (ramificationIdx_eq_and_ord_eq_one k F htop hφ).2

end Eisenstein

end Place

end TauCeti
