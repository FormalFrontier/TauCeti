/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import TauCeti.Algebra.Polynomial.CommonXPower
public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Adic
public import TauCeti.RingTheory.Valuation.Polynomial

/-!
# Valuation rings of an algebraic function field are the rings of places

Stichtenoth defines a *valuation ring* of `F / k` to be a subring `𝒪` with `k ⊊ 𝒪 ⊊ F` such that
`z ∈ 𝒪` or `z⁻¹ ∈ 𝒪` for every `z : F` (Definition 1.1.4), and proves that every such ring is a
discrete valuation ring (Theorem 1.1.6), so that the places of `F / k` are exactly the proper
valuation subrings of `F` containing the constants (Theorem 1.1.13). This file proves that
recognition theorem: `TauCeti.Place.ofValuationSubring` turns a proper `ValuationSubring F`
containing `k` into a place whose valuation ring is the given one, and
`TauCeti.Place.existsUnique_integers_eq` says the place is unique with that property.

The mathematical content is the discreteness, `TauCeti.isDiscreteValuationRing_of_isFunctionField`,
and the argument is Stichtenoth's. The engine is Lemma 1.1.7: if `x` is a nonzero nonunit of `𝒪`,
then a family `y i` of nonunits whose valuations increase strictly and stay above `v x` is linearly
independent over `k(x)`, hence has at most `[F : k(x)]` members. Because `x` is transcendental —
a nonunit cannot be algebraic over `k` — that degree is finite, so `𝒪` admits no infinite chain of
nonunits of strictly increasing valuation. Two applications finish the proof: the valuations of the
nonzero nonunits attain a maximum, at an element `t`, and every nonzero `z : 𝒪` is `t ^ n` times a
unit. That is exactly Mathlib's `HasUnitMulPowIrreducibleFactorization`.

## Main results

* `TauCeti.linearIndependent_of_strictMono_valuation`: Stichtenoth, Lemma 1.1.7.
* `TauCeti.isDiscreteValuationRing_of_isFunctionField`: a proper valuation subring of an algebraic
  function field containing the constants is a discrete valuation ring (Stichtenoth,
  Theorem 1.1.6).
* `TauCeti.Place.ofValuationSubring`, with `TauCeti.Place.valuation_ofValuationSubring` and
  `TauCeti.Place.integers_ofValuationSubring`: the place attached to such a valuation subring,
  its valuation, and the fact that its valuation ring is the subring one started from.
* `TauCeti.Place.existsUnique_integers_eq`: the place is the unique one with that valuation ring
  (Stichtenoth, Theorem 1.1.13).

## Implementation notes

Everything is phrased through `ValuationSubring.valuation`, the tautological valuation of a
valuation subring, rather than through membership in the subring: `x ∈ A` is `A.valuation x ≤ 1`
and `x` is a nonunit of `A` exactly when `A.valuation x < 1`, and in this vocabulary the estimates
of Lemma 1.1.7 are one-line applications of `Valuation.map_sum_eq_of_lt`. The value group of
`A.valuation` is only known to be a linearly ordered commutative group with zero; that it is `ℤᵐ⁰`
is the conclusion, not a hypothesis, and it is obtained by handing the discrete valuation ring back
to Mathlib's `IsDiscreteValuationRing.maximalIdeal` and the adic valuation of that height-one
prime.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.1.6, Lemma 1.1.7 and Theorem 1.1.13.
-/

public section

noncomputable section

open IntermediateField Polynomial

open scoped IntermediateField.algebraAdjoinAdjoin

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] {A : ValuationSubring F}

/-! ### Stichtenoth's chain estimate -/

/-- **Stichtenoth, Lemma 1.1.7.** Let `x` be a nonzero nonunit of a valuation subring `A` of `F`
containing the constants. A family of nonunits of `A` whose valuations increase strictly
along a linear order, and are all at least `A.valuation x` — hence nonzero — is linearly
independent over `k(x)`.

In Stichtenoth's additive notation the hypothesis reads
`ord x ≥ ord (y i₀) > ord (y i₁) > ⋯ > 0`, and the conclusion bounds the length of such a chain by
`[F : k(x)]`. -/
theorem linearIndependent_of_strictMono_valuation (hk : ∀ c : k, algebraMap k F c ∈ A) {x : F}
    (hx0 : x ≠ 0) (hx : A.valuation x < 1) {ι : Type*} [LinearOrder ι] {y : ι → F}
    (hy : ∀ i, A.valuation (y i) < 1)
    (hmono : StrictMono fun i ↦ A.valuation (y i)) (hxy : ∀ i, A.valuation x ≤ A.valuation (y i)) :
    LinearIndependent k⟮x⟯ y := by
  classical
  have hxpos : 0 < A.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  have hy0 : ∀ i, y i ≠ 0 := fun i ↦ (Valuation.ne_zero_iff _).1 (hxpos.trans_le (hxy i)).ne'
  have hkle : ∀ c : k, A.valuation (algebraMap k F c) ≤ 1 :=
    fun c ↦ (A.valuation_le_one_iff _).2 (hk c)
  have : A.valuation.IsTrivialOn k := .of_le_one _ hkle
  have hxtr : Transcendental k x := Valuation.transcendental_of_ne_one k x hx0 hx.ne
  have hinj : Function.Injective (aeval x : k[X] →ₐ[k] F) := transcendental_iff_injective.mp hxtr
  rw [← LinearIndependent.iff_fractionRing (Algebra.adjoin k {x}) k⟮x⟯, linearIndependent_iff']
  intro s g hsum i₀ hi₀
  by_contra hg0
  -- Write the coefficients as polynomials in `x`.
  have hrange : ∀ z : F, z ∈ Algebra.adjoin k ({x} : Set F) → ∃ p : k[X], aeval x p = z := by
    intro z hz
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  choose p hp using fun i ↦ hrange (g i : F) (g i).2
  have hpa : ∀ i, algebraMap (Algebra.adjoin k ({x} : Set F)) F (g i) = aeval x (p i) :=
    fun i ↦ by rw [Subalgebra.algebraMap_apply]; exact (hp i).symm
  have hpzero : ∀ i, p i = 0 ↔ g i = 0 := fun i ↦ by
    rw [← hinj.eq_iff, map_zero, hp i, ZeroMemClass.coe_eq_zero]
  obtain ⟨m, q, hfactor, j₁, hj₁s, hqj₁⟩ :=
    Polynomial.exists_common_X_pow_factor s p ⟨i₀, hi₀, fun h ↦ hg0 ((hpzero i₀).mp h)⟩
  -- The relation, with the common factor `x ^ m` removed.
  have hsumF : ∑ i ∈ s, aeval x (q i) * y i = 0 := by
    refine mul_left_cancel₀ (pow_ne_zero m hx0) ?_
    rw [Finset.mul_sum, mul_zero, ← hsum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Algebra.smul_def, hpa i, hfactor i hi]
    simp [mul_assoc]
  -- Among the indices whose polynomial has nonzero constant term, take the largest.
  have hs'ne : (s.filter fun i ↦ (q i).coeff 0 ≠ 0).Nonempty :=
    ⟨j₁, Finset.mem_filter.2 ⟨hj₁s, hqj₁⟩⟩
  set j := (s.filter fun i ↦ (q i).coeff 0 ≠ 0).max' hs'ne
  obtain ⟨hjs, hqj⟩ := Finset.mem_filter.1 ((s.filter fun i ↦ (q i).coeff 0 ≠ 0).max'_mem hs'ne)
  have hvj : A.valuation (aeval x (q j)) = 1 := valuation_aeval_eq_one hk hx hqj
  -- Its term strictly dominates every other term of the relation.
  have hkey : ∀ i ∈ s \ {j},
      A.valuation (aeval x (q i) * y i) < A.valuation (aeval x (q j) * y j) := by
    intro i hi
    obtain ⟨his, hij⟩ := Finset.mem_sdiff.1 hi
    rw [Finset.notMem_singleton] at hij
    rw [map_mul, map_mul, hvj, one_mul]
    rcases hij.lt_or_gt with hlt | hgt
    · calc A.valuation (aeval x (q i)) * A.valuation (y i)
          ≤ 1 * A.valuation (y i) := by gcongr; exact A.valuation.aeval_le_one hkle hx.le _
        _ = A.valuation (y i) := one_mul _
        _ < A.valuation (y j) := hmono hlt
    · have hqi0 : (q i).coeff 0 = 0 := by
        by_contra hc
        exact absurd ((s.filter fun i ↦ (q i).coeff 0 ≠ 0).le_max' i
          (Finset.mem_filter.2 ⟨his, hc⟩)) (not_le.2 hgt)
      obtain ⟨r, hr⟩ := X_dvd_iff.2 hqi0
      have hqix : aeval x (q i) = x * aeval x r := by rw [hr]; simp
      calc A.valuation (aeval x (q i)) * A.valuation (y i)
          = A.valuation x * A.valuation (aeval x r) * A.valuation (y i) := by
            rw [hqix, map_mul]
        _ ≤ A.valuation x * 1 * A.valuation (y i) := by
            gcongr; exact A.valuation.aeval_le_one hkle hx.le _
        _ = A.valuation x * A.valuation (y i) := by rw [mul_one]
        _ < A.valuation x * 1 := mul_lt_mul_of_pos_left (hy i) hxpos
        _ = A.valuation x := mul_one _
        _ ≤ A.valuation (y j) := hxy j
  -- Hence the sum has the valuation of that term, contradicting that the sum vanishes.
  have hzero := Valuation.map_sum_eq_of_lt A.valuation hjs hkey
  rw [hsumF, map_zero] at hzero
  have hqj0 : aeval x (q j) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvj
    exact zero_ne_one hvj
  exact mul_ne_zero hqj0 (hy0 j) ((Valuation.zero_iff _).1 hzero.symm)

/-! ### Discreteness -/

/-- The chain bound of Stichtenoth's Lemma 1.1.7, in the form used twice below: an algebraic
function field admits no infinite sequence of nonunits of a valuation subring whose valuations
increase strictly and stay at or above the valuation of a fixed nonzero element. -/
private theorem not_exists_seq_valuation_strictMono (hF : IsFunctionField k F)
    (hk : ∀ c : k, algebraMap k F c ∈ A) {x : F} (hx0 : x ≠ 0)
    {y : ℕ → F} (hy : ∀ n, A.valuation (y n) < 1)
    (hstep : ∀ n, A.valuation (y n) < A.valuation (y (n + 1)))
    (hxy : A.valuation x ≤ A.valuation (y 0)) : False := by
  have hx : A.valuation x < 1 := hxy.trans_lt (hy 0)
  have hmono : StrictMono fun n : ℕ ↦ A.valuation (y n) := strictMono_nat_of_lt_succ hstep
  have : A.valuation.IsTrivialOn k :=
    .of_le_one _ fun c ↦ (A.valuation_le_one_iff _).2 (hk c)
  have : FiniteDimensional k⟮x⟯ F :=
    hF.finiteDimensional_adjoin (Valuation.transcendental_of_ne_one k x hx0 hx.ne)
  have hli : LinearIndependent k⟮x⟯ fun i : Fin (Module.finrank k⟮x⟯ F + 1) ↦ y i :=
    linearIndependent_of_strictMono_valuation hk hx0 hx (fun i ↦ hy i)
      (fun _ _ hij ↦ hmono hij) fun i ↦ hxy.trans (hmono.monotone (Nat.zero_le _))
  simpa using hli.fintype_card_le_finrank

/-- **Stichtenoth, Theorem 1.1.6**, key step: the valuations of the nonzero nonunits of a proper
valuation subring of an algebraic function field attain a maximum. In additive notation, the
orders of the nonunits attain a minimum, at a prime element. -/
private theorem exists_max_valuation_lt_one (hF : IsFunctionField k F)
    (hk : ∀ c : k, algebraMap k F c ∈ A) (hA : A ≠ ⊤) :
    ∃ t : F, t ≠ 0 ∧ A.valuation t < 1 ∧
      ∀ z : F, z ≠ 0 → A.valuation z < 1 → A.valuation z ≤ A.valuation t := by
  -- A proper valuation subring has a nonzero nonunit to start from.
  obtain ⟨u, hu⟩ : ∃ u : F, u ∉ A := by
    by_contra hcon
    exact hA (ValuationSubring.ext A ⊤ fun z ↦ ⟨fun _ ↦ trivial, fun _ ↦ not_not.1 (hcon ⟨z, ·⟩)⟩)
  have hu0 : u ≠ 0 := fun h ↦ hu (h ▸ A.zero_mem)
  have hui0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hui : A.valuation u⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hu0))]
    exact lt_of_not_ge fun h ↦ hu ((A.valuation_le_one_iff u).1 h)
  by_contra hcon
  push Not at hcon
  -- Otherwise the valuations of the nonunits climb forever, contradicting the chain bound.
  let g : {z : F // z ≠ 0 ∧ A.valuation z < 1} → {z : F // z ≠ 0 ∧ A.valuation z < 1} :=
    fun t ↦ ⟨(hcon t.1 t.2.1 t.2.2).choose, (hcon t.1 t.2.1 t.2.2).choose_spec.1,
      (hcon t.1 t.2.1 t.2.2).choose_spec.2.1⟩
  have hg : ∀ t, A.valuation t.1 < A.valuation (g t).1 :=
    fun t ↦ (hcon t.1 t.2.1 t.2.2).choose_spec.2.2
  refine not_exists_seq_valuation_strictMono hF hk hui0
    (y := fun n ↦ (g^[n] ⟨u⁻¹, hui0, hui⟩).1) (fun n ↦ (g^[n] _).2.2)
    (fun n ↦ ?_) le_rfl
  rw [Function.iterate_succ_apply']
  exact hg _

/-- **Stichtenoth, Theorem 1.1.6.** A proper valuation subring of an algebraic function field that
contains the constants is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_isFunctionField (hF : IsFunctionField k F)
    (hk : ∀ c : k, algebraMap k F c ∈ A) (hA : A ≠ ⊤) : IsDiscreteValuationRing A := by
  obtain ⟨t, ht0, ht1, htmax⟩ := exists_max_valuation_lt_one hF hk hA
  have htA : t ∈ A := (A.valuation_le_one_iff t).1 ht1.le
  have htpos : 0 < A.valuation t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0)
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨t, htA⟩, ⟨fun hu ↦ ht1.ne ((A.valuation_eq_one_iff _).1 hu), fun a b hab ↦ ?_⟩, ?_⟩
  · -- Irreducibility: a factor of smaller valuation than `t` is impossible.
    have hcoe : t = (a : F) * (b : F) := congrArg Subtype.val hab
    have ha0 : (a : F) ≠ 0 := fun h ↦ ht0 (by rw [hcoe, h, zero_mul])
    rcases eq_or_lt_of_le ((A.valuation_le_one_iff (a : F)).2 a.2) with hva | hva
    · exact Or.inl ((A.valuation_eq_one_iff a).2 hva)
    refine Or.inr ((A.valuation_eq_one_iff b).2 (le_antisymm ((A.valuation_le_one_iff _).2 b.2)
      (not_lt.1 fun hlt ↦ absurd (htmax _ ha0 hva) (not_le.2 ?_))))
    calc A.valuation t = A.valuation (a : F) * A.valuation (b : F) := by rw [hcoe, map_mul]
      _ < A.valuation (a : F) * 1 :=
          mul_lt_mul_of_pos_left hlt (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))
      _ = A.valuation (a : F) := mul_one _
  · -- Factorisation: dividing by `t` repeatedly must eventually reach a unit.
    intro z hz
    have hz0 : (z : F) ≠ 0 := fun h ↦ hz (Subtype.ext h)
    have hval : ∀ n : ℕ, A.valuation ((z : F) / t ^ n) =
        A.valuation (z : F) / A.valuation t ^ n := fun n ↦ by
      rw [map_div₀, Valuation.map_pow]
    have hne : ∀ n : ℕ, (z : F) / t ^ n ≠ 0 := fun n ↦ div_ne_zero hz0 (pow_ne_zero n ht0)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, A.valuation ((z : F) / t ^ N) = 1 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ n : ℕ, A.valuation ((z : F) / t ^ n) < 1 := by
        intro n
        induction n with
        | zero =>
          refine lt_of_le_of_ne ?_ (hcon 0)
          rw [pow_zero, div_one]
          exact (A.valuation_le_one_iff _).2 z.2
        | succ n ih =>
          refine lt_of_le_of_ne ?_ (hcon (n + 1))
          rw [hval, pow_succ, ← div_div, ← hval, div_le_one₀ htpos]
          exact htmax _ (hne n) ih
      refine not_exists_seq_valuation_strictMono hF hk hz0
        (y := fun n ↦ (z : F) / t ^ n) hall (fun n ↦ ?_) (by simp)
      rw [hval, hval]
      exact (div_lt_div_iff_of_pos_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz0))
        (pow_pos htpos _) (pow_pos htpos _)).2
        (pow_lt_pow_right_of_lt_one₀ htpos ht1 n.lt_succ_self)
    have hwA : (z : F) / t ^ N ∈ A := (A.valuation_le_one_iff _).1 hN.le
    have hw : IsUnit (⟨(z : F) / t ^ N, hwA⟩ : A) := (A.valuation_eq_one_iff _).2 hN
    refine ⟨N, hw.unit, Subtype.ext ?_⟩
    rw [IsUnit.unit_spec]
    push_cast
    field_simp

/-! ### The place of a valuation subring -/

namespace Place

/-- The valuation subring of the adic valuation of the maximal ideal of a discrete valuation
subring `A` of `F` is `A` itself. This is Mathlib's
`IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`, read through the fact that the
structure map of a valuation subring is the inclusion. -/
theorem valuationSubring_valuation_maximalIdeal (A : ValuationSubring F)
    [IsDiscreteValuationRing A] :
    ((IsDiscreteValuationRing.maximalIdeal A).valuation F).valuationSubring = A := by
  refine ValuationSubring.toSubring_injective ?_
  rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := A) (K := F)]
  ext z
  simp [Subring.mem_map, ValuationSubring.algebraMap_apply]

/-- **Stichtenoth, Theorem 1.1.13.** The place of `F / k` attached to a proper valuation subring
of `F` containing the constants: its valuation is the adic valuation of the maximal ideal of the
subring, which is a discrete valuation ring by
`TauCeti.isDiscreteValuationRing_of_isFunctionField`. -/
def ofValuationSubring (hF : IsFunctionField k F) (hk : ∀ c : k, algebraMap k F c ∈ A)
    (hA : A ≠ ⊤) : Place k F :=
  haveI := isDiscreteValuationRing_of_isFunctionField hF hk hA
  { valuation := (IsDiscreteValuationRing.maximalIdeal A).valuation F
    valuation_surjective := IsDedekindDomain.HeightOneSpectrum.valuation_surjective F _
    isTrivialOn := by
      have hmem : ∀ z : F,
          (IsDiscreteValuationRing.maximalIdeal A).valuation F z ≤ 1 ↔ z ∈ A := fun z ↦ by
        rw [← Valuation.mem_valuationSubring_iff, valuationSubring_valuation_maximalIdeal A]
      exact ⟨fun c hc ↦ by
        have hprod : (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c) *
            (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c⁻¹) = 1 := by
          rw [← map_mul, ← map_mul]
          simp [hc]
        refine le_antisymm ((hmem _).2 (hk c)) (not_lt.1 fun hlt ↦ hprod.not_lt ?_)
        calc (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c) *
              (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c⁻¹)
            ≤ (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c) * 1 := by
              gcongr
              exact (hmem _).2 (hk c⁻¹)
          _ = (IsDiscreteValuationRing.maximalIdeal A).valuation F (algebraMap k F c) := mul_one _
          _ < 1 := hlt⟩ }

/-- The valuation of `TauCeti.Place.ofValuationSubring` is the adic valuation of the maximal
ideal of the subring. -/
theorem valuation_ofValuationSubring (hF : IsFunctionField k F)
    (hk : ∀ c : k, algebraMap k F c ∈ A) (hA : A ≠ ⊤) :
    (ofValuationSubring hF hk hA).valuation =
      let _ := isDiscreteValuationRing_of_isFunctionField hF hk hA
      (IsDiscreteValuationRing.maximalIdeal A).valuation F := by
  let _ := isDiscreteValuationRing_of_isFunctionField hF hk hA
  -- Tactic `rfl`, not the term: the body of `ofValuationSubring` is not `@[expose]`d, so the
  -- projection is only reducible here, inside the module that defines it.
  rfl

/-- The valuation ring of `TauCeti.Place.ofValuationSubring` is the subring one started from. -/
@[simp]
theorem integers_ofValuationSubring (hF : IsFunctionField k F)
    (hk : ∀ c : k, algebraMap k F c ∈ A) (hA : A ≠ ⊤) :
    (ofValuationSubring hF hk hA).integers = A := by
  have := isDiscreteValuationRing_of_isFunctionField hF hk hA
  refine ValuationSubring.ext _ _ fun z ↦ ?_
  rw [mem_integers_iff, valuation_ofValuationSubring, ← Valuation.mem_valuationSubring_iff,
    valuationSubring_valuation_maximalIdeal A]

/-- **Stichtenoth, Theorem 1.1.13.** A proper valuation subring of an algebraic function field
containing the constants is the valuation ring of exactly one place. -/
theorem existsUnique_integers_eq (hF : IsFunctionField k F) (hk : ∀ c : k, algebraMap k F c ∈ A)
    (hA : A ≠ ⊤) : ∃! P : Place k F, P.integers = A :=
  ⟨ofValuationSubring hF hk hA, integers_ofValuationSubring hF hk hA, fun _ h ↦
    integers_injective (h.trans (integers_ofValuationSubring hF hk hA).symm)⟩

end Place

end TauCeti
