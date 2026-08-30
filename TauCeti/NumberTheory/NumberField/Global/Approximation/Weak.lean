/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.Valuation.Approximation

/-!
# Weak approximation at finite and infinite places

This file proves Artin--Whaples weak approximation for a number field in a finite product that
contains both nonarchimedean and archimedean completions.  The finite factors are Mathlib's
`HeightOneSpectrum.adicCompletion`, and the infinite factors are
`NumberField.InfinitePlace.Completion`.

The proof first applies Mathlib's weak approximation theorem for inequivalent real absolute
values to the disjoint union of the chosen places.  At a finite place, the normalized discrete
valuation is viewed as a real absolute value through `Valuation.toRealAbsoluteValue`.  Distinct
finite places are inequivalent, distinct infinite places are inequivalent, and a finite place is
inequivalent to an infinite one because every algebraic integer has finite absolute value at most
one whereas every infinite place sends `2` to `2`.

The resulting approximation inside the number field is then promoted to the actual completions.
Density of the field in each individual completion supplies nearby field-valued targets, and a
second simultaneous approximation remains inside the prescribed product neighbourhood.

## Main result

* `GlobalNumberFields.weakApproximation_denseRange`: the diagonal image of a number field is dense
  in every finite product of finite and infinite completions.

## References

The weak approximation theorem is due to E. Artin and G. Whaples, *Axiomatic characterization of
fields by the product formula for valuations*, Bull. Amer. Math. Soc. **51** (1945).  The mixed
number-field formulation also appears in J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number
Theory*, Chapter II.
-/

public section

open Filter IsDedekindDomain NumberField NumberField.InfinitePlace Set Topology
open scoped NNReal Topology WithZero

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private abbrev FinitePlace (K : Type*) [Field K]
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))) :=
  {v : HeightOneSpectrum (RingOfIntegers K) // v ∈ S}

private noncomputable def mixedAbsoluteValue
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)} :
    FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → AbsoluteValue K ℝ
  | .inl v => (v.1.valuation K).toRealAbsoluteValue
  | .inr w => w.1.1

private theorem mixedAbsoluteValue_isNontrivial
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (v : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf}) :
    (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) v).IsNontrivial := by
  cases v with
  | inl v =>
      exact (Valuation.toRealAbsoluteValue_isNontrivial_iff (v.1.valuation K)).mpr inferInstance
  | inr w =>
      exact w.1.isNontrivial

private theorem finite_mixedAbsoluteValue_not_isEquiv_infinite
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (v : FinitePlace K Sₑ) (w : {w : InfinitePlace K // w ∈ Sinf}) :
    ¬(mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)).IsEquiv
      (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w)) := by
  intro h
  have hfinite : mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) (2 : K) ≤
      mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) 1 := by
    rw [mixedAbsoluteValue, Valuation.toRealAbsoluteValue_le_iff, map_one,
      ← map_ofNat (algebraMap (RingOfIntegers K) K) 2]
    exact v.1.valuation_le_one (K := K) 2
  have hinfinite : ¬mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w) (2 : K) ≤
      mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inr w) 1 := by
    have hw : (1 : ℝ) < w.1.1 (2 : K) := by
      rw [← InfinitePlace.coe_apply, ← Nat.cast_ofNat (R := K) (n := 2),
        InfinitePlace.map_natCast]
      norm_num
    simpa only [mixedAbsoluteValue, map_one, not_le] using hw
  exact hinfinite ((h (2 : K) 1).mp hfinite)

private theorem mixedAbsoluteValue_pairwise_not_isEquiv
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)} :
    Pairwise fun v w : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} =>
      ¬(mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) v).IsEquiv
        (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) w) := by
  intro v w hvw
  cases v with
  | inl v =>
      cases w with
      | inl w =>
          intro h
          apply hvw
          apply congrArg Sum.inl
          apply Subtype.ext
          exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
            ((Valuation.toRealAbsoluteValue_isEquiv_iff _ _).mp h)
      | inr w =>
          exact finite_mixedAbsoluteValue_not_isEquiv_infinite v w
  | inr v =>
      cases w with
      | inl w =>
          exact fun h => finite_mixedAbsoluteValue_not_isEquiv_infinite w v h.symm
      | inr w =>
          intro h
          apply hvw
          apply congrArg Sum.inr
          apply Subtype.ext
          exact (InfinitePlace.eq_iff_isEquiv (K := K)).mpr h

private theorem exists_mixed_approximation
    {Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))} {Sinf : Finset (InfinitePlace K)}
    (aₑ : FinitePlace K Sₑ → K) (ainf : {w : InfinitePlace K // w ∈ Sinf} → K)
    (εₑ : FinitePlace K Sₑ → ℤᵐ⁰) (hεₑ : ∀ v, εₑ v ≠ 0)
    (einf : {w : InfinitePlace K // w ∈ Sinf} → ℝ) (heinf : ∀ w, 0 < einf w) :
    ∃ x : K, (∀ v, v.1.valuation K (x - aₑ v) < εₑ v) ∧
      ∀ w, w.1 (x - ainf w) < einf w := by
  classical
  choose p hp using fun (v : FinitePlace K Sₑ) => v.1.valuation_surjective K (εₑ v)
  let a : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → K
    | .inl v => aₑ v
    | .inr w => ainf w
  let ρ : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} → ℝ
    | .inl v => mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v) (p v)
    | .inr w => einf w
  have hρ : ∀ i, 0 < ρ i := by
    rintro (v | w)
    · exact (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)).pos_iff.mpr
        ((v.1.valuation K).ne_zero_iff.mp (hp v ▸ hεₑ v))
    · exact heinf w
  cases @isEmpty_or_nonempty (FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf}) with
  | inl h =>
      refine ⟨0,
        fun v => (h.false (Sum.inl (β := {w : InfinitePlace K // w ∈ Sinf}) v)).elim,
        fun w => (h.false (Sum.inr (α := FinitePlace K Sₑ) w)).elim⟩
  | inr h =>
      let _ := Fintype.ofFinite (FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf})
      let r := Finset.univ.inf' Finset.univ_nonempty ρ
      have hr : 0 < r := (Finset.lt_inf'_iff _).mpr fun i _ => hρ i
      obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi
          (v := fun i : FinitePlace K Sₑ ⊕ {w : InfinitePlace K // w ∈ Sinf} =>
            mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) i)
          (fun i => mixedAbsoluteValue_isNontrivial i)
          mixedAbsoluteValue_pairwise_not_isEquiv).exists_dist_lt
        (fun i => WithAbs.toAbs
          (mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) i) (a i)) (ε := r) hr
      refine ⟨x, fun v => ?_, fun w => ?_⟩
      · have hv := (dist_pi_lt_iff hr).mp hx (Sum.inl v)
        rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hv
        simp only [a] at hv
        have hvρ : mixedAbsoluteValue (Sₑ := Sₑ) (Sinf := Sinf) (Sum.inl v)
            (x - aₑ v) < ρ (Sum.inl v) :=
          hv.trans_le (Finset.inf'_le ρ (Finset.mem_univ (Sum.inl v)))
        simp only [ρ] at hvρ
        rw [← hp v]
        exact lt_of_not_ge fun h => not_le.mpr hvρ
          ((Valuation.toRealAbsoluteValue_le_iff _).mpr h)
      · have hw := (dist_pi_lt_iff hr).mp hx (Sum.inr w)
        rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hw
        simp only [a, mixedAbsoluteValue] at hw
        exact hw.trans_le (Finset.inf'_le ρ (Finset.mem_univ (Sum.inr w)))

/-- **Artin--Whaples weak approximation at mixed places.** For finite sets `Sₑ` of finite
places and `Sinf` of infinite places, the diagonal image of a number field `K` is dense in the
product of the corresponding finite and infinite completions.

The finite factors are Mathlib's normalized adic completions and the infinite factors are its
completions of `K` at `InfinitePlace K`; in particular, this is not merely approximation inside
copies of `K` equipped with the place topologies. -/
theorem weakApproximation_denseRange
    (Sₑ : Finset (HeightOneSpectrum (RingOfIntegers K))) (Sinf : Finset (InfinitePlace K)) :
    DenseRange fun x : K =>
      ((fun v : {v : HeightOneSpectrum (RingOfIntegers K) // v ∈ Sₑ} =>
          algebraMap K (v.1.adicCompletion K) x),
        fun w : {w : InfinitePlace K // w ∈ Sinf} => algebraMap K w.1.Completion x) := by
  classical
  rw [DenseRange, dense_iff_inter_open]
  intro U hU ⟨y, hyU⟩
  obtain ⟨Uₑ, Uinf, hUₑ, hyₑ, hUinf, hyinf, hprod⟩ :=
    mem_nhds_prod_iff'.mp (hU.mem_nhds hyU)
  obtain ⟨Vₑ, hVₑ, hVₑU⟩ := (isOpen_pi_iff'.mp hUₑ) y.1 hyₑ
  obtain ⟨Vinf, hVinf, hVinfU⟩ := (isOpen_pi_iff'.mp hUinf) y.2 hyinf
  choose aₑ haₑ using fun (v : FinitePlace K Sₑ) =>
    (v.1.denseRange_algebraMap K).exists_mem_open (hVₑ v).1 ⟨y.1 v, (hVₑ v).2⟩
  have hdenseinf (w : {w : InfinitePlace K // w ∈ Sinf}) :
      DenseRange (fun x : K => algebraMap K w.1.Completion x) := by
    -- Expose the two coercions used to construct the algebra map so `DenseRange.comp` applies.
    change DenseRange
      (((↑) : WithAbs w.1.1 → w.1.Completion) ∘ (WithAbs.equiv w.1.1).symm)
    exact (InfinitePlace.Completion.denseRange_coe (v := w.1)).comp
      (WithAbs.equiv w.1.1).symm.surjective.denseRange
      (InfinitePlace.Completion.continuous_coe (v := w.1))
  choose ainf hainf using fun (w : {w : InfinitePlace K // w ∈ Sinf}) =>
    (hdenseinf w).exists_mem_open (hVinf w).1 ⟨y.2 w, (hVinf w).2⟩
  choose γ hγ using fun (v : FinitePlace K Sₑ) =>
    Valued.mem_nhds.mp ((hVₑ v).1.mem_nhds (haₑ v))
  choose einf heinf hballinf using fun (w : {w : InfinitePlace K // w ∈ Sinf}) =>
    Metric.mem_nhds_iff.mp ((hVinf w).1.mem_nhds (hainf w))
  -- Convert the value-group radii supplied by the valued topology back to `ℤᵐ⁰` radii.
  let εₑ : FinitePlace K Sₑ → ℤᵐ⁰ := fun v =>
    MonoidWithZeroHom.ValueGroup₀.embedding (γ v : MonoidWithZeroHom.ValueGroup₀
      (.ofClass (Valued.v : Valuation (v.1.adicCompletion K) ℤᵐ⁰)))
  have hεₑ : ∀ v, εₑ v ≠ 0 := fun v => by
    intro h
    apply Units.ne_zero (γ v)
    apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
    -- Unfold only the chosen radius; the value-group embedding itself remains abstract.
    change MonoidWithZeroHom.ValueGroup₀.embedding
      (γ v : MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation (v.1.adicCompletion K) ℤᵐ⁰))) = 0 at h
    rw [map_zero]
    exact h
  obtain ⟨x, hxₑ, hxinf⟩ := exists_mixed_approximation aₑ ainf εₑ hεₑ einf heinf
  refine ⟨_, ?_, ⟨x, rfl⟩⟩
  apply hprod
  constructor
  · apply hVₑU
    intro v _
    apply hγ v
    -- `Valued.mem_nhds` presents the ball using `restrict`; expose that exact predicate.
    change Valued.v.restrict
      (algebraMap K (v.1.adicCompletion K) x -
        algebraMap K (v.1.adicCompletion K) (aₑ v)) < γ v
    rw [Valuation.restrict_lt_iff_lt_embedding]
    rw [← map_sub]
    -- The completion algebra map is the canonical coercion on field elements.
    change Valued.v ((x - aₑ v : K) : v.1.adicCompletion K) < εₑ v
    rw [v.1.valuedAdicCompletion_eq_valuation']
    exact hxₑ v
  · apply hVinfU
    intro w _
    apply hballinf w
    -- `Metric.mem_nhds_iff` presents the chosen neighbourhood as this open ball.
    change dist (algebraMap K w.1.Completion x)
      (algebraMap K w.1.Completion (ainf w)) < einf w
    rw [dist_eq_norm, ← map_sub, InfinitePlace.Completion.algebraMap_apply,
      ← (WithAbs.equiv w.1.1).apply_symm_apply (x - ainf w),
      InfinitePlace.Completion.norm_coe]
    exact hxinf w

end TauCeti.GlobalNumberFields
