/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.BlockTransport
public import TauCeti.Probability.DeFinetti.ViaKoopman.InvariantConditionalLaw
public import Mathlib.Dynamics.BirkhoffSum.Average
public import TauCeti.Probability.Ergodic.CondExpProjection
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Displacing the last coordinate of a block

The step that decouples one factor from a block, over an invariant event.

Appending the coordinate `r + m` to the prefix `0, 1, …, r - 1` gives a strictly increasing
selection for *every* `m`, so the block transport makes the set-integral of the resulting product
independent of `m`. Averaging over `m < n` therefore leaves the left-hand side unchanged while
turning the right-hand side into a Birkhoff average of `𝟙_B ∘ (· r)` under the shift — which is
where the mean ergodic theorem enters.

## Source

The Koopman route to de Finetti follows Kallenberg's first proof (see References). No material is
adapted from `cameronfreer/exchangeability`: that development carries its own `ViaKoopman` subtree
covering this argument, but the lemmas here are assembled from Tau Ceti's own pieces — the
invariant block transport of `PathSpace/Invariant/BlockTransport.lean`, the `L¹` mean ergodic
bridge of `Ergodic/CondExpProjection.lean`, and the invariant conditional law of
`ViaKoopman/InvariantConditionalLaw.lean`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  Theorem 1.1.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 5** (Koopman operators and
  invariant σ-algebras), whose milestone is `deFinetti_viaKoopman`.

## Main results

* `ContractableLaw.condExp_indicator_coord_ae_eq_invariantConditionalProbabilityMeasure` — the
  invariant conditional law computes the conditional expectation of *every* coordinate indicator,
  not just the first;
* `ContractableLaw.setIntegral_weight_mul_prefix_mul_indicator_eq_condExp` — over an invariant
  event, the weighted integral of `𝟙_B` at coordinate `r` equals the weighted integral of its
  conditional expectation given the shift-invariant σ-algebra. This form needs no standard-Borel
  hypothesis;
* `setIntegral_weight_mul_prefix_mul_indicator_eq_invariantConditionalProbabilityMeasure` (same
  namespace) — and, where the witness exists, that limit is the invariant conditional law `ν(B)`.

The transport and averaging stages behind these — the displacement identity, its Birkhoff-average
form, the coordinate/Birkhoff bridge and the `L¹` convergence — are private: they are steps of this
file's argument, not API.

The weighted transport and decoupling statements carry an invariants-measurable weight `w`. The
weight is what makes the chain usable in an induction across a block: the factors already peeled
off accumulate as exactly such a weight, which an unweighted form cannot express.

The limit passage itself is one private estimate,
`tendsto_setIntegral_mul_of_tendsto_integral_abs`: `L¹` convergence plus `|p| ≤ 1` gives
convergence of the weighted set-integrals. Keeping it separate localises the integrability
obligations instead of rediscovering them inside the Koopman calculation.

The `condExp` form is the one an induction consumes, because `stronglyMeasurable_condExp` makes it
*strictly* measurable for the invariants σ-algebra, which is what the weight hypothesis demands;
the `ν` form is only an a.e. identity and cannot serve as a weight. Conversion happens once, at the
end.

The weighted transport and decoupling statements carry an invariants-measurable weight `w`; the
preliminary and analytic lemmas do not. The weight is what makes the chain usable in an induction
across a block: the factors already peeled off accumulate as exactly such a weight, which an
unweighted form cannot express.

This is the engine of the Koopman factorization: the `m`-independence is what allows the average
over `m` to be inserted for free, and that average is what the ergodic theorem consumes.

The induction on `r` that iterates this decoupling across a whole block, and the `ℝ≥0∞` ending it
feeds, are not here yet.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **Appending a later coordinate to the prefix is strictly increasing.** The prefix occupies
`0, 1, …, r - 1` and the appended coordinate is `r + m`, so the selection is strictly increasing
whatever the displacement `m`. -/
private theorem snoc_prefix_strictMono (r m : ℕ) :
    StrictMono (Fin.snoc (fun i : Fin r => (i : ℕ)) (r + m) : Fin (r + 1) → ℕ) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  rw [Fin.snoc_castSucc]
  rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨j, hj⟩ | hj
  · rw [hj, Fin.snoc_castSucc]
    have : (i : ℕ) < (j : ℕ) := by
      have := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    exact_mod_cast this
  · rw [hj, Fin.snoc_last]
    exact lt_of_lt_of_le i.isLt (Nat.le_add_right r m)

omit [MeasurableSpace α] in
/-- **The displaced coordinates are a Birkhoff average.** Reading coordinate `r` along the shift
orbit gives exactly the displaced coordinates `r, r + 1, …`, so the average over displacements is
`birkhoffAverage` of the single observable `𝟙_B ∘ (· r)`.

This is where the two halves of the argument meet: the left side is what the invariant transport
controls (each term has the same integral over an invariant event), and the right side is what the
mean ergodic theorem converges. -/
private theorem birkhoffAverage_shift_coord_eq {B : Set α} (r n : ℕ) (x : ℕ → α) :
    birkhoffAverage ℝ (shift α) (fun y : ℕ → α => (B.indicator (fun _ => (1 : ℝ)) (y r))) n x
      = (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, B.indicator (fun _ => (1 : ℝ)) (x (r + m)) := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [shift_iterate_apply]


/-- **The Birkhoff averages of a coordinate indicator converge in `L¹`.** The mean ergodic bridge,
applied to the indicator of `B` at coordinate `r`: the limit is the conditional expectation of that
same indicator given the shift-invariant σ-algebra. -/
private theorem tendsto_integral_abs_birkhoffAverage_indicator_coord
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hmp : MeasurePreserving (shift α) ρ ρ)
    {B : Set α} (hB : MeasurableSet B) (r : ℕ) :
    Filter.Tendsto (fun n => ∫ x,
        |birkhoffAverage ℝ (shift α) (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r)) n x
          - ρ[fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r) |
              MeasurableSpace.invariants (shift α)] x| ∂ρ)
      Filter.atTop (nhds 0) := by
  have hmeas : Measurable fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r) :=
    (measurable_const.indicator hB).comp (measurable_pi_apply r)
  have hbdd : ∀ y : ℕ → α, ‖B.indicator (fun _ => (1 : ℝ)) (y r)‖ ≤ 1 := by
    intro y
    have h0 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) (y r) :=
      Set.indicator_apply_nonneg fun _ => zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  exact tendsto_integral_abs_birkhoffAverage_sub_condExp (shift α) hmp
    (MemLp.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbdd))

namespace ContractableLaw

/-- **The invariant conditional law computes every coordinate, not just the first.** Combining the
witness's characteristic property at coordinate `0` with the transport fact that all coordinates
agree over invariant events. This is what lets the Birkhoff limit at coordinate `r` be named as the
witness. -/
theorem condExp_indicator_coord_ae_eq_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α] {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ContractableLaw ρ) {B : Set α} (hB : MeasurableSet B) (r : ℕ) :
    ρ[fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r) |
        MeasurableSpace.invariants (shift α)]
      =ᵐ[ρ] fun x => ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real B := by
  classical
  have hle : MeasurableSpace.invariants (shift α) ≤ (inferInstance : MeasurableSpace (ℕ → α)) :=
    MeasurableSpace.invariants_le _
  have hmeas : ∀ s : ℕ, Measurable fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y s) :=
    fun s => (measurable_const.indicator hB).comp (measurable_pi_apply s)
  have hint : ∀ s : ℕ, Integrable (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y s)) ρ := by
    intro s
    refine ⟨(hmeas s).aestronglyMeasurable, .of_bounded (C := 1) (Filter.Eventually.of_forall ?_)⟩
    intro y
    have h0 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) (y s) :=
      Set.indicator_apply_nonneg fun _ => zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  -- The witness is the conditional expectation at coordinate `0`.
  have hwit := invariantConditionalProbabilityMeasure_ae_eq_condExp (ρ := ρ) hB
  refine Filter.EventuallyEq.symm (ae_eq_condExp_of_forall_setIntegral_eq hle (hint r)
    (fun s _ _ => (integrable_condExp.congr hwit.symm).integrableOn) (fun s hs _ => ?_) ?_)
  · -- Test against an invariant event: coordinate `r` agrees with coordinate `0`.
    have h0 : ∫ x in s, ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real B ∂ρ
        = ∫ x in s, B.indicator (fun _ => (1 : ℝ)) (x 0) ∂ρ := by
      have hint0 : Integrable ((B.indicator fun _ => (1 : ℝ)) ∘ fun x : ℕ → α => x 0) ρ := hint 0
      simpa only [Function.comp_apply] using
        (setIntegral_congr_ae (hle _ hs) (hwit.mono fun x hx _ => hx)).trans
          (setIntegral_condExp hle hint0 hs)
    rw [h0]
    exact (hρ.setIntegral_comp_coord_eq_comp_zero_of_measurableSet_invariants r hs
      (measurable_const.indicator hB)).symm
  · exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hwit.symm

/-- **The displaced weighted integral does not depend on the displacement.** Appending `r + m` to
the prefix is strictly increasing for every `m`, so the weighted block transport carries each
displaced integral onto the same prefix integral.

The invariant weight `w` is what makes this usable in an induction: the factors already peeled off
a block accumulate as exactly such a weight. -/
private theorem setIntegral_weight_mul_prefix_mul_indicator_displaced_eq
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {r : ℕ}
    {w : (ℕ → α) → ℝ} (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    {g : (Fin r → α) → ℝ} (hg : Measurable g) {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) (m : ℕ) :
    ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + m))) ∂ρ
      = ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ := by
  classical
  -- The combined observable on a block of length `r + 1`.
  set G : (Fin (r + 1) → α) → ℝ := fun y =>
    g (fun j : Fin r => y j.castSucc) * B.indicator (fun _ => (1 : ℝ)) (y (Fin.last r)) with hG
  have hG_meas : Measurable G := by
    refine Measurable.mul ?_ ?_
    · exact hg.comp (measurable_pi_lambda _ fun j => measurable_pi_apply j.castSucc)
    · exact (measurable_const.indicator hB).comp (measurable_pi_apply (Fin.last r))
  -- Reading the combined observable along the displaced selection is the integrand.
  have hcomp : ∀ (d : ℕ) (x : ℕ → α),
      G (fun i : Fin (r + 1) =>
          x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + d) : Fin (r + 1) → ℕ) i))
        = g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + d)) := by
    intro d x
    have hpp : (fun j : Fin r => x (j : ℕ)) = prefixProj α r x :=
      (funext fun i => prefixProj_apply r x i).symm
    simp only [hG, Fin.snoc_castSucc, Fin.snoc_last, hpp]
  -- Every displacement transports onto the prefix, weight and all.
  have key : ∀ d : ℕ,
      ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + d))) ∂ρ
        = ∫ x in A, w x * G (prefixProj α (r + 1) x) ∂ρ := by
    intro d
    calc ∫ x in A, w x * (g (prefixProj α r x)
            * B.indicator (fun _ => (1 : ℝ)) (x (r + d))) ∂ρ
        = ∫ x in A, w x * G (fun i : Fin (r + 1) =>
            x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + d) : Fin (r + 1) → ℕ) i)) ∂ρ :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hcomp])
      _ = ∫ x in A, w x * G (prefixProj α (r + 1) x) ∂ρ :=
          hρ.setIntegral_mul_block_eq_prefixProj_of_strictMono_of_measurable_invariants
            (snoc_prefix_strictMono r d) hA hw hG_meas
  rw [key m, ← key 0, Nat.add_zero]

/-- **The weighted integral equals its own Birkhoff average.** Because the displaced integrals all
agree, averaging over `m < n` changes nothing on the left while turning the integrand on the right
into a Birkhoff average — for every `n ≠ 0`.

This is the step that hands the argument to the mean ergodic theorem. -/
private theorem setIntegral_weight_mul_prefix_mul_indicator_eq_birkhoffAverage
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ) {r : ℕ}
    {w : (ℕ → α) → ℝ} (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    (hw_bdd : ∀ᵐ x ∂ρ, |w x| ≤ 1)
    {g : (Fin r → α) → ℝ} (hg : Measurable g) (hg_bdd : ∀ y, |g y| ≤ 1)
    {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ
      = ∫ x in A, w x * (g (prefixProj α r x)
          * birkhoffAverage ℝ (shift α)
              (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r)) n x) ∂ρ := by
  classical
  have hw' : Measurable w := hw.mono (MeasurableSpace.invariants_le _) le_rfl
  have hgm : Measurable fun x : ℕ → α => g (prefixProj α r x) := hg.comp (measurable_prefixProj r)
  have hbd : ∀ d : ℕ, ∀ᵐ x ∂ρ.restrict A,
      ‖w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + d)))‖ ≤ 1 := by
    intro d
    filter_upwards [ae_restrict_of_ae hw_bdd] with x hwx
    have h0 : (0 : ℝ) ≤ B.indicator (fun _ => (1 : ℝ)) (x (r + d)) :=
      Set.indicator_apply_nonneg fun _ => zero_le_one
    have h1 : B.indicator (fun _ => (1 : ℝ)) (x (r + d)) ≤ 1 :=
      Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0]
    have hinner : |g (prefixProj α r x)| * B.indicator (fun _ => (1 : ℝ)) (x (r + d)) ≤ 1 :=
      (mul_le_mul (hg_bdd _) h1 h0 zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul hwx hinner (by positivity) zero_le_one).trans_eq (one_mul 1)
  have hterm : ∀ d : ℕ, Integrable
      (fun x : ℕ → α => w x * (g (prefixProj α r x)
        * B.indicator (fun _ => (1 : ℝ)) (x (r + d)))) (ρ.restrict A) := by
    intro d
    have hm : Measurable fun x : ℕ → α => w x * (g (prefixProj α r x)
        * B.indicator (fun _ => (1 : ℝ)) (x (r + d))) :=
      hw'.mul (hgm.mul ((measurable_const.indicator hB).comp (measurable_pi_apply (r + d))))
    exact ⟨hm.aestronglyMeasurable, .of_bounded (C := 1) (hbd d)⟩
  have hrhs : ∫ x in A, w x * (g (prefixProj α r x)
      * birkhoffAverage ℝ (shift α)
          (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r)) n x) ∂ρ
      = (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, ∫ x in A, w x * (g (prefixProj α r x)
          * B.indicator (fun _ => (1 : ℝ)) (x (r + m))) ∂ρ := by
    rw [← integral_finsetSum _ fun m _ => hterm m, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [birkhoffAverage_shift_coord_eq, ← Finset.mul_sum]
    ring
  rw [hrhs]
  simp only [hρ.setIntegral_weight_mul_prefix_mul_indicator_displaced_eq hw hg hB hA]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

/-- **Passing a bounded weight through an `L¹` limit.** If `u n → v` in `L¹` and `|p| ≤ 1`, the
weighted set-integrals converge. The whole content is one estimate:

`|∫_A p (u n - v)| ≤ ∫_A |u n - v| ≤ ∫ |u n - v| → 0`.

Isolating it keeps the integrability obligations in one place rather than rediscovering them inside
the Koopman calculation. Private: the Koopman limit passage is the only consumer. -/
private theorem tendsto_setIntegral_mul_of_tendsto_integral_abs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : Set Ω} {p : Ω → ℝ}
    {u : ℕ → Ω → ℝ} {v : Ω → ℝ}
    (hp : AEStronglyMeasurable p μ) (hp_bdd : ∀ᵐ x ∂μ, ‖p x‖ ≤ 1)
    (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ)
    (hconv : Filter.Tendsto (fun n => ∫ x, |u n x - v x| ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in A, p x * u n x ∂μ) Filter.atTop
      (nhds (∫ x in A, p x * v x ∂μ)) := by
  -- Weighting by `p` does not increase the `L¹` distance, since `|p| ≤ 1`.
  have hmono : ∀ n, eLpNorm ((fun x => p x * u n x) - fun x => p x * v x) 1 μ
      ≤ eLpNorm ((u n) - v) 1 μ := by
    intro n
    refine eLpNorm_mono_ae ?_
    filter_upwards [hp_bdd] with x hpx
    simp only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) ((Real.norm_eq_abs _) ▸ hpx)
  have hbase : Filter.Tendsto (fun n => eLpNorm ((u n) - v) 1 μ) Filter.atTop (nhds 0) := by
    refine TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub hu hv ?_
    simpa only [Real.norm_eq_abs] using hconv
  have hL1 : Filter.Tendsto
      (fun n => eLpNorm ((fun x => p x * u n x) - fun x => p x * v x) 1 μ)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
      (fun _ => zero_le) hmono
  exact tendsto_setIntegral_of_L1' _ (hp.mul hv.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun n => (hu n).bdd_mul hp hp_bdd) hL1 A

/-- **The last coordinate decouples into the invariant conditional expectation.** Over an invariant
event, the weighted integral of `𝟙_B` at coordinate `r` equals the weighted integral of its
conditional expectation given the shift-invariant σ-algebra. No standard-Borel hypothesis is
needed, since no witness is named; that is the following theorem.

Where the two halves meet: the averaged sequence is *constant* in `n` by
`ContractableLaw.setIntegral_weight_mul_prefix_mul_indicator_eq_birkhoffAverage`, and the same
sequence converges to the right-hand side by the `L¹` mean ergodic theorem; a sequence has one
limit. -/
theorem setIntegral_weight_mul_prefix_mul_indicator_eq_condExp
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ContractableLaw ρ) {r : ℕ}
    {w : (ℕ → α) → ℝ} (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    (hw_bdd : ∀ᵐ x ∂ρ, |w x| ≤ 1)
    {g : (Fin r → α) → ℝ} (hg : Measurable g) (hg_bdd : ∀ y, |g y| ≤ 1)
    {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ
      = ∫ x in A, w x * (g (prefixProj α r x)
          * ρ[fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r) |
              MeasurableSpace.invariants (shift α)] x) ∂ρ := by
  classical
  have hw' : Measurable w := hw.mono (MeasurableSpace.invariants_le _) le_rfl
  have hgm : Measurable fun x : ℕ → α => g (prefixProj α r x) := hg.comp (measurable_prefixProj r)
  have hind_nonneg : ∀ y : α, 0 ≤ B.indicator (fun _ => (1 : ℝ)) y := fun _ =>
    Set.indicator_apply_nonneg fun _ => zero_le_one
  have hind_le : ∀ y : α, B.indicator (fun _ => (1 : ℝ)) y ≤ 1 := fun _ =>
    Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  set φ : (ℕ → α) → ℝ := fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r) with hφdef
  have hφ_meas : Measurable φ := (measurable_const.indicator hB).comp (measurable_pi_apply r)
  set F : (ℕ → α) → ℝ := ρ[φ | MeasurableSpace.invariants (shift α)] with hFdef
  have havg_meas : ∀ n : ℕ, Measurable (birkhoffAverage ℝ (shift α) φ n) := by
    intro n
    have hsum : Measurable fun x : ℕ → α => ∑ m ∈ Finset.range n, φ ((shift α)^[m] x) :=
      Finset.measurable_sum _ fun m _ => hφ_meas.comp (measurable_shift.iterate m)
    exact hsum.const_smul ((n : ℝ)⁻¹)
  have havg_bdd : ∀ (n : ℕ) (x : ℕ → α), ‖birkhoffAverage ℝ (shift α) φ n x‖ ≤ 1 := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [birkhoffAverage, birkhoffSum]
    · have hs0 : 0 ≤ ∑ m ∈ Finset.range n, φ ((shift α)^[m] x) :=
        Finset.sum_nonneg fun m _ => hind_nonneg _
      have hsn : ∑ m ∈ Finset.range n, φ ((shift α)^[m] x) ≤ (n : ℝ) := by
        calc ∑ m ∈ Finset.range n, φ ((shift α)^[m] x)
            ≤ ∑ _m ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun m _ => hind_le _
          _ = (n : ℝ) := by simp
      rw [birkhoffAverage, birkhoffSum, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      calc (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, φ ((shift α)^[m] x)
          ≤ (n : ℝ)⁻¹ * (n : ℝ) := by gcongr
        _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
  have havg_int : ∀ n : ℕ, Integrable (birkhoffAverage ℝ (shift α) φ n) ρ := fun n =>
    ⟨(havg_meas n).aestronglyMeasurable,
      .of_bounded (C := 1) (Filter.Eventually.of_forall (havg_bdd n))⟩
  have hF_int : Integrable F ρ := integrable_condExp
  set c : ℕ → ℝ := fun n => ∫ x in A, w x * (g (prefixProj α r x)
    * birkhoffAverage ℝ (shift α) φ n x) ∂ρ with hcdef
  have hL : Filter.Tendsto c Filter.atTop
      (nhds (∫ x in A, w x
        * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simp only [hcdef, hφdef]
    exact hρ.setIntegral_weight_mul_prefix_mul_indicator_eq_birkhoffAverage hw hw_bdd hg hg_bdd
      hB hA hn.ne'
  have hR : Filter.Tendsto c Filter.atTop
      (nhds (∫ x in A, w x * (g (prefixProj α r x) * F x) ∂ρ)) := by
    have hconv := tendsto_integral_abs_birkhoffAverage_indicator_coord
      hρ.measurePreserving_shift hB r
    rw [← hφdef, ← hFdef] at hconv
    have hp_bdd : ∀ᵐ x ∂ρ, ‖w x * g (prefixProj α r x)‖ ≤ 1 := by
      filter_upwards [hw_bdd] with x hwx
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul hwx (hg_bdd _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hpm : Measurable fun x : ℕ → α => w x * g (prefixProj α r x) := hw'.mul hgm
    simpa only [hcdef, mul_assoc] using
      tendsto_setIntegral_mul_of_tendsto_integral_abs (A := A)
        hpm.aestronglyMeasurable hp_bdd havg_int hF_int hconv
  rw [tendsto_nhds_unique hL hR, hFdef]

/-- **Naming the limit as the invariant conditional law.** The `condExp` form above says the last
coordinate decouples; this says what it decouples into. -/
theorem setIntegral_weight_mul_prefix_mul_indicator_eq_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ContractableLaw ρ) {r : ℕ}
    {w : (ℕ → α) → ℝ} (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    (hw_bdd : ∀ᵐ x ∂ρ, |w x| ≤ 1)
    {g : (Fin r → α) → ℝ} (hg : Measurable g) (hg_bdd : ∀ y, |g y| ≤ 1)
    {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    ∫ x in A, w x * (g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ
      = ∫ x in A, w x * (g (prefixProj α r x)
          * ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real B) ∂ρ := by
  rw [hρ.setIntegral_weight_mul_prefix_mul_indicator_eq_condExp hw hw_bdd hg hg_bdd hB hA]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae
    (hρ.condExp_indicator_coord_ae_eq_invariantConditionalProbabilityMeasure hB r)] with x hx
  rw [hx]

end ContractableLaw

end Probability

end TauCeti

end
