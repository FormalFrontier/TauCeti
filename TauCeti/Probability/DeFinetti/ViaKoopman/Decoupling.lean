/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.BlockReduction
public import Mathlib.Dynamics.BirkhoffSum.Average
public import TauCeti.Probability.Ergodic.CondExpProjection

/-!
# Displacing the last coordinate of a block

The step that decouples one factor from a block, over an invariant event.

Appending the coordinate `r + m` to the prefix `0, 1, …, r - 1` gives a strictly increasing
selection for *every* `m`, so the block transport makes the set-integral of the resulting product
independent of `m`. Averaging over `m < n` therefore leaves the left-hand side unchanged while
turning the right-hand side into a Birkhoff average of `𝟙_B ∘ (· r)` under the shift — which is
where the mean ergodic theorem enters.

## Main results

Transport side:

* `strictMono_snoc_prefix` — appending `r + m` to the prefix is strictly increasing;
* `ContractableLaw.map_restrict_snoc_prefix_eq_prefixProj` — so every displacement pushes the
  restricted law to the same measure;
* `ContractableLaw.setIntegral_prefix_mul_indicator_displaced_eq` — hence the weighted set-integral
  does not depend on the displacement `m`;
* `ContractableLaw.setIntegral_prefix_mul_indicator_eq_birkhoffAverage` — so an average over
  `m < n` may be inserted for free, turning the integrand into a Birkhoff average.

Analytic side:

* `birkhoffAverage_shift_coord_eq` — the displaced coordinates *are* that Birkhoff average;
* `ContractableLaw.tendsto_integral_abs_birkhoffAverage_indicator_coord` — it converges in `L¹` to
  the conditional expectation given the invariants;
* `ContractableLaw.condExp_indicator_coord_ae_eq_invariantConditional` — and that limit is the
  invariant conditional law, by
  `ContractableLaw.setIntegral_comp_coord_eq_comp_zero_of_measurableSet_invariants`.

This is the engine of the Koopman factorization: the `m`-independence is what allows the average
over `m` to be inserted for free, and that average is what the ergodic theorem consumes.

The induction that combines the two sides is not here yet.
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
theorem strictMono_snoc_prefix (r m : ℕ) :
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

/-- **The displaced block has a law independent of the displacement.** Over an invariant event,
pushing the restricted law forward along the prefix-plus-`r + m` selection gives the same measure
for every `m` — namely the pushforward along the plain prefix of length `r + 1`.

This is the `m`-independence the decoupling runs on: because the right-hand side does not mention
`m`, an average over `m < n` may be inserted on the left without changing anything, and that
average is a Birkhoff average of the last coordinate under the shift. -/
theorem ContractableLaw.map_restrict_snoc_prefix_eq_prefixProj
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) (r m : ℕ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    (ρ.restrict A).map
        (fun x : ℕ → α => fun i : Fin (r + 1) =>
          x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + m) : Fin (r + 1) → ℕ) i))
      = (ρ.restrict A).map (prefixProj α (r + 1)) :=
  hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants
    (strictMono_snoc_prefix r m) hA

omit [MeasurableSpace α] in
/-- **The displaced coordinates are a Birkhoff average.** Reading coordinate `r` along the shift
orbit gives exactly the displaced coordinates `r, r + 1, …`, so the average over displacements is
`birkhoffAverage` of the single observable `𝟙_B ∘ (· r)`.

This is where the two halves of the argument meet: the left side is what the invariant transport
controls (each term has the same integral over an invariant event), and the right side is what the
mean ergodic theorem converges. -/
theorem birkhoffAverage_shift_coord_eq {B : Set α} (r n : ℕ) (x : ℕ → α) :
    birkhoffAverage ℝ (shift α) (fun y : ℕ → α => (B.indicator (fun _ => (1 : ℝ)) (y r))) n x
      = (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, B.indicator (fun _ => (1 : ℝ)) (x (r + m)) := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [shift_iterate_apply]

/-- **Every coordinate has the same set-integral over an invariant event.** The single-coordinate
instance of the block transport: reading coordinate `r` and reading coordinate `0` give the same
integral of any measurable real observable, over any invariant event. -/
theorem ContractableLaw.setIntegral_comp_coord_eq_comp_zero_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) (r : ℕ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {f : α → ℝ} (hf : Measurable f) :
    ∫ x in A, f (x r) ∂ρ = ∫ x in A, f (x 0) ∂ρ := by
  classical
  have hmap := hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants
    (k := fun _ : Fin 1 => r) (Subsingleton.strictMono _) hA
  have hmap0 := hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants
    (k := fun _ : Fin 1 => 0) (Subsingleton.strictMono _) hA
  have hg : Measurable fun y : Fin 1 → α => f (y 0) := hf.comp (measurable_pi_apply 0)
  have hcoord : ∀ (s : ℕ), Measurable fun x : ℕ → α => fun _ : Fin 1 => x s :=
    fun s => measurable_pi_lambda _ fun _ => measurable_pi_apply s
  have key : ∀ s : ℕ, StrictMono (fun _ : Fin 1 => s) → ∫ x in A, f (x s) ∂ρ
      = ∫ y, f (y 0) ∂((ρ.restrict A).map (prefixProj α 1)) := by
    intro s hs
    rw [← hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants hs hA,
      integral_map (hcoord s).aemeasurable hg.aestronglyMeasurable]
  rw [key r (Subsingleton.strictMono _), key 0 (Subsingleton.strictMono _)]

/-- **The Birkhoff averages of a coordinate indicator converge to the invariant conditional
expectation of the first coordinate.** Combining the mean ergodic bridge with the fact that every
coordinate agrees with the first: the limit is named at coordinate `0`, which is where the
invariant conditional law is defined. -/
theorem ContractableLaw.tendsto_integral_abs_birkhoffAverage_indicator_coord
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ContractableLaw ρ)
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
  exact tendsto_integral_abs_birkhoffAverage_sub_condExp (shift α) hρ.measurePreserving_shift
    (MemLp.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbdd))

/-- **The invariant conditional law computes every coordinate, not just the first.** Combining the
witness's characteristic property at coordinate `0` with the transport fact that all coordinates
agree over invariant events. This is what lets the Birkhoff limit at coordinate `r` be named as the
witness. -/
theorem ContractableLaw.condExp_indicator_coord_ae_eq_invariantConditional
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
      rw [setIntegral_congr_ae (hle _ hs) (hwit.mono fun x hx _ => hx),
        setIntegral_condExp hle hint0 hs]
      rfl
    rw [h0]
    exact (hρ.setIntegral_comp_coord_eq_comp_zero_of_measurableSet_invariants r hs
      (measurable_const.indicator hB)).symm
  · exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hwit.symm

/-- **A weighted block integral does not depend on the displacement.** For a weight `g` reading
only the first `r` coordinates, the integral over an invariant event of `g` times the indicator at
coordinate `r + m` is the same for every `m` — in particular equal to its value at `m = 0`.

This is the `m`-independence in the form the induction consumes: the left-hand side may therefore
be replaced by an average over `m < n` at no cost, and that average is a Birkhoff average. -/
theorem ContractableLaw.setIntegral_prefix_mul_indicator_displaced_eq
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {r : ℕ} {g : (Fin r → α) → ℝ}
    (hg : Measurable g) {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) (m : ℕ) :
    ∫ x in A, g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + m)) ∂ρ
      = ∫ x in A, g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r) ∂ρ := by
  classical
  -- The combined observable on a block of length `r + 1`.
  set G : (Fin (r + 1) → α) → ℝ := fun y =>
    g (fun j : Fin r => y j.castSucc) * B.indicator (fun _ => (1 : ℝ)) (y (Fin.last r)) with hG
  have hG_meas : Measurable G := by
    refine Measurable.mul ?_ ?_
    · exact hg.comp (measurable_pi_lambda _ fun j => measurable_pi_apply j.castSucc)
    · exact (measurable_const.indicator hB).comp (measurable_pi_apply (Fin.last r))
  have hsel : ∀ (d : ℕ), Measurable
      (fun x : ℕ → α => fun i : Fin (r + 1) =>
        x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + d) : Fin (r + 1) → ℕ) i)) :=
    fun d => measurable_pi_lambda _ fun i => measurable_pi_apply _
  -- Reading the combined observable along the displaced selection is the integrand.
  have hcomp : ∀ (d : ℕ) (x : ℕ → α),
      G (fun i : Fin (r + 1) =>
          x ((Fin.snoc (fun j : Fin r => (j : ℕ)) (r + d) : Fin (r + 1) → ℕ) i))
        = g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x (r + d)) := by
    intro d x
    simp only [hG, Fin.snoc_castSucc, Fin.snoc_last]
    rfl
  -- Every displacement pushes the restricted law to the same measure.
  have key : ∀ d : ℕ, ∫ x in A, g (prefixProj α r x)
      * B.indicator (fun _ => (1 : ℝ)) (x (r + d)) ∂ρ
      = ∫ y, G y ∂((ρ.restrict A).map (prefixProj α (r + 1))) := by
    intro d
    rw [← hρ.map_restrict_snoc_prefix_eq_prefixProj r d hA,
      integral_map (hsel d).aemeasurable hG_meas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hcomp d x).symm)
  rw [key m, ← key 0, Nat.add_zero]

/-- **The weighted integral equals its own Birkhoff average.** Because the displaced integrals all
agree, averaging over `m < n` changes nothing on the left while turning the integrand on the right
into a Birkhoff average — for every `n ≠ 0`.

This is the step that hands the argument to the mean ergodic theorem. -/
theorem ContractableLaw.setIntegral_prefix_mul_indicator_eq_birkhoffAverage
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ) {r : ℕ}
    {g : (Fin r → α) → ℝ} (hg : Measurable g) (hg_bdd : ∀ y, |g y| ≤ 1)
    {B : Set α} (hB : MeasurableSet B)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ x in A, g (prefixProj α r x) * B.indicator (fun _ => (1 : ℝ)) (x r) ∂ρ
      = ∫ x in A, g (prefixProj α r x)
          * birkhoffAverage ℝ (shift α)
              (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r)) n x ∂ρ := by
  classical
  have hAm : MeasurableSet A := MeasurableSpace.invariants_le _ _ hA
  have hgm : Measurable fun x : ℕ → α => g (prefixProj α r x) :=
    hg.comp (measurable_prefixProj r)
  have hterm : ∀ d : ℕ, Integrable
      (fun x : ℕ → α => g (prefixProj α r x)
        * B.indicator (fun _ => (1 : ℝ)) (x (r + d))) (ρ.restrict A) := by
    intro d
    have hm : Measurable fun x : ℕ → α => g (prefixProj α r x)
        * B.indicator (fun _ => (1 : ℝ)) (x (r + d)) :=
      hgm.mul ((measurable_const.indicator hB).comp (measurable_pi_apply (r + d)))
    refine ⟨hm.aestronglyMeasurable, .of_bounded (C := 1) (Filter.Eventually.of_forall ?_)⟩
    intro x
    have h0 : (0 : ℝ) ≤ B.indicator (fun _ => (1 : ℝ)) (x (r + d)) :=
      Set.indicator_apply_nonneg fun _ => zero_le_one
    have h1 : B.indicator (fun _ => (1 : ℝ)) (x (r + d)) ≤ 1 :=
      Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    calc |g (prefixProj α r x)| * B.indicator (fun _ => (1 : ℝ)) (x (r + d))
        ≤ 1 * 1 := mul_le_mul (hg_bdd _) h1 h0 zero_le_one
      _ = 1 := one_mul 1
  -- Expand the Birkhoff average and integrate term by term.
  have hrhs : ∫ x in A, g (prefixProj α r x)
      * birkhoffAverage ℝ (shift α)
          (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y r)) n x ∂ρ
      = (n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, ∫ x in A, g (prefixProj α r x)
          * B.indicator (fun _ => (1 : ℝ)) (x (r + m)) ∂ρ := by
    rw [← integral_finsetSum _ fun m _ => hterm m, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [birkhoffAverage_shift_coord_eq, ← Finset.mul_sum]
    ring
  rw [hrhs]
  simp only [hρ.setIntegral_prefix_mul_indicator_displaced_eq hg hB hA]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

end Probability

end TauCeti

end
