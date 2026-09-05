/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Approximation of a finite-moment law by a finitely supported one

On a separable ground space every probability measure with finite `p`-moment can be pushed within
any prescribed Wasserstein accuracy by a quantizer, for every finite exponent `1 ≤ p < ∞`. When
singletons are measurable, these pushforwards are measures carried by finite sets. This file also
records the two standard consequences: the finitely supported laws are dense in
`TauCeti.WassersteinSpace p X` under the compatible standard-Borel and second-countability
hypotheses, and the `N`-point quantization error of a fixed law tends to `0`.

The approximating measures are produced by a *quantizer*: a measurable map `T : X → X` with
finitely many values, approximating the identity. The displacement bound
`TauCeti.wassersteinEDist_map_le` — the graph plan of `T` is a coupling of `μ` with `μ.map T`, so
the Wasserstein distance between them is at most the `L^p (μ)` seminorm of `x ↦ edist x (T x)` —
turns an estimate on the displacement into an estimate on the distance. The map itself sends `x`
to `u i`, for the least index `i` of a dense sequence `u` with `dist x (u i) < δ` when that index
is smaller than a cutoff `n`, and to `u 0` otherwise. The displacement is then at most `δ` off the
tail set of points whose least index is at least `n`, and those tail sets decrease to the empty
set, so the finite `p`-moment about `u 0` makes their contribution vanish by dominated
convergence.

The construction uses a finite exponent: at `p = ∞` a displacement that is small off a set of
small measure is not small in `L^∞`, and finitely supported laws need not be `W_∞`-dense on a
general separable metric space (for example, on a countably infinite discrete metric space).
The ground space is separable, which is where the dense sequence comes from.

## Support conventions

A quantizer statement — the map `T` takes finitely many values — is available on a pseudometric
ground space, whereas the assertion that a measure gives mass `0` to the complement of a finite
set is not: in a pseudometric space that complement need not be measurable. On an infinite type
with the zero pseudometric and its Borel structure, no probability measure vanishes on the
complement of a finite set. The measure-level statements therefore ask for measurable singletons,
which a metric ground space with its Borel structure supplies for free. For the same reason the
finite carrier is recorded as a `Finset X` whose complement is null, rather than through
`MeasureTheory.Measure.support`: on a pseudometric space the topological support of a Dirac law is
the whole ball of radius `0` around its atom, so it is not finite.

## Main statements

* `TauCeti.wassersteinEDist_map_le` — the displacement bound: `W_p (μ, T_* μ)` is at most the
  `L^p (μ)` seminorm of `x ↦ edist x (T x)`;
* `TauCeti.hasFiniteMoment_of_ae_mem_finset` — a law carried by a finite set has finite
  `p`-moment for every exponent;
* `TauCeti.exists_map_wassersteinEDist_le` — the approximation theorem in quantizer form: some
  measurable map with finitely many values pushes `μ` to within `ε` of itself;
* `TauCeti.exists_ae_mem_finset_wassersteinEDist_le` — its measure form, with the approximating
  law carried by a finite set and again of finite `p`-moment, assuming measurable singletons;
* `TauCeti.WassersteinSpace.dense_setOfPred_ae_mem_finset` — the finitely supported laws are dense
  in `P_p (X)` on a pseudometric ground space with `[StandardBorelSpace X]`, `[BorelSpace X]`,
  and `[SecondCountableTopology X]`;
* `TauCeti.wassersteinQuantizationError` and `TauCeti.tendsto_wassersteinQuantizationError` — the
  `N`-point quantization error and its convergence to `0`.

## Implementation notes

`TauCeti.wassersteinQuantizationError` is an infimum over competitors, so it is defined without
any hypothesis on the ground space and carries no attainment claim: a best `N`-point quantizer
need not exist at this generality, and the rate at which the error decays is a separate question
with its own hypotheses. Only `TauCeti.tendsto_wassersteinQuantizationError` uses the
approximation theorem.

The approximation theorem is stated with a target accuracy `ε : ℝ≥0∞` rather than as a limit
along a sequence of quantizers, because the sequence of cutoffs is chosen after the radius and
the two are not indexed by a single parameter.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  the density of finitely supported laws in `P_p (X)` is used to reduce statements about general
  laws to finite ones.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
* S. Graf and H. Luschgy, *Foundations of Quantization for Probability Distributions*, Lecture
  Notes in Mathematics 1730, Springer 2000, Chapter I, for the quantization error.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

section Approximation

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  {μ : Measure X} {ε : ℝ≥0∞}

/-- **Approximation by a quantizer.** On a separable ground space, a probability measure with
finite `p`-moment and a finite exponent `1 ≤ p < ∞` is pushed to within any prescribed accuracy
of itself by a measurable map taking finitely many values. -/
theorem exists_map_wassersteinEDist_le (hp : 1 ≤ p) (hp_top : p ≠ ∞) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMoment p μ) (hε : ε ≠ 0) :
    ∃ (s : Finset X) (T : X → X), Measurable T ∧ (∀ x, T x ∈ s) ∧
      wassersteinEDist p μ (μ.map T) ≤ ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  classical
  have : Nonempty X := ⟨(hasFiniteMoment_def.1 hμ).choose⟩
  -- the accuracy, halved and truncated to a finite nonzero value
  set c : ℝ≥0∞ := min ε 1 / 2 with hc_def
  have hmin_pos : 0 < min ε 1 := lt_min (pos_iff_ne_zero.2 hε) one_pos
  have hc_ne_top : c ≠ ∞ :=
    (ENNReal.div_lt_top (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)) two_ne_zero).ne
  have hc_ne_zero : c ≠ 0 := by
    simp only [hc_def, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hmin_pos.ne', ENNReal.ofNat_ne_top⟩
  set δ : ℝ := c.toReal with hδ_def
  have hδ : 0 < δ := ENNReal.toReal_pos hc_ne_zero hc_ne_top
  have hδc : ENNReal.ofReal δ = c := ENNReal.ofReal_toReal hc_ne_top
  -- the least index of a dense sequence within `δ` of a point
  set u : ℕ → X := TopologicalSpace.denseSeq X with hu_def
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  have hidx : ∀ x : X, ∃ i, dist x (u i) < δ := fun x ↦ Metric.denseRange_iff.1 hu x δ hδ
  set idx : X → ℕ := fun x ↦ Nat.find (hidx x) with hidx_def
  have hidx_spec : ∀ x, dist x (u (idx x)) < δ := fun x ↦ Nat.find_spec (hidx x)
  have hidx_meas : Measurable idx := measurable_find hidx fun k ↦ measurableSet_ball
  -- the ground distance to the basepoint `u 0`, and its `p`-th moment
  set f : X → ℝ≥0∞ := fun y ↦ edist (u 0) y with hf_def
  have hf_meas : Measurable f := measurable_edist.comp (measurable_const.prodMk measurable_id)
  have hmom : MemLp f p μ := hμ.memLp hf_meas.aestronglyMeasurable
  have hfin : ∫⁻ y, f y ^ p.toReal ∂μ ≠ ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_eq_self, lt_top_iff_ne_top] using
      (hmom.integrable_enorm_rpow hp0 hp_top).hasFiniteIntegral
  -- the tail sets decrease to the empty set, so their contribution vanishes
  set A : ℕ → Set X := fun n ↦ {x | n ≤ idx x} with hA_def
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n ↦ hidx_meas MeasurableSet.of_discrete
  have hA_tendsto : Tendsto (fun n ↦ ∫⁻ y, (A n).indicator (fun z ↦ f z ^ p.toReal) y ∂μ)
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ y ∂μ,
        Tendsto (fun n ↦ (A n).indicator (fun z ↦ f z ^ p.toReal) y) atTop (𝓝 0) := by
      refine .of_forall fun y ↦ Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (idx y)] with n hn
      exact (Set.indicator_of_notMem (by simpa [hA_def] using not_le.2 hn) _).symm
    have key := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun n y ↦ (A n).indicator (fun z ↦ f z ^ p.toReal) y) (f := fun _ ↦ (0 : ℝ≥0∞))
      (bound := fun z ↦ f z ^ p.toReal)
      (fun n ↦ (ENNReal.continuous_rpow_const.measurable.comp hf_meas).indicator (hA_meas n))
      (fun n ↦ .of_forall fun y ↦ Set.indicator_le_self _ _ y) hfin hlim
    simpa using key
  obtain ⟨n, hn⟩ : ∃ n, ∫⁻ y, (A n).indicator (fun z ↦ f z ^ p.toReal) y ∂μ ≤ c ^ p.toReal := by
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hA_tendsto _
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc_ne_zero) hc_ne_top)
    exact ⟨N, hN N le_rfl⟩
  -- the quantizer: the nearest listed point of index below the cutoff, and `u 0` beyond it
  set T : X → X := fun x ↦ if idx x < n then u (idx x) else u 0 with hT_def
  have hT_meas : Measurable T :=
    (Measurable.of_discrete (f := fun i : ℕ ↦ if i < n then u i else u 0)).comp hidx_meas
  refine ⟨(Finset.range (n + 1)).image u, T, hT_meas, fun x ↦ ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_range, hT_def]
    by_cases h : idx x < n
    · exact ⟨idx x, by omega, by simp [h]⟩
    · exact ⟨0, by omega, by simp [h]⟩
  -- the displacement is at most `δ` off the tail set, and at most the tail distance on it
  have hbound : ∀ x, edist x (T x) ≤ ENNReal.ofReal δ + (A n).indicator f x := by
    intro x
    by_cases h : idx x < n
    · refine le_trans ?_ (self_le_add_right _ _)
      have hTx : T x = u (idx x) := by simp [hT_def, h]
      rw [hTx, edist_dist]
      exact ENNReal.ofReal_le_ofReal (hidx_spec x).le
    · have hx : x ∈ A n := by simpa [hA_def] using not_lt.1 h
      have hTx : T x = u 0 := by simp [hT_def, h]
      rw [hTx, Set.indicator_of_mem hx, hf_def, edist_comm]
      exact self_le_add_left _ _
  have hind : eLpNorm ((A n).indicator f) p μ ≤ c := by
    refine (ENNReal.rpow_le_rpow_iff ht).1 ?_
    rw [eLpNorm_rpow_eq_lintegral hp0 hp_top]
    refine le_trans (le_of_eq (lintegral_congr fun y ↦ ?_)) hn
    by_cases hy : y ∈ A n
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos ht]
  calc wassersteinEDist p μ (μ.map T)
      ≤ eLpNorm (fun x ↦ edist x (T x)) p μ :=
        wassersteinEDist_map_le measurable_edist hT_meas.aemeasurable p
    _ ≤ eLpNorm ((fun _ : X ↦ ENNReal.ofReal δ) + (A n).indicator f) p μ :=
        eLpNorm_mono_enorm fun x ↦ by simpa using hbound x
    _ ≤ eLpNorm (fun _ : X ↦ ENNReal.ofReal δ) p μ + eLpNorm ((A n).indicator f) p μ :=
        eLpNorm_add_le aestronglyMeasurable_const
          (hf_meas.indicator (hA_meas n)).aestronglyMeasurable hp
    _ ≤ c + c := by
        refine add_le_add (le_of_eq ?_) hind
        rw [eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero μ)]
        simp [hδc]
    _ ≤ ε := by rw [hc_def, ENNReal.add_halves]; exact min_le_left _ _

variable [MeasurableSingletonClass X]

/-- **Approximation by a finitely supported law.** On a separable ground space with measurable
singletons, a probability measure with finite `p`-moment and a finite exponent `1 ≤ p < ∞` is
within any prescribed accuracy of a probability measure carried by a finite set, which again has
finite `p`-moment. -/
theorem exists_ae_mem_finset_wassersteinEDist_le (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [IsProbabilityMeasure μ] (hμ : HasFiniteMoment p μ) (hε : ε ≠ 0) :
    ∃ (s : Finset X) (ν : Measure X), IsProbabilityMeasure ν ∧ ν ((s : Set X)ᶜ) = 0 ∧
      HasFiniteMoment p ν ∧ wassersteinEDist p μ ν ≤ ε := by
  obtain ⟨s, T, hT, hTs, hle⟩ := exists_map_wassersteinEDist_le hp hp_top hμ hε
  have hnull : (μ.map T) ((s : Set X)ᶜ) = 0 := by
    rw [Measure.map_apply hT (s.measurableSet.compl)]
    convert measure_empty (μ := μ)
    exact eq_empty_of_forall_notMem fun x hx ↦ hx (hTs x)
  refine ⟨s, μ.map T, inferInstance, hnull, ?_, hle⟩
  refine hasFiniteMoment_of_ae_mem_finset (s := s) (hasFiniteMoment_def.1 hμ).choose ?_
  exact mem_ae_iff.2 hnull

end Approximation

namespace WassersteinSpace

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **The finitely supported laws are dense in `P_p (X)`.** On a pseudometric ground space with
`[StandardBorelSpace X]`, a compatible `[BorelSpace X]`, and `[SecondCountableTopology X]`, and
for a finite exponent `1 ≤ p < ∞`, every finite-moment law is a Wasserstein limit of laws carried
by finite sets. -/
theorem dense_setOfPred_ae_mem_finset (hp_top : p ≠ ∞) :
    Dense {μ : WassersteinSpace p X |
      ∃ s : Finset X, ((μ : ProbabilityMeasure X) : Measure X) ((s : Set X)ᶜ) = 0} := by
  refine Metric.dense_iff.2 fun μ r hr ↦ ?_
  obtain ⟨s, ν, hν, hnull, hmom, hle⟩ :=
    exists_ae_mem_finset_wassersteinEDist_le (μ := ((μ : ProbabilityMeasure X) : Measure X))
      Fact.out hp_top μ.hasFiniteMoment
      (ε := ENNReal.ofReal (r / 2)) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
  have hcoe : ((mk (⟨ν, hν⟩ : ProbabilityMeasure X) hmom : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν, hν⟩ := coe_mk _ _
  refine ⟨mk ⟨ν, hν⟩ hmom, ?_, s, by rw [hcoe]; exact hnull⟩
  rw [Metric.mem_ball, dist_comm, dist_def, hcoe]
  refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) hle) ?_
  linarith

end WassersteinSpace

section Quantization

variable [EDist X]

/-- The **`N`-point quantization error** of `μ` at exponent `p`: the infimum of the Wasserstein
distances from `μ` to the probability measures carried by a set of at most `N` points.

This is an infimum, not a minimum: a best `N`-point quantizer need not exist at this
generality. -/
def wassersteinQuantizationError (p : ℝ≥0∞) (N : ℕ) (μ : Measure X) : ℝ≥0∞ :=
  ⨅ (ν : Measure X) (_ : IsProbabilityMeasure ν)
    (_ : ∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0), wassersteinEDist p μ ν

variable {μ ν : Measure X} {N : ℕ}

/-- Every competitor bounds the quantization error from above. -/
theorem wassersteinQuantizationError_le (hν : IsProbabilityMeasure ν)
    (hs : ∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) :
    wassersteinQuantizationError p N μ ≤ wassersteinEDist p μ ν :=
  iInf_le_of_le ν (iInf_le_of_le hν (iInf_le _ hs))

/-- A bound valid for every admissible competitor bounds the quantization error from below. -/
theorem le_wassersteinQuantizationError {a : ℝ≥0∞}
    (h : ∀ (ν : Measure X) (_ : IsProbabilityMeasure ν),
      (∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) →
        a ≤ wassersteinEDist p μ ν) :
    a ≤ wassersteinQuantizationError p N μ :=
  le_iInf₂ fun ν hν ↦ le_iInf fun hs ↦ h ν hν hs

/-- The quantization error is below a strict threshold exactly when an admissible competitor is
below that threshold. -/
theorem wassersteinQuantizationError_lt_iff {a : ℝ≥0∞} :
    wassersteinQuantizationError p N μ < a ↔
      ∃ ν : Measure X, IsProbabilityMeasure ν ∧
        (∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) ∧
          wassersteinEDist p μ ν < a := by
  simp only [wassersteinQuantizationError, iInf_lt_iff, exists_prop]

/-- The quantization error decreases as more points are allowed. -/
theorem wassersteinQuantizationError_antitone :
    Antitone fun N ↦ wassersteinQuantizationError p N μ := by
  refine fun N M hNM ↦ le_iInf₂ fun ν hν ↦ le_iInf fun hs ↦ ?_
  obtain ⟨s, hcard, hnull⟩ := hs
  exact wassersteinQuantizationError_le hν ⟨s, hcard.trans hNM, hnull⟩

end Quantization

section QuantizationTendsto

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSingletonClass X] {μ : Measure X}

/-- **The quantization error vanishes.** On a separable ground space with measurable singletons
and for a finite exponent `1 ≤ p < ∞`, the `N`-point quantization error of a law with finite
`p`-moment tends to `0`. No rate is claimed: a quantitative bound needs further hypotheses on the
law. -/
theorem tendsto_wassersteinQuantizationError (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [IsProbabilityMeasure μ] (hμ : HasFiniteMoment p μ) :
    Tendsto (fun N ↦ wassersteinQuantizationError p N μ) atTop (𝓝 0) := by
  refine (ENNReal.tendsto_atTop_zero_iff_le_of_antitone
    wassersteinQuantizationError_antitone).2 fun ε hε ↦ ?_
  obtain ⟨s, ν, hν, hnull, -, hle⟩ :=
    exists_ae_mem_finset_wassersteinEDist_le hp hp_top hμ hε.ne'
  exact ⟨s.card, (wassersteinQuantizationError_le hν ⟨s, le_rfl, hnull⟩).trans hle⟩

end QuantizationTendsto

end TauCeti
