/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.BallAverage
public import Mathlib.MeasureTheory.Function.UnifTight

import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# The Fréchet--Kolmogorov compactness criterion in `Lᵖ`

The **Fréchet--Kolmogorov** (or Kolmogorov--Riesz) theorem is the `Lᵖ` analogue of
Arzelà--Ascoli: it identifies the sets of `Lᵖ` functions that are relatively compact. This file
proves its sufficiency direction, for `1 ≤ p < ∞` and functions on a proper normed additive group
`E` carrying an additive Haar measure, with values in a finite-dimensional real normed space. A
family `S` of `Lᵖ` functions is totally bounded as soon as

* it is **bounded** in `Lᵖ`;
* its **translation increments are uniformly small**: for every `ε > 0` there is a `δ > 0` with
  `‖f(· + h) - f‖_p ≤ ε` for every `f ∈ S` and every `‖h‖ < δ`;
* it is **uniformly tight** in the sense of `MeasureTheory.UnifTight`.

Neither of the last two hypotheses can be dropped. On `ℝ`, the concentrating family
`n ^ (1/p) 1_{[0, 1/n]}` is bounded and tight but has translation increments of size of order one
at every scale, and the escaping family `f(· - n)` of translates of a single nonzero `f` is
bounded and has a translation-invariant modulus but is not tight; neither is totally bounded. The
`Lᵖ` bound is carried explicitly, as in the classical statements.

The tightness hypothesis is automatic for a family vanishing almost everywhere off a fixed bounded
set, which is the form
`TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl` records. This is the form
that Rellich--Kondrachov for `W^{1,p}_0(Ω)` consumes: extending by zero makes a function vanish off
`Ω`, and its translation increments are controlled by `‖h‖ ‖∇u‖_p` through
`TauCeti.W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient`. The `W^{1,p}(Ω)` clause of
Lane A.6 additionally needs an extension operator and boundary regularity.

## The proof

The two halves of the argument are already available. Smoothing is done by the **ball average**
`TauCeti.ballAverage`, whose four estimates are in
`TauCeti/MeasureTheory/Function/Lp/BallAverage.lean`: at a fixed scale `r` the ball averages of
the family are uniformly bounded (`TauCeti.enorm_ballAverage_le`), uniformly equicontinuous
(`TauCeti.enorm_ballAverage_add_sub_ballAverage_le`, packaged for a family as
`TauCeti.uniformEquicontinuous_ballAverage`) and, once `r` is smaller than the translation modulus
of the family at `ε`, uniformly within `ε` of the family itself
(`TauCeti.eLpNorm_ballAverage_sub_le`). Compactness of that smoothed family is
Mathlib's `BoundedContinuousFunction.arzela_ascoli`, applied after restricting the ball averages
to a large compact closed ball `K`.

Putting the two together, `‖f - f'‖_p` for `f'` the chosen approximant is split as the `Lᵖ`
seminorm over `K` plus the one over its complement. Off `K` tightness bounds each of `f` and `f'`
separately; on `K` the difference is compared with the difference of the two ball averages, which
is uniformly at most `η` there, and `μ K ^ (1/p) η` is made small by the choice of `η`.

## Main declarations

* `TauCeti.totallyBounded_of_comp_add_sub_of_unifTight`,
  `TauCeti.isCompact_closure_of_comp_add_sub_of_unifTight`: the Fréchet--Kolmogorov criterion, in
  totally bounded and in relatively compact form.
* `TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`,
  `TauCeti.isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`: the criterion for a
  family vanishing almost everywhere off a fixed bounded set, in totally bounded and in relatively
  compact form.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Theorem 4.26 and Corollary 4.27; H. Hanche-Olsen, H. Holden,
*The Kolmogorov--Riesz compactness theorem*, Expo. Math. 28 (2010).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal

section ArzelaAscoli

variable {X F ι : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The finite uniform net on a compact set extracted from Arzelà--Ascoli. -/
private theorem exists_finite_approx_on_isCompact {K : Set X} (hK : IsCompact K)
    {g : ι → X → F} {C η : ℝ}
    (hC : ∀ i x, g i x ∈ closedBall (0 : F) C) (hequi : UniformEquicontinuous g) (hη : 0 < η) :
    ∃ t : Set ι, t.Finite ∧ ∀ i, ∃ j ∈ t, ∀ x ∈ K, dist (g i x) (g j x) ≤ η := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let φ : ι → BoundedContinuousFunction K F := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x : K => g i x, (hequi.equicontinuous.continuous i).comp continuous_subtype_val⟩
  let 𝒜 : Set (BoundedContinuousFunction K F) := Set.range φ
  have hφcoe : ∀ i : ι, ⇑(φ i) = K.domRestrict (g i) := fun i => by
    rfl
  have hφequi : Equicontinuous fun i : ι => (φ i : K → F) := by
    rw [funext hφcoe]
    exact (equicontinuous_restrict_iff _).2 (hequi.equicontinuous.equicontinuousOn K)
  have h𝒜equi : Equicontinuous ((↑) : 𝒜 → K → F) := by
    rw [← Set.comp_rangeSplitting φ]
    exact hφequi.comp (Set.rangeSplitting φ)
  have h𝒜compact : IsCompact (closure 𝒜) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) C)
      (isCompact_closedBall _ _) 𝒜 (by
        intro q x hq
        obtain ⟨i, rfl⟩ := hq
        simpa only [φ, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
          hC i x) h𝒜equi
  have h𝒜tb : TotallyBounded 𝒜 := h𝒜compact.totallyBounded.subset subset_closure
  obtain ⟨u, hu𝒜, hufin, hucover⟩ := h𝒜tb.exists_subset (dist_mem_uniformity hη)
  let _ : Finite u := hufin.to_subtype
  choose idx hidx using fun q : u => hu𝒜 q.2
  refine ⟨Set.range idx, Set.finite_range idx, fun i => ?_⟩
  obtain ⟨q, hqu, hiq⟩ : ∃ q ∈ u, dist (φ i) q < η := by
    simpa only [mem_iUnion, mem_ofPred_eq, exists_prop] using hucover (Set.mem_range_self i)
  let q' : u := ⟨q, hqu⟩
  refine ⟨idx q', Set.mem_range_self q', fun x hx => ?_⟩
  have hφdist : dist (φ i) (φ (idx q')) < η := by rw [hidx q']; exact hiq
  simpa only [φ, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
    (BoundedContinuousFunction.dist_coe_le_dist (f := φ i) (g := φ (idx q'))
      ⟨x, hx⟩).trans hφdist.le

end ArzelaAscoli

section LpApproximation

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {mu : Measure α} {p : ℝ≥0∞}

/-- The comparison estimate used internally below: `f` and `f'` are approximated in `Lᵖ` by
`A` and `A'`, the approximants are uniformly close on `K`, and the original functions have small
`Lᵖ` tails off `K`. -/
private theorem eLpNorm_sub_le_of_approx_of_dist_bdd_on {K : Set α}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hK : MeasurableSet K) {f f' A A' : α → F} {η : ℝ}
    (hf : AEStronglyMeasurable f mu) (hf' : AEStronglyMeasurable f' mu)
    (hA : AEStronglyMeasurable A mu) (hA' : AEStronglyMeasurable A' mu)
    (hη : 0 ≤ η) (hmid : ∀ x ∈ K, dist (A x) (A' x) ≤ η) :
    eLpNorm (f - f') p mu ≤
      eLpNorm (A - f) p mu +
        (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + eLpNorm (A' - f') p mu) +
        (eLpNorm (Kᶜ.indicator f) p mu + eLpNorm (Kᶜ.indicator f') p mu) := by
  have hsplit : (f - f' : α → F) = K.indicator (f - f') + Kᶜ.indicator (f - f') :=
    (Set.indicator_self_add_compl K _).symm
  have htail_sub : eLpNorm (Kᶜ.indicator (f - f')) p mu ≤
      eLpNorm (Kᶜ.indicator f) p mu + eLpNorm (Kᶜ.indicator f') p mu := by
    rw [Set.indicator_sub']
    exact eLpNorm_sub_le (hf.indicator hK.compl) (hf'.indicator hK.compl) hp
  have hnear : eLpNorm (K.indicator (f - f')) p mu ≤
      eLpNorm (A - f) p mu +
        (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + eLpNorm (A' - f') p mu) := by
    have hdecomp : K.indicator (f - f' : α → F) =
        K.indicator (f - A) + (K.indicator (A - A') + K.indicator (A' - f')) := by
      rw [← Set.indicator_add', ← Set.indicator_add']
      congr 1
      abel
    rw [hdecomp]
    refine (eLpNorm_add_le ((hf.sub hA).indicator hK)
      (((hA.sub hA').indicator hK).add ((hA'.sub hf').indicator hK)) hp).trans ?_
    refine add_le_add ?_ ((eLpNorm_add_le ((hA.sub hA').indicator hK)
      ((hA'.sub hf').indicator hK) hp).trans (add_le_add ?_ ?_))
    · refine (eLpNorm_indicator_le _).trans ?_
      rw [← neg_sub A f, eLpNorm_neg]
    · exact eLpNorm_indicator_sub_le_of_dist_bdd mu hp' hK hη hmid
    · exact eLpNorm_indicator_le _
  calc
    eLpNorm (f - f') p mu
        ≤ eLpNorm (K.indicator (f - f')) p mu + eLpNorm (Kᶜ.indicator (f - f')) p mu := by
          conv_lhs => rw [hsplit]
          exact eLpNorm_add_le ((hf.sub hf').indicator hK) ((hf.sub hf').indicator hK.compl) hp
    _ ≤ eLpNorm (A - f) p mu +
          (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + eLpNorm (A' - f') p mu) +
          (eLpNorm (Kᶜ.indicator f) p mu + eLpNorm (Kᶜ.indicator f') p mu) :=
      add_le_add hnear htail_sub

/-- A small tail off `s`, a small approximation error, and a uniformly bounded approximant give a
small tail off `K` when `s \ K` has sufficiently small measure. -/
private theorem eLpNorm_indicator_compl_le_of_approx_of_bound
    (hp : 1 ≤ p) (hp' : p ≠ ∞) {K s : Set α} (hK : MeasurableSet K)
    (hs : MeasurableSet s) {f A : α → F} (hf : AEStronglyMeasurable f mu)
    (hA : AEStronglyMeasurable A mu) {B ε : ℝ≥0∞} (hBt : B ≠ ∞)
    (htail : eLpNorm (sᶜ.indicator f) p mu ≤ ε) (happrox : eLpNorm (A - f) p mu ≤ ε)
    (hbound : ∀ x, A x ∈ closedBall (0 : F) B.toReal)
    (hsmall : B * mu (s ∩ Kᶜ) ^ (1 / p.toReal) ≤ ε) :
    eLpNorm (Kᶜ.indicator f) p mu ≤ ε + ε + ε := by
  have hsplit : Kᶜ.indicator f =
      (Kᶜ ∩ sᶜ).indicator f + (Kᶜ ∩ s).indicator f := by
    ext x
    by_cases hxK : x ∈ K <;> by_cases hxs : x ∈ s <;> simp [hxK, hxs]
  rw [hsplit]
  refine (eLpNorm_add_le (hf.indicator (hK.compl.inter hs.compl))
    (hf.indicator (hK.compl.inter hs)) hp).trans ?_
  have hfirst : eLpNorm ((Kᶜ ∩ sᶜ).indicator f) p mu ≤ ε :=
    (eLpNorm_mono_enorm fun x =>
      enorm_indicator_le_of_subset inter_subset_right _ x).trans htail
  have hsecond : eLpNorm ((Kᶜ ∩ s).indicator f) p mu ≤ ε + ε := by
    have hsplit' : (Kᶜ ∩ s).indicator f =
        (Kᶜ ∩ s).indicator (f - A) + (Kᶜ ∩ s).indicator A := by
      rw [← Set.indicator_add']
      congr 1
      abel
    rw [hsplit']
    refine (eLpNorm_add_le ((hf.sub hA).indicator (hK.compl.inter hs))
      (hA.indicator (hK.compl.inter hs)) hp).trans (add_le_add ?_ ?_)
    · refine (eLpNorm_indicator_le _).trans ?_
      rw [← neg_sub A f, eLpNorm_neg]
      exact happrox
    · have hA' : eLpNorm ((Kᶜ ∩ s).indicator A) p mu ≤
          B * mu (s ∩ Kᶜ) ^ (1 / p.toReal) := by
        have hbound' := eLpNorm_indicator_sub_le_of_dist_bdd (p := p) mu hp'
          (hK.compl.inter hs) ENNReal.toReal_nonneg
          (c := B.toReal) (f := A) (g := 0) (fun x _ => by
            simpa only [mem_closedBall, Pi.zero_apply, dist_zero_right, dist_comm] using hbound x)
        simpa only [Pi.zero_apply, sub_zero, ENNReal.ofReal_toReal hBt, inter_comm] using hbound'
      exact hA'.trans hsmall
  calc
    eLpNorm ((Kᶜ ∩ sᶜ).indicator f) p mu +
        eLpNorm ((Kᶜ ∩ s).indicator f) p mu ≤ ε + (ε + ε) :=
      add_le_add hfirst hsecond
    _ = ε + ε + ε := by ac_rfl

end LpApproximation

section FrechetKolmogorov

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Fréchet--Kolmogorov compactness criterion.** For `1 ≤ p < ∞`, a family `S` of `Lᵖ`
functions is totally bounded as soon as it is bounded in `Lᵖ`, its translation increments are
uniformly small in `Lᵖ`, and it is uniformly tight in the sense of `MeasureTheory.UnifTight`.

Dropping either of the last two hypotheses breaks the conclusion: on `ℝ` the concentrating family
`n ^ (1/p) 1_{[0, 1/n]}` satisfies all but the smallness of translations, and the escaping family
`f(· - n)` of translates of a single nonzero `f` satisfies all but tightness, and neither is
totally bounded. -/
theorem totallyBounded_of_comp_add_sub_of_unifTight (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)} {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε)
    (htight : UnifTight (fun i : S => ⇑(i : Lp F p mu)) p mu) :
    TotallyBounded S := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hε₁ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 16) := ENNReal.ofReal_pos.2 (by linarith)
  set ε₁ : ℝ≥0∞ := ENNReal.ofReal (ε / 16)
  obtain ⟨r, hr, hrS⟩ := htrans ε₁ hε₁
  obtain ⟨s, hmeasS, hmuS, htailS⟩ := htight.exists_measurableSet_indicator hε₁.ne'
  set V : ℝ≥0∞ := mu (ball (0 : E) r)
  -- The uniform `L^∞` bound on the ball averages of the family.
  set Bₑ : ℝ≥0∞ := V ^ (-(p.toReal)⁻¹) * M
  have hV0 : V ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : V ≠ ∞ := measure_ball_lt_top.ne
  have hBₑt : Bₑ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hV0 hVt) hM
  have hgB : ∀ i : S, ∀ x : E,
      ballAverage mu r ⇑(i : Lp F p mu) x ∈ closedBall (0 : F) Bₑ.toReal := fun i x => by
    rw [mem_closedBall, dist_zero_right]
    have h := (enorm_ballAverage_le hp hp' (Lp.aestronglyMeasurable (i : Lp F p mu)) hr x).trans
      (mul_le_mul' le_rfl (hbdd _ i.2))
    simpa [Bₑ, V] using ENNReal.toReal_mono hBₑt h
  -- The uniform equicontinuity of the ball averages, at the fixed scale `r`.
  have hequi : UniformEquicontinuous fun i : S => ballAverage mu r ⇑(i : Lp F p mu) :=
    uniformEquicontinuous_ballAverage hp hp' (fun i => Lp.memLp (i : Lp F p mu)) hr
      fun c hc => by
        obtain ⟨δ, hδ, hδS⟩ := htrans c hc
        exact ⟨δ, hδ, fun i => hδS _ i.2⟩
  have hsmooth : ∀ g ∈ S, eLpNorm (ballAverage mu r ⇑g - ⇑g) p mu ≤ ε₁ := by
    intro g hg
    exact eLpNorm_ballAverage_sub_le hp hp' (Lp.memLp g) hr
      (fun e he => hrS g hg e (by simpa [dist_eq_norm] using he))
  -- A finite-measure tightness set has arbitrarily small intersection with the complement of a
  -- sufficiently large closed ball.
  let _ : IsFiniteMeasure (mu.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hmuS⟩
  have hmeasure :
      Tendsto (fun R : ℝ => mu (s ∩ (closedBall (0 : E) R)ᶜ)) atTop (𝓝 0) := by
    have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet
      (S := {mu.restrict s}) isTightMeasureSet_singleton (0 : E)
    simpa only [iSup_singleton, Measure.restrict_apply measurableSet_closedBall.compl,
      inter_comm] using h
  have hsmall : Tendsto
      (fun R : ℝ => Bₑ * mu (s ∩ (closedBall (0 : E) R)ᶜ) ^ (1 / p.toReal))
      atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hBₑt (by positivity)).comp hmeasure
  obtain ⟨R, hR⟩ := ((tendsto_order.1 hsmall).2 ε₁ hε₁).exists
  set K : Set E := closedBall (0 : E) R
  have hmeasK : MeasurableSet K := measurableSet_closedBall
  have hRS : ∀ f ∈ S,
      eLpNorm (Kᶜ.indicator ⇑f) p mu ≤ ε₁ + ε₁ + ε₁ := by
    intro f hf
    exact eLpNorm_indicator_compl_le_of_approx_of_bound hp hp' hmeasK hmeasS
      (Lp.aestronglyMeasurable f)
      ((continuous_ballAverage hp hp' (Lp.memLp f) hr).aestronglyMeasurable) hBₑt
      (htailS ⟨f, hf⟩) (hsmooth f hf) (hgB ⟨f, hf⟩) hR.le
  -- The scale of the uniform approximation on `K`, calibrated by the measure of `K`.
  have hKt : mu K ≠ ∞ := measure_closedBall_lt_top.ne
  set W : ℝ≥0∞ := mu K ^ (1 / p.toReal)
  have hWt : W ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKt).ne
  have hWnn : (0 : ℝ) ≤ W.toReal := ENNReal.toReal_nonneg
  set η : ℝ := ε / (4 * (W.toReal + 1)) with hηdef
  have hη : 0 < η := by
    rw [hηdef]; positivity
  have hWη : ENNReal.ofReal η * W ≤ ENNReal.ofReal (ε / 4) := by
    have hkey : W.toReal * η ≤ ε / 4 := by
      have hstep : (W.toReal + 1) * η = ε / 4 := by
        rw [hηdef]; field_simp
      nlinarith [hη.le]
    calc ENNReal.ofReal η * W = ENNReal.ofReal (W.toReal * η) := by
          rw [ENNReal.ofReal_mul hWnn, ENNReal.ofReal_toReal hWt, mul_comm]
      _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hkey
  -- Arzelà--Ascoli supplies a finite uniform net for the restricted ball averages.
  obtain ⟨t, htfin, ht⟩ := exists_finite_approx_on_isCompact
    (isCompact_closedBall (0 : E) R) hgB hequi hη
  refine ⟨Subtype.val '' t, htfin.image (fun i : S => (i : Lp F p mu)), fun f hf => ?_⟩
  obtain ⟨j, hjt, hmid⟩ := ht ⟨f, hf⟩
  refine mem_iUnion₂.2 ⟨(j : Lp F p mu), ⟨j, hjt, rfl⟩, ?_⟩
  set f' : Lp F p mu := (j : Lp F p mu)
  set A : E → F := ballAverage mu r ⇑f
  set A' : E → F := ballAverage mu r ⇑f'
  have hfm : AEStronglyMeasurable (⇑f) mu := Lp.aestronglyMeasurable f
  have hf'm : AEStronglyMeasurable (⇑f') mu := Lp.aestronglyMeasurable f'
  have hAm : AEStronglyMeasurable A mu :=
    (continuous_ballAverage hp hp' (Lp.memLp f) hr).aestronglyMeasurable
  have hA'm : AEStronglyMeasurable A' mu :=
    (continuous_ballAverage hp hp' (Lp.memLp f') hr).aestronglyMeasurable
  -- The three estimates: smoothing, uniform approximation on `K`, and tightness off `K`.
  have hmain : eLpNorm (⇑f - ⇑f') p mu ≤ ENNReal.ofReal (3 * ε / 4) := by
    calc eLpNorm (⇑f - ⇑f') p mu
        ≤ eLpNorm (A - ⇑f) p mu +
            (ENNReal.ofReal η * W + eLpNorm (A' - ⇑f') p mu) +
            (eLpNorm (Kᶜ.indicator ⇑f) p mu + eLpNorm (Kᶜ.indicator ⇑f') p mu) :=
          eLpNorm_sub_le_of_approx_of_dist_bdd_on hp hp' hmeasK hfm hf'm hAm hA'm hη.le hmid
      _ ≤ ε₁ + (ENNReal.ofReal (ε / 4) + ε₁) +
            ((ε₁ + ε₁ + ε₁) + (ε₁ + ε₁ + ε₁)) := by
          exact add_le_add
            (add_le_add (by simpa only [A] using hsmooth f hf)
              (add_le_add hWη (by simpa only [A', f'] using hsmooth (j : Lp F p mu) j.2)))
            (add_le_add (hRS f hf) (by simpa only [f'] using hRS (j : Lp F p mu) j.2))
      _ = ENNReal.ofReal (3 * ε / 4) := by
          simp (disch := positivity) only [ε₁, ← ENNReal.ofReal_add]
          congr 1
          ring
  rw [mem_ball, Lp.dist_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

/-- **Relative compactness in `Lᵖ` under the Fréchet--Kolmogorov hypotheses**: the closure of an
`Lᵖ`-bounded, uniformly tight family whose translation increments are uniformly small in `Lᵖ` is
compact. This is the relative-compactness form of
`TauCeti.totallyBounded_of_comp_add_sub_of_unifTight`. -/
theorem isCompact_closure_of_comp_add_sub_of_unifTight (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)} {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε)
    (htight : UnifTight (fun i : S => ⇑(i : Lp F p mu)) p mu) :
    IsCompact (closure S) :=
  ((totallyBounded_of_comp_add_sub_of_unifTight hp' hM hbdd htrans
    htight).closure).isCompact_of_isClosed isClosed_closure

/-- **The Fréchet--Kolmogorov criterion for a family vanishing almost everywhere off a fixed bounded
set**, the form that Rellich--Kondrachov for `W^{1,p}_0(Ω)` consumes. For such functions the
tightness hypothesis is automatic, so an `Lᵖ`-bounded family whose translation increments are
uniformly small in `Lᵖ` is totally bounded. -/
theorem totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    TotallyBounded S := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine totallyBounded_of_comp_add_sub_of_unifTight hp' hM hbdd htrans ?_
  rw [unifTight_iff_ennreal]
  intro ε _
  refine ⟨closedBall (0 : E) R, measure_closedBall_lt_top.ne, fun f => ?_⟩
  have h0 : (closedBall (0 : E) R)ᶜ.indicator ⇑(f : Lp F p mu) =ᵐ[mu] 0 := by
    filter_upwards [hsupp (f : Lp F p mu) f.2] with x hx
    by_cases hxK : x ∈ (closedBall (0 : E) R)ᶜ
    · rw [Set.indicator_of_mem hxK, Pi.zero_apply, hx fun hxs => hxK (hR hxs)]
    · rw [Set.indicator_of_notMem hxK, Pi.zero_apply]
  rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  exact zero_le

/-- **Relative compactness in `Lᵖ` of a family vanishing almost everywhere off a fixed bounded
set** whose translation increments are uniformly small: the closure of such an `Lᵖ`-bounded
family is compact. This is the shape in which a compact embedding theorem is stated. -/
theorem isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    IsCompact (closure S) :=
  ((totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl hp' hs hsupp hM hbdd
    htrans).closure).isCompact_of_isClosed isClosed_closure

end FrechetKolmogorov

end TauCeti
