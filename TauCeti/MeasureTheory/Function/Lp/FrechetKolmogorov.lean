/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.BallAverage
public import TauCeti.Topology.MetricSpace.Equicontinuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

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
* it is **uniformly tight**: for every `ε > 0` there is a ball off which every `f ∈ S` has
  `Lᵖ` seminorm at most `ε`.

Neither of the last two hypotheses can be dropped. On `ℝ`, the concentrating family
`n ^ (1/p) 1_{[0, 1/n]}` is bounded and tight but has translation increments of size of order one
at every scale, and the escaping family `f(· - n)` of translates of a single nonzero `f` is
bounded and has a translation-invariant modulus but is not tight; neither is totally bounded. The
`Lᵖ` bound is carried explicitly, as in the classical statements.

The tightness hypothesis is automatic for a family supported in a fixed bounded set, which is the
form `TauCeti.totallyBounded_of_translation_of_support` records and the form that
Rellich--Kondrachov — Lane A.6 of `TauCetiRoadmap/PDE/README.md`, the compactness of
`W^{1,p}(Ω) ↪ L^p(Ω)` for bounded `Ω` — consumes: a `W^{1,p}_0(Ω)` function extended by zero
vanishes off `Ω`, and its translation increments are controlled by `‖h‖ ‖∇u‖_p` through
`TauCeti.W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient`.

## The proof

The two halves of the argument are already available. Smoothing is done by the **ball average**
`TauCeti.ballAverage`, whose four estimates are in
`TauCeti/MeasureTheory/Function/Lp/BallAverage.lean`: at a fixed scale `r` the ball averages of
the family are uniformly bounded (`TauCeti.enorm_ballAverage_le`), uniformly equicontinuous
(`TauCeti.enorm_ballAverage_add_sub_ballAverage_le`, packaged for a family here as
`TauCeti.uniformEquicontinuous_ballAverage`) and, once `r` is smaller than the translation modulus
of the family at `ε`, uniformly within `ε` of the family itself
(`TauCeti.eLpNorm_ballAverage_sub_le`). Compactness of that smoothed family is
Arzelà--Ascoli in the finite-net form `TauCeti.exists_finite_approx_of_uniformEquicontinuousOn`,
which returns finitely many *indices* whose ball averages approximate all the others uniformly on
a large closed ball `K`.

Putting the two together, `‖f - f'‖_p` for `f'` the chosen approximant is split as the `Lᵖ`
seminorm over `K` plus the one over its complement. Off `K` tightness bounds each of `f` and `f'`
separately; on `K` the difference is compared with the difference of the two ball averages, which
is uniformly at most `η` there, and `μ K ^ (1/p) η` is made small by the choice of `η`.

## Main declarations

* `TauCeti.uniformEquicontinuous_ballAverage`: the ball averages, at a fixed positive scale, of a
  family with uniformly small `Lᵖ` translation increments are uniformly equicontinuous.
* `TauCeti.totallyBounded_of_translation_of_tight`,
  `TauCeti.isCompact_closure_of_translation_of_tight`: the Fréchet--Kolmogorov criterion, in
  totally bounded and in relatively compact form.
* `TauCeti.totallyBounded_of_translation_of_support`,
  `TauCeti.isCompact_closure_of_translation_of_support`: the criterion for a family supported in
  a fixed bounded set, in totally bounded and in relatively compact form.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Theorem 4.26 and Corollary 4.27; H. Hanche-Olsen, H. Holden,
*The Kolmogorov--Riesz compactness theorem*, Expo. Math. 28 (2010).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

section FrechetKolmogorov

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ F] [Fact (1 ≤ p)] in
/-- At a fixed positive scale, the ball averages of a family of `Lᵖ` functions whose translation
increments are uniformly small in `Lᵖ` form a uniformly equicontinuous family. The scale enters
only through the volume factor `μ (ball 0 r) ^ (-1/p)`; the modulus of the ball averages is the
`Lᵖ` translation modulus of the family itself. -/
theorem uniformEquicontinuous_ballAverage {iota : Type*} {u : iota → E → F} {r : ℝ}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hu : ∀ i, MemLp (u i) p mu) (hr : 0 < r)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ i, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => u i (x + h) - u i x) p mu ≤ ε) :
    UniformEquicontinuous fun i => ballAverage mu r (u i) := by
  set V : ℝ≥0∞ := mu (ball (0 : E) r)
  have hV0 : V ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : V ≠ ∞ := measure_ball_lt_top.ne
  have hVinv : V ^ (p.toReal)⁻¹ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hV0) hVt).ne'
  have hVinvt : V ^ (p.toReal)⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hV0 hVt
  have hcancel : ∀ c : ℝ≥0∞, V ^ (-(p.toReal)⁻¹) * (c * V ^ (p.toReal)⁻¹) = c := fun c => by
    rw [ENNReal.rpow_neg, mul_comm c, ← mul_assoc, ENNReal.inv_mul_cancel hVinv hVinvt, one_mul]
  rw [Metric.uniformEquicontinuous_iff]
  intro c hc
  obtain ⟨δ, hδ, hδS⟩ := htrans (ENNReal.ofReal (c / 2) * V ^ (p.toReal)⁻¹)
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by linarith)).ne' hVinv)
  refine ⟨δ, hδ, fun x y hxy i => ?_⟩
  have hyx : ‖y - x‖ < δ := by rwa [← dist_eq_norm, dist_comm]
  have hbound := enorm_ballAverage_add_sub_ballAverage_le (mu := mu) (r := r) hp hp' (hu i) hr
    (y - x) x
  rw [add_sub_cancel] at hbound
  have hb2 := hbound.trans (mul_le_mul' (le_refl (V ^ (-(p.toReal)⁻¹))) (hδS i _ hyx))
  rw [hcancel] at hb2
  have hb3 : ‖ballAverage mu r (u i) y - ballAverage mu r (u i) x‖ ≤ c / 2 := by
    rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hb2
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  linarith

/-- **The Fréchet--Kolmogorov compactness criterion.** For `1 ≤ p < ∞`, a family `S` of `Lᵖ`
functions is totally bounded as soon as it is bounded in `Lᵖ`, its translation increments are
uniformly small in `Lᵖ`, and it is uniformly tight, i.e. every member has small `Lᵖ` seminorm off
one common closed ball.

Dropping either of the last two hypotheses breaks the conclusion: on `ℝ` the concentrating family
`n ^ (1/p) 1_{[0, 1/n]}` satisfies all but the smallness of translations, and the escaping family
`f(· - n)` of translates of a single nonzero `f` satisfies all but tightness, and neither is
totally bounded. -/
theorem totallyBounded_of_translation_of_tight (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)} {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ f ∈ S,
      eLpNorm ((closedBall (0 : E) R)ᶜ.indicator ⇑f) p mu ≤ ε) :
    TotallyBounded S := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hε₁ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 8) := ENNReal.ofReal_pos.2 (by linarith)
  set ε₁ : ℝ≥0∞ := ENNReal.ofReal (ε / 8)
  obtain ⟨r, hr, hrS⟩ := htrans ε₁ hε₁
  obtain ⟨R, hRS⟩ := htight ε₁ hε₁
  set K : Set E := closedBall (0 : E) R
  set V : ℝ≥0∞ := mu (ball (0 : E) r)
  have hV0 : V ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : V ≠ ∞ := measure_ball_lt_top.ne
  -- The uniform `L^∞` bound on the ball averages of the family.
  set Bₑ : ℝ≥0∞ := V ^ (-(p.toReal)⁻¹) * M
  have hBₑt : Bₑ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hV0 hVt) hM
  have hgB : ∀ i : S, ∀ x : E,
      ballAverage mu r ⇑(i : Lp F p mu) x ∈ closedBall (0 : F) Bₑ.toReal := by
    intro i x
    rw [mem_closedBall, dist_zero_right]
    have h := (enorm_ballAverage_le hp hp' (Lp.aestronglyMeasurable (i : Lp F p mu)) hr x).trans
      (mul_le_mul' (le_refl (V ^ (-(p.toReal)⁻¹))) (hbdd _ i.2))
    simpa using ENNReal.toReal_mono hBₑt h
  -- The uniform equicontinuity of the ball averages, at the fixed scale `r`.
  have hequi : UniformEquicontinuous fun i : S => ballAverage mu r ⇑(i : Lp F p mu) :=
    uniformEquicontinuous_ballAverage hp hp' (fun i => Lp.memLp (i : Lp F p mu)) hr
      fun c hc => by
        obtain ⟨δ, hδ, hδS⟩ := htrans c hc
        exact ⟨δ, hδ, fun i => hδS _ i.2⟩
  -- The scale of the uniform approximation on `K`, calibrated by the measure of `K`.
  have hmeasK : MeasurableSet K := measurableSet_closedBall
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
  -- Arzelà--Ascoli: finitely many members of the family approximate all of it uniformly on `K`.
  obtain ⟨t, htfin, ht⟩ := exists_finite_approx_of_uniformEquicontinuousOn
    (isCompact_closedBall (0 : E) R).totallyBounded
    (fun x _ => TotallyBounded.subset (Set.range_subset_iff.2 fun i => hgB i x)
      (isCompact_closedBall (0 : F) Bₑ.toReal).totallyBounded)
    (hequi.uniformEquicontinuousOn K) hη
  refine ⟨Subtype.val '' t, htfin.image _, fun f hf => ?_⟩
  obtain ⟨j, hjt, hj⟩ := ht ⟨f, hf⟩
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
  have hsmooth : ∀ g ∈ S, eLpNorm (ballAverage mu r ⇑g - ⇑g) p mu ≤ ε₁ := by
    intro g hg
    exact eLpNorm_ballAverage_sub_le hp hp' (Lp.memLp g) hr
      (fun e he => hrS g hg e (by simpa [dist_eq_norm] using he))
  have hmid : ∀ x ∈ K, dist (A x) (A' x) ≤ η := fun x hx => hj x hx
  -- The `Lᵖ` distance of `f` to the chosen approximant, split over `K` and its complement.
  have hsplit : (⇑f - ⇑f' : E → F) = K.indicator (⇑f - ⇑f') + Kᶜ.indicator (⇑f - ⇑f') :=
    (Set.indicator_self_add_compl K _).symm
  have htail : eLpNorm (Kᶜ.indicator (⇑f - ⇑f')) p mu ≤ ε₁ + ε₁ := by
    rw [Set.indicator_sub']
    exact (eLpNorm_sub_le (hfm.indicator hmeasK.compl) (hf'm.indicator hmeasK.compl) hp).trans
      (add_le_add (hRS f hf) (hRS f' j.2))
  have hnear : eLpNorm (K.indicator (⇑f - ⇑f')) p mu ≤
      ε₁ + (ENNReal.ofReal η * W + ε₁) := by
    have hdecomp : K.indicator (⇑f - ⇑f' : E → F) =
        K.indicator (⇑f - A) + (K.indicator (A - A') + K.indicator (A' - ⇑f')) := by
      rw [← Set.indicator_add', ← Set.indicator_add']
      congr 1
      abel
    rw [hdecomp]
    refine (eLpNorm_add_le ((hfm.sub hAm).indicator hmeasK)
      (((hAm.sub hA'm).indicator hmeasK).add ((hA'm.sub hf'm).indicator hmeasK)) hp).trans ?_
    refine add_le_add ?_ ((eLpNorm_add_le ((hAm.sub hA'm).indicator hmeasK)
      ((hA'm.sub hf'm).indicator hmeasK) hp).trans (add_le_add ?_ ?_))
    · refine (eLpNorm_indicator_le _).trans ?_
      rw [← neg_sub A (⇑f : E → F), eLpNorm_neg]
      exact hsmooth f hf
    · exact eLpNorm_indicator_sub_le_of_dist_bdd mu hp' hmeasK hη.le hmid
    · exact (eLpNorm_indicator_le _).trans (hsmooth f' j.2)
  have hmain : eLpNorm (⇑f - ⇑f') p mu ≤ ENNReal.ofReal (3 * ε / 4) := by
    calc eLpNorm (⇑f - ⇑f') p mu
        ≤ eLpNorm (K.indicator (⇑f - ⇑f')) p mu + eLpNorm (Kᶜ.indicator (⇑f - ⇑f')) p mu := by
          conv_lhs => rw [hsplit]
          exact eLpNorm_add_le ((hfm.sub hf'm).indicator hmeasK)
            ((hfm.sub hf'm).indicator hmeasK.compl) hp
      _ ≤ ε₁ + (ENNReal.ofReal η * W + ε₁) + (ε₁ + ε₁) := add_le_add hnear htail
      _ ≤ ENNReal.ofReal (ε / 8) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 8)) +
            (ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8)) := by
          gcongr
      _ = ENNReal.ofReal (3 * ε / 4) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith),
            ← ENNReal.ofReal_add (by linarith) (by linarith),
            ← ENNReal.ofReal_add (by linarith) (by linarith),
            ← ENNReal.ofReal_add (by linarith) (by linarith)]
          ring_nf
  rw [mem_ball, Lp.dist_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

/-- **Relative compactness in `Lᵖ` under the Fréchet--Kolmogorov hypotheses**: the closure of an
`Lᵖ`-bounded, uniformly tight family whose translation increments are uniformly small in `Lᵖ` is
compact. This is the relative-compactness form of
`TauCeti.totallyBounded_of_translation_of_tight`. -/
theorem isCompact_closure_of_translation_of_tight (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)} {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ f ∈ S,
      eLpNorm ((closedBall (0 : E) R)ᶜ.indicator ⇑f) p mu ≤ ε) :
    IsCompact (closure S) :=
  ((totallyBounded_of_translation_of_tight hp' hM hbdd htrans
    htight).closure).isCompact_of_isClosed isClosed_closure

/-- **The Fréchet--Kolmogorov criterion for a family supported in a fixed bounded set**, the form
the Rellich--Kondrachov theorem consumes: for functions vanishing off a bounded set the tightness
hypothesis is automatic, so an `Lᵖ`-bounded family whose translation increments are uniformly
small in `Lᵖ` is totally bounded. -/
theorem totallyBounded_of_translation_of_support (hp' : p ≠ ∞) {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    TotallyBounded S := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine totallyBounded_of_translation_of_tight hp' hM hbdd htrans fun ε _ => ⟨R, fun f hf => ?_⟩
  have h0 : (closedBall (0 : E) R)ᶜ.indicator ⇑f =ᵐ[mu] 0 := by
    filter_upwards [hsupp f hf] with x hx
    by_cases hxK : x ∈ (closedBall (0 : E) R)ᶜ
    · rw [Set.indicator_of_mem hxK, Pi.zero_apply, hx fun hxs => hxK (hR hxs)]
    · rw [Set.indicator_of_notMem hxK, Pi.zero_apply]
  rw [eLpNorm_congr_ae h0, eLpNorm_zero]
  exact zero_le

/-- **Relative compactness in `Lᵖ` of a family supported in a fixed bounded set** whose
translation increments are uniformly small: the closure of such an `Lᵖ`-bounded family is
compact. This is the shape in which a compact embedding theorem is stated. -/
theorem isCompact_closure_of_translation_of_support (hp' : p ≠ ∞) {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    IsCompact (closure S) :=
  ((totallyBounded_of_translation_of_support hp' hs hsupp hM hbdd
    htrans).closure).isCompact_of_isClosed isClosed_closure

end FrechetKolmogorov

end TauCeti
