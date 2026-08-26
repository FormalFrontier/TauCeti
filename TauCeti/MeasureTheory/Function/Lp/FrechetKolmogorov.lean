/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.BallAverage
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

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
form `TauCeti.totallyBounded_of_translation_of_isBounded_support` records. This is the form that
Rellich--Kondrachov for `W^{1,p}_0(Ω)` consumes: extending by zero makes a function vanish off `Ω`,
and its translation increments are controlled by `‖h‖ ‖∇u‖_p` through
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

* `TauCeti.totallyBounded_of_translation_of_tight`,
  `TauCeti.isCompact_closure_of_translation_of_tight`: the Fréchet--Kolmogorov criterion, in
  totally bounded and in relatively compact form.
* `TauCeti.totallyBounded_of_translation_of_isBounded_support`,
  `TauCeti.isCompact_closure_of_translation_of_isBounded_support`: the criterion for a family
  supported in a fixed bounded set, in totally bounded and in relatively compact form.

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

section LpApproximation

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {mu : Measure α} {p : ℝ≥0∞}

/-- An `Lᵖ` comparison estimate obtained by approximating two functions uniformly on a measurable
set and controlling their tails off that set. This is the three-term-plus-tail estimate used in
the Fréchet--Kolmogorov argument. -/
theorem eLpNorm_sub_le_of_dist_bdd_of_eLpNorm_indicator_compl_le {K : Set α}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hK : MeasurableSet K) {f f' A A' : α → F} {a b : ℝ≥0∞} {η : ℝ}
    (hf : AEStronglyMeasurable f mu) (hf' : AEStronglyMeasurable f' mu)
    (hA : AEStronglyMeasurable A mu) (hA' : AEStronglyMeasurable A' mu)
    (hη : 0 ≤ η) (hAf : eLpNorm (A - f) p mu ≤ a)
    (hA'f' : eLpNorm (A' - f') p mu ≤ a)
    (hmid : ∀ x ∈ K, dist (A x) (A' x) ≤ η)
    (htail : eLpNorm (Kᶜ.indicator f) p mu ≤ b)
    (htail' : eLpNorm (Kᶜ.indicator f') p mu ≤ b) :
    eLpNorm (f - f') p mu ≤
      a + (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + a) + (b + b) := by
  have hsplit : (f - f' : α → F) = K.indicator (f - f') + Kᶜ.indicator (f - f') :=
    (Set.indicator_self_add_compl K _).symm
  have htail_sub : eLpNorm (Kᶜ.indicator (f - f')) p mu ≤ b + b := by
    rw [Set.indicator_sub']
    exact (eLpNorm_sub_le (hf.indicator hK.compl) (hf'.indicator hK.compl) hp).trans
      (add_le_add htail htail')
  have hnear : eLpNorm (K.indicator (f - f')) p mu ≤
      a + (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + a) := by
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
      exact hAf
    · exact eLpNorm_indicator_sub_le_of_dist_bdd mu hp' hK hη hmid
    · exact (eLpNorm_indicator_le _).trans hA'f'
  calc
    eLpNorm (f - f') p mu
        ≤ eLpNorm (K.indicator (f - f')) p mu + eLpNorm (Kᶜ.indicator (f - f')) p mu := by
          conv_lhs => rw [hsplit]
          exact eLpNorm_add_le ((hf.sub hf').indicator hK) ((hf.sub hf').indicator hK.compl) hp
    _ ≤ a + (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + a) + (b + b) :=
      add_le_add hnear htail_sub

end LpApproximation

section FrechetKolmogorov

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

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
  -- The uniform `L^∞` bound on the ball averages of the family.
  set Bₑ : ℝ≥0∞ := V ^ (-(p.toReal)⁻¹) * M
  have hgB : ∀ i : S, ∀ x : E,
      ballAverage mu r ⇑(i : Lp F p mu) x ∈ closedBall (0 : F) Bₑ.toReal := fun i x => by
    simpa only [Bₑ, V] using ballAverage_mem_closedBall_of_eLpNorm_le hp hp'
      (Lp.aestronglyMeasurable (i : Lp F p mu)) hr hM (hbdd _ i.2) x
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
  -- Arzelà--Ascoli on the restricted ball averages, bundled as bounded continuous functions.
  let _ : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let φ : S → BoundedContinuousFunction K F := fun i =>
    BoundedContinuousFunction.mkOfCompact
    ⟨fun x : K => ballAverage mu r ⇑(i : Lp F p mu) (x : E),
      (continuous_ballAverage hp hp' (Lp.memLp (i : Lp F p mu)) hr).comp continuous_subtype_val⟩
  let 𝒜 : Set (BoundedContinuousFunction K F) := Set.range φ
  have hφequi : Equicontinuous fun i : S => (φ i : K → F) := by
    change Equicontinuous (K.domRestrict ∘
      fun i : S => ballAverage mu r ⇑(i : Lp F p mu))
    exact (equicontinuous_restrict_iff _).2 (hequi.equicontinuous.equicontinuousOn K)
  have hAequi : Equicontinuous ((↑) : 𝒜 → K → F) := by
    rw [← Set.comp_rangeSplitting φ]
    exact hφequi.comp (Set.rangeSplitting φ)
  have hAcompact : IsCompact (closure 𝒜) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) Bₑ.toReal)
      (isCompact_closedBall _ _) 𝒜 (by
        intro q x hq
        obtain ⟨i, rfl⟩ := hq
        simpa only [φ, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
          hgB i x) hAequi
  have hAtb : TotallyBounded 𝒜 := hAcompact.totallyBounded.subset subset_closure
  obtain ⟨t, htA, htfin, htcover⟩ := hAtb.exists_subset (dist_mem_uniformity hη)
  -- Choose an original family index representing each member of the finite net `t`.
  let _ : Finite t := htfin.to_subtype
  choose idx hidx using fun q : t => htA q.2
  -- The representatives of `t` give the required finite subset of the original family `S`.
  refine ⟨Subtype.val '' Set.range idx, Set.finite_range idx |>.image _, fun f hf => ?_⟩
  -- Use the Arzelà--Ascoli cover to choose a net point close to the ball average of `f`.
  obtain ⟨q, hqt, hfq⟩ : ∃ q ∈ t, dist (φ ⟨f, hf⟩) q < η := by
    simpa only [mem_iUnion, mem_ofPred_eq, exists_prop] using
      htcover (Set.mem_range_self ⟨f, hf⟩)
  let q' : t := ⟨q, hqt⟩
  let j : S := idx q'
  have hφdist : dist (φ ⟨f, hf⟩) (φ j) < η := by
    rw [hidx q']
    exact hfq
  -- Pull its representative index back to the finite subset of `S` constructed above.
  refine mem_iUnion₂.2 ⟨(j : Lp F p mu), ⟨j, ⟨q', rfl⟩, rfl⟩, ?_⟩
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
  have hmid : ∀ x ∈ K, dist (A x) (A' x) ≤ η := by
    intro x hx
    simpa only [A, A', f', φ, BoundedContinuousFunction.mkOfCompact_apply,
      ContinuousMap.coe_mk] using
        (BoundedContinuousFunction.dist_coe_le_dist (f := φ ⟨f, hf⟩) (g := φ j) ⟨x, hx⟩).trans
          hφdist.le
  have hmain : eLpNorm (⇑f - ⇑f') p mu ≤ ENNReal.ofReal (3 * ε / 4) := by
    calc eLpNorm (⇑f - ⇑f') p mu
        ≤ ε₁ + (ENNReal.ofReal η * W + ε₁) + (ε₁ + ε₁) := by
          exact eLpNorm_sub_le_of_dist_bdd_of_eLpNorm_indicator_compl_le hp hp' hmeasK hfm hf'm
            hAm hA'm hη.le (hsmooth f hf) (hsmooth f' j.2) hmid (hRS f hf) (hRS f' j.2)
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
that Rellich--Kondrachov for `W^{1,p}_0(Ω)` consumes. For functions vanishing off a bounded set the
tightness hypothesis is automatic, so an `Lᵖ`-bounded family whose translation increments are
uniformly small in `Lᵖ` is totally bounded. -/
theorem totallyBounded_of_translation_of_isBounded_support (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)}
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
theorem isCompact_closure_of_translation_of_isBounded_support (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    IsCompact (closure S) :=
  ((totallyBounded_of_translation_of_isBounded_support hp' hs hsupp hM hbdd
    htrans).closure).isCompact_of_isClosed isClosed_closure

end FrechetKolmogorov

end TauCeti
