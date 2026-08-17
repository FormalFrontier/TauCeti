/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Semicontinuity.Defs
-- `TauCeti.MeasureTheory.Integral.Marcinkiewicz` is imported privately: its operator-level
-- interpolation API is used only to prove the strong maximal inequality below.
import TauCeti.MeasureTheory.Integral.Marcinkiewicz
-- `Mathlib.MeasureTheory.Constructions.BorelSpace.Order` is imported privately: it is used only
-- for `LowerSemicontinuous.measurable`, inside the proof of `TauCeti.measurable_maximalFunction`.
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
-- `Mathlib.MeasureTheory.Covering.Vitali` is imported privately: the covering lemma appears only
-- inside the proof of `TauCeti.mul_measure_le_of_forall_exists_ball`.
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The Hardy–Littlewood maximal function

The **centred Hardy–Littlewood maximal function** of `f` is

`M f x = ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ`,

the largest average of `‖f‖` over a ball centred at `x`. This file defines it, records the two
endpoint bounds it satisfies, and proves the **maximal inequality** in both of its forms: the weak
type `(1,1)` bound

`t * μ {x | t < M f x} ≤ 4 ^ n * ∫⁻ x, ‖f x‖ₑ ∂μ`

and, for `1 < p < ∞`, the strong type `(p, p)` bound `‖M f‖_p ≤ C(n, p) * ‖f‖_p`, for `μ` an
additive Haar measure on a real normed space of finite dimension `n`.

The maximal inequality is the first item of Lane B of the PDE roadmap, the estimate that drives
the Calderón–Zygmund theory and, through it, the `Lᵖ` regularity theory for elliptic equations.
It is also where the classical *asymmetric* pair of endpoints originates: `M` is bounded on `L^∞`
(`TauCeti.maximalFunction_le_eLpNormEssSup`) but, in positive dimension, not on `L¹` — a failure
not formalised here — so the correct `L¹` statement is the weak-type bound, and the strong `(p, p)`
bounds are obtained from those two ends by Marcinkiewicz interpolation. The qualification matters:
the `L¹` failure is a positive-dimensional phenomenon, since in dimension `0` every ball is the
whole space and the averages defining `M f` collapse to `‖f‖ₑ`.

## The proof

The weak-type bound is the Vitali covering argument, isolated here as
`TauCeti.mul_measure_le_of_forall_exists_ball`: if every point of a set `S` is the centre of a ball
of radius at most `R` on which `∫⁻ g` is at least `t` times the measure of the ball, then
`t * μ S ≤ 4 ^ n * ∫⁻ g`. Mathlib's
`Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` extracts a pairwise disjoint
subfamily of those balls whose fourfold enlargements still cover `S`; the enlargement costs the
factor `4 ^ n` because a Haar measure scales a ball of radius `r` by `r ^ n`, and disjointness turns
the sum of the integrals over the selected balls into a single integral over their union.

Applying this to `S = {x | t < M f x}` needs a uniform bound on the radii it selects, and that is
where finiteness of `∫⁻ ‖f‖ₑ` enters: a ball whose average exceeds `t` has measure less than
`∫⁻ ‖f‖ₑ / t`, which in positive dimension bounds its radius. In dimension `0` it does not — every
ball is the whole space — and that degenerate case is proved separately.

The strong type `(p, p)` bound then comes from
`TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`, the operator-level diagonal
case of Marcinkiewicz interpolation. That theorem performs the reusable split at height `c * t`.
Here `c = d = 2⁻¹`, so the low part is bounded by `t / 2`, its maximal function never reaches
`t`, and the weak-type bound applied to the high part gives
`t * μ {M f > t} ≤ 2 * 4 ^ n * ∫⁻ x in {‖f‖ₑ > t / 2}, ‖f x‖ₑ ∂μ`.

## Main declarations

* `TauCeti.maximalFunction`: the centred Hardy–Littlewood maximal function, with
  `TauCeti.setLAverage_le_maximalFunction`, `TauCeti.maximalFunction_le` and
  `TauCeti.lt_maximalFunction_iff` as its interface.
* `TauCeti.maximalFunction_const`: the maximal function of a constant is that constant, so the
  normalisation is the intended one.
* `TauCeti.maximalFunction_mono_ae`, `TauCeti.maximalFunction_congr_ae`: `M` is monotone in `‖f‖ₑ`
  almost everywhere, so `M f` depends on `f` only through `‖f‖ₑ` and only up to a null set.
* `TauCeti.maximalFunction_enorm`: replacing a function by its extended norm leaves its maximal
  function unchanged.
* `TauCeti.maximalFunction_zero`, `TauCeti.maximalFunction_add_le`,
  `TauCeti.maximalFunction_const_smul`: `M` is sublinear. Subadditivity and the endpoint bounds
  feed directly into `TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`.
* `TauCeti.maximalFunction_le_eLpNormEssSup`: the `L^∞` endpoint.
* `TauCeti.lowerSemicontinuous_maximalFunction`, `TauCeti.measurable_maximalFunction`: the
  superlevel sets `{x | t < M f x}` are open, so `M f` is Borel measurable.
* `TauCeti.mul_measure_le_of_forall_exists_ball`: the Vitali covering estimate.
* `TauCeti.mul_measure_lt_maximalFunction_le`, `TauCeti.measure_lt_maximalFunction_le`: the
  **maximal inequality**, in product and in quotient form.
* `TauCeti.ae_maximalFunction_lt_top`: the maximal function of an `L¹` function is finite almost
  everywhere.
* `TauCeti.lintegral_rpow_maximalFunction_le`, `TauCeti.eLpNorm_maximalFunction_le`: the
  **strong type `(p, p)` maximal inequality** for `1 < p < ∞`, with an explicit constant.
* `TauCeti.eLpNorm_maximalFunction_lt_top`,
  `TauCeti.ae_maximalFunction_lt_top_of_eLpNorm_ne_top`: a function with finite `Lᵖ` seminorm
  has a maximal function with finite `Lᵖ` seminorm for `1 < p ≤ ∞`, and the maximal function
  is finite almost everywhere for every `1 ≤ p ≤ ∞`.

The maximal function defined here is the *centred* one, whose averages are over the balls centred
at the point. The uncentred variant, over all balls containing the point, is comparable to it with
a dimensional constant and is not needed downstream.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal Topology

section PseudoMetricSpace

variable {X F F' : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [ENorm F] [ENorm F']

/-- The **centred Hardy–Littlewood maximal function** of `f` with respect to `μ`: the supremum
over the radii `r > 0` of the average of `‖f‖ₑ` over the ball of radius `r` centred at `x`.

The averages are taken in `ℝ≥0∞`, so this is defined for every `f`, taking the value `∞` at the
points where the averages are unbounded. -/
noncomputable def maximalFunction (μ : Measure X) (f : X → F) (x : X) : ℝ≥0∞ :=
  ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ

variable {μ : Measure X} {f : X → F} {g : X → F'} {x : X} {r : ℝ} {a t : ℝ≥0∞}

theorem maximalFunction_def (μ : Measure X) (f : X → F) (x : X) :
    maximalFunction μ f x = ⨆ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ := (rfl)

/-- Every ball average is at most the maximal function: the introduction rule. -/
theorem setLAverage_le_maximalFunction (μ : Measure X) (f : X → F) (x : X) (hr : 0 < r) :
    ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ maximalFunction μ f x := by
  rw [maximalFunction_def]
  exact le_iSup₂ (f := fun r (_ : 0 < r) => ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ) r hr

/-- A bound holding for every ball average bounds the maximal function: the elimination rule. -/
theorem maximalFunction_le (h : ∀ r > 0, ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ a) :
    maximalFunction μ f x ≤ a := by
  rw [maximalFunction_def]
  exact iSup₂_le h

/-- The maximal function exceeds `t` exactly when some ball average does. -/
theorem lt_maximalFunction_iff :
    t < maximalFunction μ f x ↔ ∃ r > 0, t < ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
  rw [maximalFunction_def]
  simp only [lt_iSup_iff, exists_prop]

/-- If `‖f‖ₑ ≤ ‖g‖ₑ` almost everywhere, then `M f ≤ M g`. -/
theorem maximalFunction_mono_ae (h : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ ‖g y‖ₑ) :
    maximalFunction μ f x ≤ maximalFunction μ g x :=
  maximalFunction_le fun _ hr =>
    (setLAverage_mono_ae _ h).trans (setLAverage_le_maximalFunction μ g x hr)

/-- Functions whose norms agree almost everywhere have the same maximal function. -/
theorem maximalFunction_congr_ae (h : ∀ᵐ y ∂μ, ‖f y‖ₑ = ‖g y‖ₑ) :
    maximalFunction μ f x = maximalFunction μ g x :=
  le_antisymm (maximalFunction_mono_ae (h.mono fun _ hy => hy.le))
    (maximalFunction_mono_ae (h.mono fun _ hy => hy.ge))

/-- Replacing a function by its extended norm leaves its maximal function unchanged. -/
@[simp]
theorem maximalFunction_enorm (μ : Measure X) (f : X → F) :
    maximalFunction μ (fun x => ‖f x‖ₑ) = maximalFunction μ f :=
  funext fun _ => maximalFunction_congr_ae (.of_forall fun _ => by simp)

/-- The `L^∞` endpoint of the maximal inequality: the maximal function of `f` is bounded by the
essential supremum of `‖f‖`, with constant `1`. -/
theorem maximalFunction_le_eLpNormEssSup (μ : Measure X) (f : X → F) (x : X) :
    maximalFunction μ f x ≤ eLpNormEssSup f μ := by
  rw [eLpNormEssSup_eq_essSup_enorm]
  exact maximalFunction_le fun r _ => setLAverage_le_essSup _ _

/-- The maximal function of a constant is that constant: the averages defining it are normalised,
so no factor of the measure of a ball is left behind. -/
@[simp]
theorem maximalFunction_const [ProperSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (c : F) (x : X) :
    maximalFunction μ (fun _ => c) x = ‖c‖ₑ := by
  have key : ∀ r : ℝ, 0 < r → ⨍⁻ _y in ball x r, ‖c‖ₑ ∂μ = ‖c‖ₑ := fun r hr =>
    setLAverage_const (measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne ‖c‖ₑ
  refine le_antisymm (maximalFunction_le fun r hr => (key r hr).le) ?_
  exact (key 1 one_pos).ge.trans (setLAverage_le_maximalFunction μ _ x one_pos)

section Sublinear

omit [PseudoMetricSpace X] in
/-- Pulling a finite constant out of a set average. -/
private theorem setLAverage_const_mul (μ : Measure X) (s : Set X) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : X → ℝ≥0∞) : ⨍⁻ y in s, c * h y ∂μ = c * ⨍⁻ y in s, h y ∂μ := by
  rw [setLAverage_eq, setLAverage_eq, lintegral_const_mul' _ _ hc, mul_div_assoc]

/-- The maximal function is positively homogeneous: scaling `f` by `c` scales `M f` by `‖c‖ₑ`.
This is the first half of the sublinearity of `M`, the second being
`TauCeti.maximalFunction_add_le`. -/
@[simp]
theorem maximalFunction_const_smul {𝕜 : Type*} [NNNorm 𝕜] [SMul 𝕜 F] [ENormSMulClass 𝕜 F]
    (μ : Measure X) (c : 𝕜) (f : X → F) (x : X) :
    maximalFunction μ (c • f) x = ‖c‖ₑ * maximalFunction μ f x := by
  rw [maximalFunction_def, maximalFunction_def]
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]
  exact iSup_congr fun r =>
    iSup_congr fun _ => setLAverage_const_mul μ _ enorm_ne_top fun y => ‖f y‖ₑ

variable {G : Type*} [TopologicalSpace G] [ESeminormedAddMonoid G] {f g : X → G}

/-- The maximal function of the zero function is zero. -/
@[simp]
theorem maximalFunction_zero (μ : Measure X) (x : X) : maximalFunction μ (0 : X → G) x = 0 := by
  simp [maximalFunction_def]

/-- The maximal function is subadditive, the second half of that sublinearity. Only the norm of the
first summand need be measurable. -/
theorem maximalFunction_add_le (hf : AEMeasurable (fun y => ‖f y‖ₑ) μ) (x : X) :
    maximalFunction μ (f + g) x ≤ maximalFunction μ f x + maximalFunction μ g x := by
  refine maximalFunction_le fun r hr => ?_
  calc ⨍⁻ y in ball x r, ‖(f + g) y‖ₑ ∂μ
      ≤ ⨍⁻ y in ball x r, (‖f y‖ₑ + ‖g y‖ₑ) ∂μ :=
        setLAverage_mono_ae _ (.of_forall fun y => enorm_add_le (f y) (g y))
    _ = ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ + ⨍⁻ y in ball x r, ‖g y‖ₑ ∂μ := by
        rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_left' hf.restrict,
          ENNReal.add_div]
    _ ≤ maximalFunction μ f x + maximalFunction μ g x :=
        add_le_add (setLAverage_le_maximalFunction μ f x hr)
          (setLAverage_le_maximalFunction μ g x hr)

end Sublinear

end PseudoMetricSpace

section Haar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [ENorm F] {μ : Measure E} [μ.IsAddHaarMeasure] {t : ℝ≥0∞}

/-- Enlarging a ball by the factor `4` multiplies its measure by `4 ^ n`: the dimensional cost of
the Vitali enlargement. -/
private theorem addHaar_closedBall_four_mul (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) {r : ℝ}
    (hr : 0 < r) : μ (closedBall x (4 * r)) = 4 ^ finrank ℝ E * μ (ball x r) := by
  rw [Measure.addHaar_closedBall μ x (by linarith : (0 : ℝ) ≤ 4 * r),
    Measure.addHaar_ball_of_pos μ x hr, ← mul_assoc, mul_pow,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ finrank ℝ E),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- **The Vitali covering estimate.** If every point of `S` is the centre of a ball of radius at
most `R` on which `∫⁻ g` is at least `t` times the measure of the ball, then
`t * μ S ≤ 4 ^ n * ∫⁻ g`, with `n` the dimension of the space.

The factor `4 ^ n` is the cost of passing from a pairwise disjoint subfamily of those balls to its
fourfold enlargement, which still covers `S`. -/
theorem mul_measure_le_of_forall_exists_ball {S : Set E} {R : ℝ} {g : E → ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc 0 R, t * μ (ball x r) ≤ ∫⁻ y in ball x r, g y ∂μ) :
    t * μ S ≤ 4 ^ finrank ℝ E * ∫⁻ y, g y ∂μ := by
  choose! r hr hle using hS
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun x hx =>
      ⟨x, ball_subset_interior_closedBall (mem_ball_self (hr x (hu hx)).1)⟩
  have : Countable u := hcount.to_subtype
  -- The fourfold enlargements of the selected balls cover `S`.
  have hsub : S ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := fun x hx => by
    obtain ⟨b, hb, hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_closedBall_self (hr x hx).1.le))
  -- The selected balls are pairwise disjoint, so the integrals over them add up to at most `∫⁻ g`.
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => ball (b : E) (r b)) :=
    fun b b' hbb' =>
      (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')).mono ball_subset_closedBall
        ball_subset_closedBall
  calc t * μ S
      ≤ t * ∑' b : u, μ (closedBall (b : E) (4 * r b)) := by
        gcongr
        exact (measure_mono hsub).trans (measure_biUnion_le μ hcount _)
    _ = ∑' b : u, t * μ (closedBall (b : E) (4 * r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, 4 ^ finrank ℝ E * ∫⁻ y in ball (b : E) (r b), g y ∂μ := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [addHaar_closedBall_four_mul μ _ (hr b (hu b.2)).1, mul_left_comm]
        gcongr
        exact hle b (hu b.2)
    _ = 4 ^ finrank ℝ E * ∑' b : u, ∫⁻ y in ball (b : E) (r b), g y ∂μ := ENNReal.tsum_mul_left
    _ = 4 ^ finrank ℝ E * ∫⁻ y in ⋃ b : u, ball (b : E) (r b), g y ∂μ := by
        rw [lintegral_iUnion (fun b => measurableSet_ball) hdisj']
    _ ≤ 4 ^ finrank ℝ E * ∫⁻ y, g y ∂μ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- The superlevel sets of the maximal function are open: enlarging the radius slightly keeps the
average of `‖f‖ₑ` above `t`, at every nearby centre. -/
theorem lowerSemicontinuous_maximalFunction (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) :
    LowerSemicontinuous (maximalFunction μ f) := by
  intro x t ht
  obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp ht
  have hc₀ : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hc_top : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hpos : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1) ≠ 0 := fun s hs =>
    mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hs _)).ne' hc₀
  have hne : ∀ s : ℝ, ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1) ≠ ∞ := fun _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc_top
  rw [setLAverage_eq] at hlt
  have hmul : t * (ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball (0 : E) 1)) <
      ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
    rw [← Measure.addHaar_ball_of_pos μ x hr]
    exact ENNReal.mul_lt_of_lt_div hlt
  -- A slightly larger radius still works, by continuity of `s ↦ t * (s ^ n * μ (ball 0 1))`.
  have hcont : Tendsto
      (fun s : ℝ => t * (ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1))) (𝓝 r)
      (𝓝 (t * (ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball (0 : E) 1)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow _).tendsto r)) (.inr hc_top))
      (.inl (hpos r hr))
  have hev : ∀ᶠ s : ℝ in 𝓝[>] r,
      t * (ENNReal.ofReal (s ^ finrank ℝ E) * μ (ball (0 : E) 1)) <
        ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually_lt_const hmul
  obtain ⟨s, hs, hrs⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrs' : r < s := hrs
  have hs_pos : 0 < s := hr.trans hrs'
  -- Every centre within `s - r` of `x` then has a ball average exceeding `t`.
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrs')] with y hy
  refine lt_of_lt_of_le ?_ (setLAverage_le_maximalFunction μ f y hs_pos)
  rw [setLAverage_eq, Measure.addHaar_ball_of_pos μ y hs_pos,
    ENNReal.lt_div_iff_mul_lt (.inl (hpos s hs_pos)) (.inl (hne s))]
  refine hs.trans_le (lintegral_mono_set (ball_subset_ball' ?_))
  rw [dist_comm]
  linarith [mem_ball.mp hy]

/-- The maximal function is Borel measurable, being lower semicontinuous. No hypothesis on `f` is
needed: the supremum defining `M f` is over balls, not over values of `f`. -/
@[fun_prop]
theorem measurable_maximalFunction (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) :
    Measurable (maximalFunction μ f) :=
  (lowerSemicontinuous_maximalFunction μ f).measurable

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The maximal inequality in the degenerate case of a `0`-dimensional space, where every ball is
the whole space and the radii carry no information. -/
private theorem mul_measure_lt_maximalFunction_le_of_subsingleton [Subsingleton E] (μ : Measure E)
     (f : E → F) (t : ℝ≥0∞) :
    t * μ {x | t < maximalFunction μ f x} ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rcases eq_empty_or_nonempty {x | t < maximalFunction μ f x} with hS | ⟨x, hx⟩
  · simp [hS]
  obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp hx
  have hball : ball x r = univ :=
    eq_univ_of_forall fun y => by simpa [Subsingleton.elim y x] using hr
  rw [setLAverage_eq, hball, Measure.restrict_univ] at hlt
  calc t * μ {x | t < maximalFunction μ f x}
      ≤ t * μ univ := by gcongr; exact subset_univ _
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := (ENNReal.mul_lt_of_lt_div hlt).le
    _ ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
        simpa using mul_le_mul_left (one_le_pow₀ (a := (4 : ℝ≥0∞)) (by norm_num)
          (n := finrank ℝ E)) (∫⁻ x, ‖f x‖ₑ ∂μ)

/-- **The Hardy–Littlewood maximal inequality**, the weak-type `(1,1)` bound: the measure of the
set where the maximal function exceeds `t`, multiplied by `t`, is at most `4 ^ n` times the `L¹`
norm of `f`, with `n` the dimension of the space.

No integrability hypothesis is needed: the bound is vacuous when `∫⁻ x, ‖f x‖ₑ ∂μ = ∞`. -/
theorem mul_measure_lt_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (t : ℝ≥0∞) :
    t * μ {x | t < maximalFunction μ f x} ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rcases eq_or_ne (∫⁻ x, ‖f x‖ₑ ∂μ) ∞ with hI | hI
  · rw [hI, ENNReal.mul_top (pow_ne_zero _ (by norm_num))]
    exact le_top
  rcases eq_or_ne t 0 with rfl | ht₀
  · simp
  rcases eq_or_ne t ∞ with rfl | ht_top
  · -- the superlevel set at `∞` is empty
    simp
  rcases subsingleton_or_nontrivial E with _ | _
  · exact mul_measure_lt_maximalFunction_le_of_subsingleton μ f t
  have hc₀ : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hc_top : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have htc₀ : t * μ (ball (0 : E) 1) ≠ 0 := mul_ne_zero ht₀ hc₀
  have htc_top : t * μ (ball (0 : E) 1) ≠ ∞ := ENNReal.mul_ne_top ht_top hc_top
  -- Every point of the superlevel set is the centre of a ball whose average exceeds `t`.
  have hex : ∀ x ∈ {x | t < maximalFunction μ f x},
      ∃ r : ℝ, 0 < r ∧ t * μ (ball x r) < ∫⁻ y in ball x r, ‖f y‖ₑ ∂μ := by
    intro x hx
    obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.mp hx
    rw [setLAverage_eq] at hlt
    exact ⟨r, hr, ENNReal.mul_lt_of_lt_div hlt⟩
  choose! r hr₀ hrlt using hex
  -- Those radii are bounded, because `∫⁻ ‖f‖ₑ ∂μ` is finite and the dimension is positive.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ {x | t < maximalFunction μ f x}, r x ∈ Ioc 0 R := by
    refine ⟨max 1 ((∫⁻ x, ‖f x‖ₑ ∂μ) / (t * μ (ball (0 : E) 1))).toReal,
      fun x hx => ⟨hr₀ x hx, ?_⟩⟩
    have hlt : ENNReal.ofReal (r x ^ finrank ℝ E) * (t * μ (ball (0 : E) 1)) <
        ∫⁻ y, ‖f y‖ₑ ∂μ := by
      rw [mul_left_comm, ← Measure.addHaar_ball_of_pos μ x (hr₀ x hx)]
      exact (hrlt x hx).trans_le (setLIntegral_le_lintegral _ _)
    rw [← ENNReal.lt_div_iff_mul_lt (.inl htc₀) (.inl htc_top),
      ENNReal.ofReal_lt_iff_lt_toReal (pow_nonneg (hr₀ x hx).le _)
        (ENNReal.div_ne_top hI htc₀)] at hlt
    by_contra! hcon
    have h₁ : (1 : ℝ) ≤ r x := le_trans (le_max_left _ _) hcon.le
    have h₂ : r x ≤ r x ^ finrank ℝ E := le_self_pow₀ h₁ Module.finrank_pos.ne'
    linarith [le_max_right (1 : ℝ) ((∫⁻ x, ‖f x‖ₑ ∂μ) / (t * μ (ball (0 : E) 1))).toReal]
  exact mul_measure_le_of_forall_exists_ball fun x hx => ⟨r x, hR x hx, (hrlt x hx).le⟩

/-- **The Hardy–Littlewood maximal inequality**, in quotient form. -/
theorem measure_lt_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (ht : t ≠ 0) :
    μ {x | t < maximalFunction μ f x} ≤ 4 ^ finrank ℝ E * (∫⁻ x, ‖f x‖ₑ ∂μ) / t := by
  rcases eq_or_ne t ∞ with rfl | ht_top
  · -- the superlevel set at `∞` is empty
    simp
  refine (ENNReal.le_div_iff_mul_le (.inl ht) (.inl ht_top)).2 ?_
  rw [mul_comm]
  exact mul_measure_lt_maximalFunction_le μ f t

/-- The maximal function of an `L¹` function is finite almost everywhere: the maximal inequality
with `t → ∞`. -/
theorem ae_maximalFunction_lt_top (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F)
    (hf : ∫⁻ x, ‖f x‖ₑ ∂μ ≠ ∞) : ∀ᵐ x ∂μ, maximalFunction μ f x < ∞ := by
  have hC : 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hf
  have hsub : ∀ t : ℝ≥0∞, t ≠ ∞ →
      t * μ {x | maximalFunction μ f x = ∞} ≤ 4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ := by
    refine fun t ht => le_trans (mul_le_mul_right (measure_mono
      fun x (hx : maximalFunction μ f x = ∞) => lt_of_lt_of_le (lt_top_iff_ne_top.2 ht) hx.ge) t)
      (mul_measure_lt_maximalFunction_le μ f t)
  have hm : μ {x | maximalFunction μ f x = ∞} = 0 := by
    by_contra hm'
    rcases eq_or_ne (μ {x | maximalFunction μ f x = ∞}) ∞ with hm_top | hm_top
    · exact hC (top_le_iff.1 (by simpa [hm_top] using hsub 1 ENNReal.one_ne_top))
    · have hle := hsub ((4 ^ finrank ℝ E * ∫⁻ x, ‖f x‖ₑ ∂μ + 1) /
        μ {x | maximalFunction μ f x = ∞}) (ENNReal.div_ne_top (by simp [hC]) hm')
      rw [ENNReal.div_mul_cancel hm' hm_top] at hle
      exact absurd hle (not_le.2 (ENNReal.lt_add_right hC one_ne_zero))
  rw [ae_iff]
  simpa only [not_lt, top_le_iff] using hm

section StrongType

/-- **The Hardy–Littlewood maximal inequality**, the strong-type `(p, p)` bound for `1 < p < ∞`,
as an inequality between the integrals `∫⁻ ‖·‖ₑ ^ p`:

`∫⁻ (M f) ^ p ∂μ ≤ (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ n * ∫⁻ ‖f‖ₑ ^ p ∂μ`.

The constant degenerates as `p → 1`, as it must in positive dimension, where `M` is not bounded on
`L¹`. -/
theorem lintegral_rpow_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F}
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, maximalFunction μ f x ^ p ∂μ ≤
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ finrank ℝ E *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hconst : ENNReal.ofReal (p * (2 : ℝ)⁻¹ ^ (1 - p) / (p - 1)) * (2 * 4 ^ finrank ℝ E) =
      ENNReal.ofReal (2 * p * 2 ^ (p - 1) / (p - 1)) * 4 ^ finrank ℝ E := by
    have hinv : ((2 : ℝ))⁻¹ ^ (1 - p) = 2 ^ (p - 1) := by
      rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub]
    have hsplit : 2 * p * 2 ^ (p - 1) / (p - 1) = 2 * (p * 2 ^ (p - 1) / (p - 1)) := by ring
    rw [hinv, hsplit, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  rw [← hconst]
  rw [← maximalFunction_enorm μ f]
  simpa only [inv_inv, ENNReal.ofReal_ofNat, enorm_eq_self] using
    lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
      (T := fun g => maximalFunction μ g) (A := 4 ^ finrank ℝ E) (b := 1)
      (c := 2⁻¹) (d := 2⁻¹) hf
      (measurable_maximalFunction μ fun x => ‖f x‖ₑ).aemeasurable hp
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun g h hg _hh => .of_forall fun y => maximalFunction_add_le
        (by simpa only [enorm_eq_self] using hg) y)
      (fun g _hg s => by
        simpa only [enorm_eq_self] using mul_measure_lt_maximalFunction_le μ g s)
      (fun (g : E → ℝ≥0∞) (_hg : AEMeasurable g μ) =>
        .of_forall fun y : E => by simpa only [ENNReal.ofReal_one, one_mul] using
          maximalFunction_le_eLpNormEssSup μ g y)

/-- **The Hardy–Littlewood maximal inequality**, the strong-type `(p, p)` bound for `1 < p < ∞`,
in terms of representative-level `Lᵖ` seminorms.

Together with `TauCeti.maximalFunction_le_eLpNormEssSup` (the case `p = ∞`) and
`TauCeti.mul_measure_lt_maximalFunction_le` (the weak-type substitute at `p = 1`), this gives the
representative-level strong estimate for the maximal function. The resulting finiteness statement
is recorded by
`TauCeti.eLpNorm_maximalFunction_lt_top` below. -/
theorem eLpNorm_maximalFunction_le (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F}
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (maximalFunction μ f) p μ ≤
      (ENNReal.ofReal (2 * p.toReal * 2 ^ (p.toReal - 1) / (p.toReal - 1)) *
        4 ^ finrank ℝ E) ^ (1 / p.toReal) * eLpNorm f p μ := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow (lintegral_rpow_maximalFunction_le μ hf hpr) (by positivity)

end StrongType

section Finiteness

variable {p : ℝ≥0∞} {f : E → F}

/-- The maximal function of an `Lᵖ` function has finite `Lᵖ` seminorm when `1 < p ≤ ∞`. -/
theorem eLpNorm_maximalFunction_lt_top (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : AEMeasurable (fun x => ‖f x‖ₑ) μ) (hf_top : eLpNorm f p μ ≠ ∞)
    (hp : 1 < p) : eLpNorm (maximalFunction μ f) p μ < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [eLpNorm_exponent_top]
    refine (eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun x => ?_)).trans_lt (by
        simpa only [eLpNorm_exponent_top] using hf_top.lt_top)
    rw [enorm_eq_self]
    exact maximalFunction_le_eLpNormEssSup μ f x
  · exact (eLpNorm_maximalFunction_le μ hf hp hp_top).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hf_top.lt_top)

/-- The maximal function of a function with finite `Lᵖ` seminorm is finite almost everywhere
when `1 ≤ p`, including both endpoints. -/
theorem ae_maximalFunction_lt_top_of_eLpNorm_ne_top (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) (hf_top : eLpNorm f p μ ≠ ∞)
    (hp : 1 ≤ p) : ∀ᵐ x ∂μ, maximalFunction μ f x < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact .of_forall fun x => (maximalFunction_le_eLpNormEssSup μ f x).trans_lt
      (by simpa only [eLpNorm_exponent_top] using hf_top.lt_top)
  rcases hp.eq_or_lt with rfl | hp
  · exact ae_maximalFunction_lt_top μ f (by
      simpa only [eLpNorm_one_eq_lintegral_enorm] using hf_top)
  · have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
    have hpr : 1 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
    let g : E → ℝ≥0∞ := fun x => if 1 < ‖f x‖ₑ then ‖f x‖ₑ else 0
    have hg_le (x : E) : g x ≤ ‖f x‖ₑ ^ p.toReal := by
      simp only [g]
      split_ifs with hx
      · exact ENNReal.le_rpow_self_of_one_le hx.le hpr.le
      · exact bot_le
    have hfp : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ < ∞ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top).mp hf_top.lt_top
    have hg_int : ∫⁻ x, ‖g x‖ₑ ∂μ ≠ ∞ := by
      simpa only [enorm_eq_self] using (lt_of_le_of_lt (lintegral_mono hg_le) hfp).ne
    have hfg (x : E) : ‖f x‖ₑ ≤ 1 + g x := by
      simp only [g]
      split_ifs with hx
      · exact le_add_left le_rfl
      · simpa only [add_zero] using le_of_not_gt hx
    have hM (x : E) : maximalFunction μ f x ≤ 1 + maximalFunction μ g x := by
      calc
        maximalFunction μ f x ≤
            maximalFunction μ ((fun _ : E => (1 : ℝ≥0∞)) + g) x :=
          maximalFunction_mono_ae (.of_forall fun y => by
            simpa only [Pi.add_apply, enorm_eq_self] using hfg y)
        _ ≤ maximalFunction μ (fun _ : E => (1 : ℝ≥0∞)) x + maximalFunction μ g x :=
          maximalFunction_add_le aemeasurable_const x
        _ = 1 + maximalFunction μ g x := by
          rw [maximalFunction_const]
          simp only [enorm_eq_self]
    exact (ae_maximalFunction_lt_top μ g hg_int).mono fun x hx =>
      (hM x).trans_lt (ENNReal.add_lt_top.2 ⟨by finiteness, hx⟩)

end Finiteness

end Haar

end TauCeti
