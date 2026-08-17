/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- `Mathlib.MeasureTheory.Measure.Prod` is imported privately: the product measure and
-- Tonelli's theorem appear only inside the proof below.
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Marcinkiewicz interpolation between weak type `(1,1)` and `L^∞`

A **sublinear** operator `T` that is simultaneously of **weak type `(1,1)`** and bounded on `L^∞`
is bounded on `L^p` for every `1 < p < ∞`. This is the diagonal case `p₀ = 1`, `p₁ = ∞` of the
Marcinkiewicz interpolation theorem, and it is the mechanism that turns the Hardy–Littlewood
maximal inequality into the strong `(p,p)` bounds, item 9 of Lane B of the PDE roadmap.

## The statement proved here

Interpolation arguments run entirely on the **distribution functions** of `T f` and of `f`, so the
theorem is stated in that form rather than in terms of a bundled operator: the sublinearity of `T`
and its two endpoint bounds are used only to produce, for each height `t`, the single inequality

`t * ν {T f > t} ≤ A * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`,

which says that only the part of `f` above the height `c * t` can push `T f` above `t`. That
inequality is the hypothesis of `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`, and its
conclusion is the `L^p` bound

`∫⁻ (T f) ^ p ∂ν ≤ (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ ‖f‖ ^ p ∂μ`.

Keeping the hypothesis in this form has three advantages. It does not force `T` to be defined on
all of a function space; it lets `μ` and `ν` live on different spaces, as a genuine interpolation
statement should; and it makes the dependence of the constant on `p`, on the weak-type constant
`A` and on the truncation ratio `c` completely explicit, which matters because the constant blows
up as `p → 1`, exactly as it must — an operator of weak type `(1,1)` need not be bounded on `L¹`.

## The proof

The layer cake formula (`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`) converts both
sides into integrals in the height variable `t`. The hypothesis, multiplied by `t ^ (p - 2)`,
bounds the integrand by `A * t ^ (p - 2) * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`; Tonelli's theorem then
exchanges the `t` and `x` integrations, and for each fixed `x` the inner integral is the
elementary `∫⁻ t in (0, ‖f x‖ / c), t ^ (p - 2) = (‖f x‖ / c) ^ (p - 1) / (p - 1)`, evaluated by
`TauCeti.lintegral_indicator_ofReal_rpow_Ioi`, which reassembles into
`c ^ (1 - p) / (p - 1) * ‖f x‖ ^ p`. Convergence of that inner integral at the origin is where
`1 < p` is used, and it is why the constant carries the factor `1 / (p - 1)`.

Tonelli's theorem needs `μ` to be s-finite, but the statement does not: both sides ignore the
part of `μ` outside `{f > 0}`, and once `∫⁻ f ^ p ∂μ` is finite that part is σ-finite, being
exhausted by the level sets `{f ≥ 1 / (n + 1)}`, each of finite measure by Chebyshev.

## Main declarations

* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`: the interpolation estimate.

## References

* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.1.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {u : β → ℝ≥0∞} {p c : ℝ} {A : ℝ≥0∞}

/-- The interpolation estimate for a measurable `f` and an s-finite `μ`, which is the generality
in which Tonelli's theorem is available; both hypotheses are removed below. -/
private theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite [SFinite μ]
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  -- The jointly measurable integrand of the double integral: the part of `f` above the height
  -- `c * t`, weighted by `t ^ (p - 2)`.
  set S : Set (ℝ × α) := {q | ENNReal.ofReal (c * q.1) < f q.2} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_lt ((measurable_fst.const_mul c).ennreal_ofReal) (hf.comp measurable_snd)
  have hfstpow : Measurable fun q : ℝ × α => ENNReal.ofReal (q.1 ^ (p - 2)) :=
    (measurable_fst.pow measurable_const).ennreal_ofReal
  have hrpow : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 2)) :=
    (measurable_id.pow measurable_const).ennreal_ofReal
  set G : ℝ × α → ℝ≥0∞ := S.indicator fun q => ENNReal.ofReal (q.1 ^ (p - 2)) * f q.2 with hG
  have hGmeas : Measurable G := (hfstpow.mul (hf.comp measurable_snd)).indicator hSmeas
  -- `G` is the weight `t ^ (p - 2)` times the truncation of `f` at the height `c * t`; the same
  -- cut-off can be read as a condition on `x` for a fixed `t`, or as one on `t` for a fixed `x`.
  have hGval : ∀ (t : ℝ) (x : α), G (t, x) =
      ENNReal.ofReal (t ^ (p - 2)) * {x | ENNReal.ofReal (c * t) < f x}.indicator f x := by
    intro t x
    have hmem : (t, x) ∈ S ↔ x ∈ {x | ENNReal.ofReal (c * t) < f x} := by
      simp only [hS, Set.mem_ofPred]
    by_cases hx : x ∈ {x | ENNReal.ofReal (c * t) < f x}
    · rw [hG, Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx]
    · rw [hG, Set.indicator_of_notMem (hmem.not.2 hx), Set.indicator_of_notMem hx, mul_zero]
  have hGvalt : ∀ (t : ℝ) (x : α), G (t, x) =
      {t : ℝ | ENNReal.ofReal (c * t) < f x}.indicator
        (fun t => ENNReal.ofReal (t ^ (p - 2))) t * f x := by
    intro t x
    have hmem : (t, x) ∈ S ↔ t ∈ {t : ℝ | ENNReal.ofReal (c * t) < f x} := by
      simp only [hS, Set.mem_ofPred]
    by_cases ht : t ∈ {t : ℝ | ENNReal.ofReal (c * t) < f x}
    · rw [hG, Set.indicator_of_mem (hmem.2 ht), Set.indicator_of_mem ht]
    · rw [hG, Set.indicator_of_notMem (hmem.not.2 ht), Set.indicator_of_notMem ht, zero_mul]
  -- Its slices are the truncated integrals appearing in the hypothesis.
  have hslice : ∀ t : ℝ, ∫⁻ x, G (t, x) ∂μ =
      ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ := by
    intro t
    have hSt : MeasurableSet {x | ENNReal.ofReal (c * t) < f x} :=
      measurableSet_lt measurable_const hf
    rw [← lintegral_indicator hSt, ← lintegral_const_mul _ (hf.indicator hSt)]
    exact lintegral_congr fun x => hGval t x
  -- Multiplying the hypothesis by `t ^ (p - 2)` bounds the layer cake integrand.
  have hkey : ∀ t ∈ Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) ≤
      A * ∫⁻ x, G (t, x) ∂μ := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hexp : p - 1 = 1 + (p - 2) := by ring
    have hpow : t ^ (p - 1) = t * t ^ (p - 2) := by
      rw [hexp, Real.rpow_add ht', Real.rpow_one]
    calc ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 2)) := by
          rw [hpow, ENNReal.ofReal_mul ht'.le]; ring
      _ ≤ (A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) *
            ENNReal.ofReal (t ^ (p - 2)) := mul_le_mul_left (h t ht') _
      _ = A * ∫⁻ x, G (t, x) ∂μ := by rw [hslice t]; ring
  -- For each `x`, the inner integral in `t` is the truncated power integral.
  have hinner : ∀ x, (∫⁻ t in Ioi (0 : ℝ), G (t, x)) =
      ENNReal.ofReal (c ^ (1 - p) / (p - 1)) * f x ^ p := by
    intro x
    have hcut : MeasurableSet {t : ℝ | ENNReal.ofReal (c * t) < f x} :=
      measurableSet_lt ((measurable_id.const_mul c).ennreal_ofReal) measurable_const
    have hexp : p - 2 + 1 = p - 1 := by ring
    have hneg : (1 : ℝ) - p = -(p - 1) := by ring
    -- `f x ^ (p - 1) * f x = f x ^ p`, valid also at the values `0` and `∞`.
    have hsucc : f x ^ (p - 1) * f x = f x ^ p := by
      conv_rhs => rw [← sub_add_cancel p 1]
      rw [ENNReal.rpow_add_of_nonneg _ _ hp1.le zero_le_one, ENNReal.rpow_one]
    rw [lintegral_congr fun t => hGvalt t x, lintegral_mul_const _ (hrpow.indicator hcut),
      lintegral_indicator_ofReal_rpow_Ioi (by linarith) hc (f x), hexp, hneg, mul_assoc, hsucc]
  -- Assemble: layer cake, the pointwise bound, Tonelli, and the inner integral.
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ν hu hp0]
  calc ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), A * ∫⁻ x, G (t, x) ∂μ := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hkey t ht
    _ = ENNReal.ofReal p * (A * ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), G (t, x)) ∂μ) := by
        rw [lintegral_const_mul _ hGmeas.lintegral_prod_right',
          lintegral_lintegral_swap (f := fun t x => G (t, x)) hGmeas.aemeasurable]
    _ ≤ ENNReal.ofReal p * (A * (ENNReal.ofReal (c ^ (1 - p) / (p - 1)) * ∫⁻ x, f x ^ p ∂μ)) := by
        gcongr
        rw [← lintegral_const_mul _ (hf.pow_const p)]
        exact lintegral_mono fun x => (hinner x).le
    _ = ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
        have hconst : p * c ^ (1 - p) / (p - 1) = p * (c ^ (1 - p) / (p - 1)) := by ring
        rw [hconst, ENNReal.ofReal_mul hp0.le]
        ring

/-- A function with a finite `L^p` norm is carried by a σ-finite part of the measure: the level
sets `{f ≥ 1 / (n + 1)}` have finite measure by Chebyshev's inequality applied to `f ^ p`, and they
exhaust `{f > 0}`. -/
private theorem sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top (hf : Measurable f)
    (hp : 0 < p) (htop : ∫⁻ x, f x ^ p ∂μ ≠ ∞) : SigmaFinite (μ.restrict {x | 0 < f x}) := by
  have hsmeas : MeasurableSet {x | 0 < f x} := measurableSet_lt measurable_const hf
  have hlevel : ∀ n : ℕ, μ {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} ≠ ∞ := by
    intro n
    have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.2 (by simp [ENNReal.natCast_ne_top])
    have hεpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ ^ p := ENNReal.rpow_pos hpos hne
    have hset : {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} = {x | ((n : ℝ≥0∞) + 1)⁻¹ ^ p ≤ f x ^ p} :=
      Set.ext fun x => (ENNReal.rpow_le_rpow_iff hp).symm
    rw [hset]
    refine ne_top_of_le_ne_top (ENNReal.div_lt_top htop hεpos.ne').ne
      (meas_ge_le_lintegral_div (hf.pow_const p).aemeasurable hεpos.ne'
        (ENNReal.rpow_ne_top_of_nonneg hp.le hne))
  refine ⟨⟨⟨fun n => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} ∪ {x | 0 < f x}ᶜ, fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    have hcompl : μ.restrict {x | 0 < f x} {x | 0 < f x}ᶜ = 0 := by
      rw [Measure.restrict_apply hsmeas.compl, Set.compl_inter_self, measure_empty]
    refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [hcompl, add_zero]
    exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (lt_top_iff_ne_top.2 (hlevel n))
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne (f x) 0 with hx | hx
    · exact Set.mem_iUnion.2 ⟨0, Set.mem_union_right _ (by simp [hx])⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
      exact Set.mem_iUnion.2
        ⟨n, Set.mem_union_left _ ((ENNReal.inv_le_inv' le_self_add).trans hn.le)⟩

/-- The interpolation estimate for a measurable `f` and an arbitrary measure `μ`.

Only the part of `μ` carried by `{f > 0}` enters either side, and once `f` has finite `L^p` norm
that part is σ-finite by `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`. So the
s-finite case applies to `μ` restricted to `{f > 0}`, after the two degenerate cases — a vanishing
weak-type constant and an infinite right-hand side — are disposed of. -/
private theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hK : (0 : ℝ) < p * c ^ (1 - p) / (p - 1) := by positivity
  rcases eq_or_ne A 0 with hA | hA
  · -- With `A = 0` the hypothesis holds over the zero measure as well, and there it already
    -- yields the bound `∫⁻ u ^ p ∂ν ≤ 0`.
    have hzero := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite
      (μ := (0 : Measure α)) (A := A) hf hu hp hc fun t ht => by simpa [hA] using h t ht
    simpa [hA] using hzero
  rcases eq_or_ne (∫⁻ x, f x ^ p ∂μ) ∞ with htop | htop
  · -- The right-hand side is infinite.
    rw [htop, ENNReal.mul_top (mul_ne_zero (ENNReal.ofReal_pos.2 hK).ne' hA)]
    exact le_top
  -- `μ` restricted to `{f > 0}` is σ-finite, so in particular s-finite.
  have hσ : SigmaFinite (μ.restrict {x | 0 < f x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hf hp0 htop
  -- The truncated integrals of the hypothesis do not see the complement of `{f > 0}`.
  have hsub : ∀ t : ℝ, 0 < t → {x | ENNReal.ofReal (c * t) < f x} ⊆ {x | 0 < f x} := by
    intro t _ x hx
    exact Set.mem_ofPred.2 (lt_of_le_of_lt zero_le (Set.mem_ofPred.1 hx))
  -- Neither does `∫⁻ f ^ p`, since `f ^ p` is supported in `{f > 0}`.
  have hpow : ∫⁻ x, f x ^ p ∂μ.restrict {x | 0 < f x} = ∫⁻ x, f x ^ p ∂μ := by
    refine setLIntegral_eq_of_support_subset fun x hx => ?_
    have hx' : f x ^ p ≠ 0 := hx
    refine Set.mem_ofPred.2 (pos_iff_ne_zero.2 fun h0 => hx' ?_)
    rw [h0, ENNReal.zero_rpow_of_pos hp0]
  have hmain := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite
    (μ := μ.restrict {x | 0 < f x}) hf hu hp hc fun t ht => by
      rw [Measure.restrict_restrict_of_subset (hsub t ht)]
      exact h t ht
  rwa [hpow] at hmain

/-- **Marcinkiewicz interpolation**, the diagonal case `p₀ = 1`, `p₁ = ∞`, in distributional form.

If for every height `t > 0` the superlevel set `{u > t}` obeys the weak-type bound

`t * ν {u > t} ≤ A * ∫⁻ x in {f > c * t}, f ∂μ`

against the part of `f` above `c * t`, then for every `1 < p < ∞`

`∫⁻ u ^ p ∂ν ≤ (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ f ^ p ∂μ`.

Applied with `u = T f` for a sublinear `T`, the hypothesis is what the weak `(1,1)` and `L^∞`
endpoint bounds for `T` give after splitting `f` at the height `c * t`, and the conclusion is the
strong type `(p,p)` bound. The constant degenerates as `p → 1`, as it must. -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le
    (hf : AEMeasurable f μ) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hae := hf.ae_eq_mk
  have hset : ∀ a : ℝ≥0∞,
      ∫⁻ x in {x | a < f x}, f x ∂μ = ∫⁻ x in {x | a < hf.mk f x}, hf.mk f x ∂μ := by
    intro a
    have hsets : {x | a < f x} =ᵐ[μ] {x | a < hf.mk f x} := by
      filter_upwards [hae] with x hx
      exact congrArg (fun z : ℝ≥0∞ => a < z) hx
    rw [Measure.restrict_congr_set hsets]
    exact lintegral_congr_ae (ae_restrict_of_ae hae)
  have hrpow : (fun x => f x ^ p) =ᵐ[μ] fun x => hf.mk f x ^ p :=
    hae.mono fun x hx => congrArg (fun z : ℝ≥0∞ => z ^ p) hx
  rw [lintegral_congr_ae hrpow]
  refine lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable hf.measurable_mk hu hp hc
    fun t ht => ?_
  rw [← hset]
  exact h t ht

end TauCeti
