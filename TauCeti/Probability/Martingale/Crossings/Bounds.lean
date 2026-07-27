/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Martingale.Upcrossing
import TauCeti.Probability.Martingale.Reverse
import TauCeti.Probability.Martingale.Crossings.Pathwise
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Crossings: uniform upcrossing bound for reverse martingales

The L¹-uniform upcrossing bound used in the reverse-martingale antitone-limit argument. Built on
top of `Pathwise.lean` and `Reverse.lean`.

## Main results

- `exists_lintegral_upcrossings_condExp_le` (roadmap alias `upcrossings_bdd_uniform`): a uniform
  crossing bound for the antitone conditional-expectation sequence `n ↦ μ[f | 𝔽 n]`, for integrable
  `f`.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings/Bounds.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Positive-part L¹ bound for the reversed conditional-expectation process: for integrable `f`,
the integral of `(revCEFinite f 𝔽 N M · - a)⁺` is bounded by `‖f‖₁ + |a| · μ(univ)`,
uniformly in the horizon `N` and the time `M`. -/
private lemma lintegral_pos_part_revCEFinite_le
    (f : Ω → ℝ) (hf : Integrable f μ) (a : ℝ) (N M : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ := by
  -- Use (x - a)⁺ ≤ |x - a| ≤ |x| + |a|, integrate, then convert to `eLpNorm` and apply the
  -- L¹ contraction of conditional expectation.
  calc ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (|revCEFinite (μ := μ) f 𝔽 N M ω| + |a|) ∂μ := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        calc (revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺
            = max (revCEFinite (μ := μ) f 𝔽 N M ω - a) 0 := rfl
          _ ≤ |revCEFinite (μ := μ) f 𝔽 N M ω - a| := by
              simp only [le_abs_self, max_le_iff, abs_nonneg, and_self]
          _ ≤ |revCEFinite (μ := μ) f 𝔽 N M ω| + |a| := by
              rw [sub_eq_add_neg]
              simpa using abs_add_le (revCEFinite (μ := μ) f 𝔽 N M ω) (-a)
    _ = ∫⁻ ω, (ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| + ENNReal.ofReal |a|) ∂μ := by
        simp [ENNReal.ofReal_add]
    _ = ∫⁻ ω, ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| ∂μ
          + ENNReal.ofReal |a| * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ := by
        gcongr
        have hconv : ∫⁻ ω, ENNReal.ofReal |revCEFinite (μ := μ) f 𝔽 N M ω| ∂μ =
            eLpNorm (revCEFinite (μ := μ) f 𝔽 N M) 1 μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          congr 1; ext ω
          exact (Real.enorm_eq_ofReal_abs _).symm
        rw [hconv]
        calc eLpNorm (revCEFinite (μ := μ) f 𝔽 N M) 1 μ
            ≤ eLpNorm f 1 μ := by
                rw [revCEFinite_apply]; exact eLpNorm_condExp_le_eLpNorm f le_rfl
          _ = ENNReal.ofReal (eLpNorm f 1 μ).toReal := by
              rw [ENNReal.ofReal_toReal]
              exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top

/-- Surrogate bound (kept private): uniform (in `N`) bound on upcrossings for the reversed
conditional-expectation process.

For an integrable `f` and the process obtained by reversing an antitone filtration, the expected
number of upcrossings is uniformly bounded, independent of the time horizon `N`, by Doob's
upcrossing inequality. The public `upcrossings_bdd_uniform` transfers this surrogate bound to the
genuine antitone sequence `n ↦ μ[f | 𝔽 n]`. -/
private lemma lintegral_upcrossings_revCEFinite_bdd
    [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C := by
  -- `C = (‖f‖₁ + |a| · μ(univ)) / (b - a)` via Doob's upcrossing inequality.
  set C := (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ)
      / ENNReal.ofReal (b - a)
  have hC_finite : C < ⊤ := by
    refine ENNReal.div_lt_top ?h1 ?h2
    · -- Numerator ≠ ⊤ (finite measure keeps `μ Set.univ < ⊤`)
      refine (ENNReal.add_lt_top.2 ⟨?_, ?_⟩).ne
      · rw [ENNReal.ofReal_toReal]
        · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
        · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
      · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
    · -- Denominator ≠ 0
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  refine ⟨C, hC_finite, fun N => ?_⟩
  -- Doob's upcrossing inequality for the reversed submartingale, then bound the supremum with
  -- the positive-part L¹ estimate.
  have hsub := (revCEFinite_martingale (μ := μ) h_antitone h_le f N).submartingale
  have key := hsub.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ :=
    iSup_le fun M => lintegral_pos_part_revCEFinite_le f hf a N M
  have step1 : (∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ)
      * ENNReal.ofReal (b - a)
      ≤ ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ := by
    rw [mul_comm]; exact key
  calc ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ
      ≤ (⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCEFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ)
          / ENNReal.ofReal (b - a) := by
        refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 step1
        · left; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
        · left; exact ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ)
          / ENNReal.ofReal (b - a) := by
        gcongr
    _ = C := rfl

/-- Pathwise comparison: the upcrossings of `n ↦ μ[f | 𝔽 n]` on `[a, b]` before time `N` are
bounded by the total upcrossings on `[-b, -a]` of the negated finite-horizon reverse process. -/
private lemma upcrossingsBefore_condExp_le_upcrossings_neg_revCEFinite
    (f : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ upcrossings (-b) (-a) (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
  -- `revProcess (μ[f|𝔽·]) N` and `revCEFinite f 𝔽 N` agree on `[0, N]` (below the horizon,
  -- `Polynomial.revAt N` is genuine subtraction). The `N + 1` reversed horizon lets crossings
  -- completing exactly at `N` count, but the extra index `N + 1` is a *free boundary*: it never
  -- affects the crossing count (`upcrossingsBefore_succ_congr`), so we may swap the two processes
  -- there even though they differ at `N + 1`.
  have h_agree : ∀ n ≤ N, (-(revProcess (fun n => μ[f | 𝔽 n]) N)) n ω
      = (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) n ω := by
    intro n hn
    simp only [Pi.neg_apply, revProcess_apply_of_le _ hn, revCEFinite_apply]
  have hle : upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
      ≤ upcrossingsBefore (-b) (-a) (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) (N + 1) ω :=
    calc upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
        ≤ upcrossingsBefore (-b) (-a) (-(revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω :=
          upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ _ a b hab N ω
      _ = upcrossingsBefore (-b) (-a) (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) (N + 1) ω :=
          upcrossingsBefore_succ_congr h_agree
  calc ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ ↑(upcrossingsBefore (-b) (-a)
            (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) (N + 1) ω) := Nat.cast_le.mpr hle
    _ ≤ upcrossings (-b) (-a) (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
        simp only [MeasureTheory.upcrossings]
        exact le_iSup (fun M => (upcrossingsBefore (-b) (-a)
          (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) M ω : ℝ≥0∞)) (N + 1)

/-- Finite-horizon integral step: negating commutes a.e. with the reverse conditional-expectation
process (via `condExp_neg`), so the upcrossing integrals of the negated process and of the reverse
process of `-f` agree. -/
private lemma lintegral_upcrossings_neg_revCEFinite_eq
    (f : Ω → ℝ) (a b : ℝ) (N : ℕ) :
    ∫⁻ ω, upcrossings (-b) (-a)
        (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω ∂μ
      = ∫⁻ ω, upcrossings (-b) (-a)
          (fun n => revCEFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ := by
  apply lintegral_congr_ae
  -- The two processes agree a.e. at every time index (countable intersection via `ae_all_iff`).
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
      (-(fun m => revCEFinite (μ := μ) f 𝔽 N m)) n ω =
      revCEFinite (μ := μ) (fun x => -f x) 𝔽 N n ω := by
    rw [ae_all_iff]
    intro n
    simp only [Pi.neg_apply, revCEFinite_apply]
    exact (condExp_neg f (𝔽 (N - n))).symm
  filter_upwards [h_ae_eq] with ω hω
  simp only [MeasureTheory.upcrossings]
  refine iSup_congr fun M => ?_
  rw [upcrossingsBefore_congr (fun k _ => hω k)]

/-- Upgrade a uniform-in-`N` bound on the per-horizon `upcrossingsBefore` integrals to a bound on
the total `upcrossings` integral, by monotone convergence in the horizon `N`. The adapted process
`g` supplies the measurability of each `upcrossingsBefore` count. -/
private lemma lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le
    {g : ℕ → Ω → ℝ} {a b : ℝ} {C : ℝ≥0∞}
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    (h_adapted : StronglyAdapted ℱ g) (hab : a < b)
    (h_N_bound : ∀ N, ∫⁻ ω, ↑(upcrossingsBefore a b g N ω) ∂μ ≤ C) :
    ∫⁻ ω, upcrossings a b g ω ∂μ ≤ C := by
  -- Set `U N ω := upcrossingsBefore` (as `ℝ≥0∞`) for the process `g`.
  set U : ℕ → Ω → ℝ≥0∞ := fun N ω => (upcrossingsBefore a b g N ω : ℝ≥0∞) with hU
  -- Monotonicity in `N` (pathwise): more time allows more completed crossings.
  have hU_mono : Monotone U := by
    intro m n hmn ω
    simp only [hU]
    exact Nat.cast_le.2 (upcrossingsBefore_mono (f := g) hab hmn ω)
  -- Measurability of each `U N` via the adaptedness hypothesis.
  have hU_meas : ∀ N, Measurable (U N) := fun _ =>
    measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab)
  -- Monotone convergence, then bound the supremum of integrals by `C`.
  have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := lintegral_iSup hU_meas hU_mono
  have hbound : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := iSup_le h_N_bound
  -- Conclude via `upcrossings = ⨆ N, upcrossingsBefore N`.
  simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans hbound

/-- Uniform crossing bound for the antitone conditional-expectation sequence.

For an antitone filtration `𝔽` and integrable `f`, the expected number of upcrossings of the
conditional-expectation process `n ↦ μ[f | 𝔽 n]` on any interval `[a, b]` is finite — the L¹
reverse-martingale upcrossing bound. This is the crossing bound consumed by the antitone-limit
(Lévy downward) argument. -/
theorem exists_lintegral_upcrossings_condExp_le [IsFiniteMeasure μ] (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) (hf : Integrable f μ)
    (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
  -- Downcrossings-side surrogate bound: apply the (private) reversed-process bound to `-f` on the
  -- reflected interval `[-b, -a]`. This yields the constant `C_down` used throughout.
  obtain ⟨C_down, h_C_down_finite, hC_down⟩ :=
    lintegral_upcrossings_revCEFinite_bdd (μ := μ) h_antitone h_le
      (fun ω => -f ω) hf.neg (-b) (-a) (by linarith)
  refine ⟨C_down, h_C_down_finite, ?_⟩
  -- Per-horizon `L¹` bound: compose the pathwise comparison with the negation-commutes step, then
  -- discharge with the surrogate bound `hC_down`.
  have h_N_bound : ∀ N,
      ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C_down := fun N =>
    calc ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ
        ≤ ∫⁻ ω, upcrossings (-b) (-a)
              (-(fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω ∂μ :=
          lintegral_mono
            (upcrossingsBefore_condExp_le_upcrossings_neg_revCEFinite f hab N)
      _ = ∫⁻ ω, upcrossings (-b) (-a)
            (fun n => revCEFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ :=
          lintegral_upcrossings_neg_revCEFinite_eq f a b N
      _ ≤ C_down := hC_down N
  -- The sequence `μ[f | 𝔽 n]` is adapted to the constant ambient filtration, supplying the
  -- measurability needed for the monotone-convergence upgrade.
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Ω) le_rfl
  have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
    fun n => stronglyMeasurable_condExp.mono (h_le n)
  -- Upgrade the per-horizon bound to the total upcrossings integral (monotone convergence in `N`).
  exact lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le h_adapted hab h_N_bound

/-- Roadmap Layer 4 target name (`TauCetiRoadmap/Exchangeability`) for the uniform upcrossing bound
`exists_lintegral_upcrossings_condExp_le`. -/
alias upcrossings_bdd_uniform := exists_lintegral_upcrossings_condExp_le

end MeasureTheory
