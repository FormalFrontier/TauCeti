/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Ergodic.InvariantSigma
public import TauCeti.Probability.Ergodic.MeanErgodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# The mean ergodic projection is conditional expectation given the invariants

Mathlib's von Neumann mean ergodic theorem gives convergence to an orthogonal projection, and the
probabilistic form of the theorem still needs that projection identified with a conditional
expectation. This file carries out the identification for the `L²` composition (Koopman) operator
of a measure-preserving map `T`: the mean ergodic projection `metProjection T hT` of
`TauCeti.Probability.Ergodic.MeanErgodic` is Mathlib's `condExpL2` for the invariant σ-algebra
`MeasurableSpace.invariants T`, and therefore almost everywhere the conditional expectation
`μ[· | MeasurableSpace.invariants T]`.

The identification is not a simp step: it rests on `fixedSpace_eq_lpMeas_invariants`, which
replaces an almost invariant observable by an invariantly measurable representative, together with
the fact that both operators are orthogonal projections onto the resulting common subspace of
`L²`.

Feeding the identification into `birkhoffAverage_tendsto_metProjection` turns the Hilbert-space
statement into the probabilists' mean ergodic theorem: the time averages `birkhoffAverage ℝ T f n`
of a square-integrable observable converge in `L²` to `μ[f | MeasurableSpace.invariants T]`. The
translation between the operator Birkhoff averages of the composition operator and the pointwise
Birkhoff averages of a representative is `coeFn_birkhoffAverage_compMeasurePreserving`.

## Main results

* `metProjection_eq_condExpL2` — the mean ergodic projection is `condExpL2` for the invariant
  σ-algebra;
* `metProjection_ae_eq_condExp` — its representatives are the conditional expectation given the
  invariant σ-algebra;
* `condExpL2_invariants_eq_self_iff` — that conditional expectation fixes exactly the almost
  everywhere invariant observables;
* `coeFn_birkhoffAverage_compMeasurePreserving` — the Birkhoff averages of the composition
  operator are represented by the pointwise Birkhoff averages of a representative;
* `birkhoffAverage_tendsto_condExpL2` and `tendsto_eLpNorm_birkhoffAverage_sub_condExp` — the two
  resulting forms of the mean ergodic theorem for conditional expectations.

The `Exchangeability` roadmap records this identification as the Layer 5 milestone
`proj_eq_condexp`, whose migration source is the `Ergodic` subtree of
`cameronfreer/exchangeability`. Nothing here is a port: the statements are for an arbitrary
measure-preserving map rather than the path-space shift, and the proofs consume Mathlib's
`condExpL2` and von Neumann mean ergodic theorem.
-/

public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The projection as a conditional expectation -/

/-- The mean ergodic projection on real `L²` is Mathlib's `L²` conditional expectation for the
invariant σ-algebra of the transformation.

Both sides are the orthogonal projection onto the same closed subspace of `L²`: the observables
fixed by composition with `T` are exactly those almost everywhere strongly measurable for
`MeasurableSpace.invariants T`, by `fixedSpace_eq_lpMeas_invariants`. -/
theorem metProjection_eq_condExpL2 (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp ℝ 2 μ) :
    metProjection (𝕜 := ℝ) T hT g =
      (condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g : Lp ℝ 2 μ) := by
  haveI : Fact (MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace Ω)) :=
    ⟨MeasurableSpace.invariants_le T⟩
  have hcoe :
      ((condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g :
          lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ) : Lp ℝ 2 μ) =
        (lpMeas ℝ ℝ (MeasurableSpace.invariants T) 2 μ).starProjection g :=
    Submodule.coe_orthogonalProjectionOnto_apply _ g
  rw [metProjection_eq_starProjection]
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [fixedSpace_eq_lpMeas_invariants T hT]
    exact Submodule.coe_mem _
  · rw [fixedSpace_eq_lpMeas_invariants T hT, hcoe]
    exact Submodule.sub_starProjection_mem_orthogonal _

/-- On a finite measure space, the mean ergodic projection of a square-integrable observable is
almost everywhere its conditional expectation given the invariant σ-algebra. -/
theorem metProjection_ae_eq_condExp [IsFiniteMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Lp ℝ 2 μ) :
    (metProjection (𝕜 := ℝ) T hT g : Ω → ℝ) =ᵐ[μ]
      μ[(g : Ω → ℝ) | MeasurableSpace.invariants T] := by
  have h := (Lp.memLp g).condExpL2_ae_eq_condExp (𝕜 := ℝ) (MeasurableSpace.invariants_le T)
  rw [Lp.toLp_coeFn] at h
  rw [metProjection_eq_condExpL2]
  exact h

/-- Conditional expectation for the invariant σ-algebra fixes exactly the almost everywhere
invariant `L²` observables. -/
theorem condExpL2_invariants_eq_self_iff (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp ℝ 2 μ) :
    (condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g : Lp ℝ 2 μ) = g ↔
      (g : Ω → ℝ) ∘ T =ᵐ[μ] g := by
  rw [← metProjection_eq_condExpL2 T hT g, metProjection_eq_self_iff, mem_fixedSpace_iff hT,
    compMeasurePreserving_eq_self_iff hT]

/-! ## Birkhoff averages of the composition operator -/

section Birkhoff

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Iterating the `Lᵖ` composition operator composes with the iterated transformation. -/
theorem coeFn_iterate_compMeasurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) (n : ℕ) :
    ⇑((Lp.compMeasurePreserving (E := E) (p := p) T hT)^[n] g) =ᵐ[μ] ⇑g ∘ T^[n] := by
  rw [Lp.compMeasurePreserving_iterate hT n]
  exact Lp.coeFn_compMeasurePreserving g (hT.iterate n)

/-- The Birkhoff sums of the `Lᵖ` composition operator are represented by the pointwise Birkhoff
sums of any representative. -/
theorem coeFn_birkhoffSum_compMeasurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) (n : ℕ) :
    ⇑(birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g) =ᵐ[μ]
      birkhoffSum T (⇑g) n := by
  induction n with
  | zero =>
      simp only [birkhoffSum_zero', Pi.zero_apply]
      exact Lp.coeFn_zero E p μ
  | succ n ih =>
      rw [birkhoffSum_succ]
      filter_upwards [ih, coeFn_iterate_compMeasurePreserving hT g n,
        Lp.coeFn_add (birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g)
          (id ((Lp.compMeasurePreserving (E := E) (p := p) T hT)^[n] g))] with ω hsum hiter hadd
      rw [hadd, birkhoffSum_succ]
      exact congrArg₂ _ hsum hiter

/-- Almost everywhere equal observables have almost everywhere equal Birkhoff sums along a
measure-preserving transformation. -/
theorem birkhoffSum_congr_ae {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f₁ f₂ : Ω → E}
    (hf : f₁ =ᵐ[μ] f₂) (n : ℕ) :
    birkhoffSum T f₁ n =ᵐ[μ] birkhoffSum T f₂ n := by
  induction n with
  | zero => simp only [birkhoffSum_zero']; rfl
  | succ n ih =>
      filter_upwards [ih, (hT.iterate n).quasiMeasurePreserving.ae_eq_comp hf] with ω hsum hiter
      rw [birkhoffSum_succ, birkhoffSum_succ]
      exact congrArg₂ _ hsum hiter

variable [NormedSpace ℝ E]

/-- The Birkhoff averages of the `Lᵖ` composition operator are represented by the pointwise
Birkhoff averages of any representative. -/
theorem coeFn_birkhoffAverage_compMeasurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) (n : ℕ) :
    ⇑(birkhoffAverage ℝ (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g) =ᵐ[μ]
      birkhoffAverage ℝ T (⇑g) n := by
  filter_upwards [coeFn_birkhoffSum_compMeasurePreserving hT g n,
    Lp.coeFn_smul ((n : ℝ)⁻¹)
      (birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g)] with ω hsum hsmul
  rw [birkhoffAverage, hsmul, Pi.smul_apply, hsum, birkhoffAverage]

/-- Almost everywhere equal observables have almost everywhere equal Birkhoff averages along a
measure-preserving transformation. -/
theorem birkhoffAverage_congr_ae {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f₁ f₂ : Ω → E}
    (hf : f₁ =ᵐ[μ] f₂) (n : ℕ) :
    birkhoffAverage ℝ T f₁ n =ᵐ[μ] birkhoffAverage ℝ T f₂ n := by
  filter_upwards [birkhoffSum_congr_ae hT hf n] with ω hω
  rw [birkhoffAverage, birkhoffAverage, hω]

end Birkhoff

/-! ## The mean ergodic theorem for conditional expectations -/

private theorem coe_compMeasurePreservingₗᵢ_toContinuousLinearMap (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) :
    ⇑(Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) T hT).toContinuousLinearMap =
      ⇑(Lp.compMeasurePreserving (E := ℝ) (p := 2) T hT) := by
  funext g
  rfl

/-- The Birkhoff averages of the `L²` composition operator converge to the `L²` conditional
expectation for the invariant σ-algebra. -/
theorem birkhoffAverage_tendsto_condExpL2 (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp ℝ 2 μ) :
    Tendsto
      (birkhoffAverage ℝ (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap id · g)
      atTop (𝓝 (condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g : Lp ℝ 2 μ)) := by
  simpa only [metProjection_eq_condExpL2 T hT g] using
    birkhoffAverage_tendsto_metProjection (𝕜 := ℝ) T hT g

/-- **The mean ergodic theorem for conditional expectations.** On a finite measure space, the
Birkhoff time averages of a square-integrable observable converge in `L²` to its conditional
expectation given the invariant σ-algebra of the transformation. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp [IsFiniteMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Tendsto
      (fun n => eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) 2 μ)
      atTop (𝓝 0) := by
  have hBA := birkhoffAverage_tendsto_metProjection (𝕜 := ℝ) T hT (hf.toLp f)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hBA
  refine Filter.Tendsto.congr (fun n => eLpNorm_congr_ae ?_) hBA
  have haverage : ⇑(birkhoffAverage ℝ
      (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap id n (hf.toLp f)) =ᵐ[μ]
      birkhoffAverage ℝ T f n := by
    rw [coe_compMeasurePreservingₗᵢ_toContinuousLinearMap T hT]
    exact (coeFn_birkhoffAverage_compMeasurePreserving hT (hf.toLp f) n).trans
      (birkhoffAverage_congr_ae hT hf.coeFn_toLp n)
  have hprojection : ⇑(metProjection (𝕜 := ℝ) T hT (hf.toLp f)) =ᵐ[μ]
      μ[f | MeasurableSpace.invariants T] :=
    (metProjection_ae_eq_condExp T hT (hf.toLp f)).trans (condExp_congr_ae hf.coeFn_toLp)
  exact haverage.sub hprojection

end Probability

end TauCeti
