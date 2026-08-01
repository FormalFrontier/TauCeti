/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Ergodic.InvariantSigma
public import TauCeti.Probability.Ergodic.MeanErgodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import TauCeti.Probability.Ergodic.BirkhoffLp
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving

/-!
# The mean ergodic projection is conditional expectation given the invariants

Mathlib's von Neumann mean ergodic theorem gives convergence to an orthogonal projection, and the
probabilistic form of the theorem still needs that projection identified with a conditional
expectation. This file carries out the identification for the `L²` composition (Koopman) operator
of a measure-preserving map `T`: the mean ergodic projection `metProjection T hT` of
`TauCeti.Probability.Ergodic.MeanErgodic` is Mathlib's `condExpL2` for the invariant σ-algebra
`MeasurableSpace.invariants T`. Passing from `condExpL2` to the conditional expectation
`μ[· | MeasurableSpace.invariants T]` of representatives costs exactly what Mathlib's
`MemLp.condExpL2_ae_eq_condExp'` costs — σ-finiteness of the trimmed measure
`μ.trim (MeasurableSpace.invariants_le T)` and integrability of the observable — so the pointwise
statements below assume those while the `condExpL2` ones do not. Both hold automatically on a
finite measure space.

The identification is not a simp step: it rests on `fixedSpace_eq_lpMeas_invariants`, which
replaces an almost invariant observable by an invariantly measurable representative, together with
the fact that both operators are orthogonal projections onto the resulting common subspace of
`L²`.

Feeding the identification into `birkhoffAverage_tendsto_metProjection` turns the Hilbert-space
statement into the probabilists' mean ergodic theorem: the time averages
`birkhoffAverage ℝ T f n` of an integrable square-integrable observable converge in `L²` to
`μ[f | MeasurableSpace.invariants T]`. The translation between the operator Birkhoff averages of
the composition operator and the pointwise Birkhoff averages of a representative is
`coeFn_birkhoffAverage_compMeasurePreserving` of `TauCeti.Probability.Ergodic.BirkhoffLp`.

## Main results

* `metProjection_eq_condExpL2` — the mean ergodic projection is `condExpL2` for the invariant
  σ-algebra, for an arbitrary measure;
* `metProjection_ae_eq_condExp` — its representatives are the conditional expectation given the
  invariant σ-algebra;
* `condExpL2_invariants_eq_self_iff` — `condExpL2` for the invariant σ-algebra fixes exactly the
  almost everywhere invariant observables, again for an arbitrary measure;
* `birkhoffAverage_tendsto_condExpL2` — the Birkhoff averages of the composition operator converge
  to `condExpL2`, and `tendsto_eLpNorm_birkhoffAverage_sub_condExp` — the pointwise Birkhoff
  averages converge in `L²` to the conditional expectation.

The `Exchangeability` roadmap records this identification as the Layer 5 milestone
`proj_eq_condexp`, whose migration source is the `Ergodic` subtree of
`cameronfreer/exchangeability`. Nothing here is a port: the statements are for an arbitrary
measure-preserving map rather than the path-space shift, and the proofs consume Mathlib's
`condExpL2` and von Neumann mean ergodic theorem.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

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
  rw [hcoe]
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [← fixedSpace_eq_lpMeas_invariants T hT]
    exact metProjection_mem_fixedSpace T hT g
  · rw [← fixedSpace_eq_lpMeas_invariants T hT]
    exact sub_metProjection_mem_orthogonal T hT g

/-- The mean ergodic projection of an integrable square-integrable observable is almost everywhere
its conditional expectation given the invariant σ-algebra. -/
theorem metProjection_ae_eq_condExp (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] (g : Lp ℝ 2 μ)
    (hg : Integrable (g : Ω → ℝ) μ) : (metProjection (𝕜 := ℝ) T hT g : Ω → ℝ) =ᵐ[μ]
      μ[(g : Ω → ℝ) | MeasurableSpace.invariants T] := by
  have h :=
    (Lp.memLp g).condExpL2_ae_eq_condExp' (𝕜 := ℝ) (MeasurableSpace.invariants_le T) hg
  rw [Lp.toLp_coeFn] at h
  rw [metProjection_eq_condExpL2]
  exact h

/-- Conditional expectation for the invariant σ-algebra fixes exactly the almost everywhere
invariant `L²` observables. -/
@[simp]
theorem condExpL2_invariants_eq_self_iff (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp ℝ 2 μ) :
    (condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g : Lp ℝ 2 μ) = g ↔
      (g : Ω → ℝ) ∘ T =ᵐ[μ] g := by
  rw [← metProjection_eq_condExpL2 T hT g, metProjection_eq_self_iff, mem_fixedSpace_iff hT,
    compMeasurePreserving_eq_self_iff hT]

/-! ## The mean ergodic theorem for conditional expectations -/

/-- The Birkhoff averages of the `L²` composition operator converge to the `L²` conditional
expectation for the invariant σ-algebra. -/
theorem birkhoffAverage_tendsto_condExpL2 (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp ℝ 2 μ) :
    Tendsto
      (birkhoffAverage ℝ (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap id · g)
      atTop (𝓝 (condExpL2 ℝ ℝ (MeasurableSpace.invariants_le T) g : Lp ℝ 2 μ)) := by
  simpa only [metProjection_eq_condExpL2 T hT g] using
    birkhoffAverage_tendsto_metProjection (𝕜 := ℝ) T hT g

/-- **The mean ergodic theorem for conditional expectations.** The Birkhoff time averages of an
integrable square-integrable observable converge in `L²` to its conditional expectation given the
invariant σ-algebra of the transformation. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    [SigmaFinite (μ.trim (MeasurableSpace.invariants_le T))] {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (hf_int : Integrable f μ) :
    Tendsto
      (fun n => eLpNorm (birkhoffAverage ℝ T f n - μ[f | MeasurableSpace.invariants T]) 2 μ)
      atTop (𝓝 0) := by
  have hBA := birkhoffAverage_tendsto_metProjection (𝕜 := ℝ) T hT (hf.toLp f)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hBA
  refine Filter.Tendsto.congr (fun n => eLpNorm_congr_ae ?_) hBA
  have haverage : ⇑(birkhoffAverage ℝ
      (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap id n (hf.toLp f)) =ᵐ[μ]
      birkhoffAverage ℝ T f n := by
    rw [LinearIsometry.coe_toContinuousLinearMap, coe_compMeasurePreservingₗᵢ]
    exact (coeFn_birkhoffAverage_compMeasurePreserving hT (hf.toLp f) n).trans
      (hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hf.coeFn_toLp n)
  have hprojection : ⇑(metProjection (𝕜 := ℝ) T hT (hf.toLp f)) =ᵐ[μ]
      μ[f | MeasurableSpace.invariants T] :=
    (metProjection_ae_eq_condExp T hT (hf.toLp f)
      (hf_int.congr hf.coeFn_toLp.symm)).trans (condExp_congr_ae hf.coeFn_toLp)
  exact haverage.sub hprojection

end Probability

end TauCeti
