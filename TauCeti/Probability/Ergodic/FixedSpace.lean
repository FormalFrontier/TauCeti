/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed points of a measure-preserving transformation on `Lᵖ`

This file relates membership in Mathlib's fixed submodule for the `Lᵖ` composition isometry to
almost-everywhere invariance of representatives. This is the closed subspace onto which the mean
ergodic projection in the Koopman route to de Finetti's theorem will project.

It also records the simp lemma `coe_compMeasurePreservingₗᵢ`, which identifies the map underlying
the composition isometry with Mathlib's composition operator
`MeasureTheory.Lp.compMeasurePreserving`, so that statements phrased with the isometry can be
rewritten into the form the lemmas about representatives use.
-/

public section

noncomputable section

open Function MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

section Generic

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NormedRing 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable {p : ℝ≥0∞} {μ : Measure Ω}

/-- The submodule of `Lᵖ` observables fixed by composition with a measure-preserving
transformation. -/
def fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Submodule 𝕜 (Lp E p μ) :=
  (Lp.compMeasurePreservingₗ 𝕜 T hT).fixedSubmodule

private theorem compMeasurePreservingₗ_apply (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) :
    Lp.compMeasurePreservingₗ 𝕜 T hT g = Lp.compMeasurePreserving T hT g := by
  rw [Lp.compMeasurePreservingₗ_apply]
  exact congrFun (AddHom.toFun_eq_coe (Lp.compMeasurePreserving T hT).toAddHom) g

/-- Membership in the fixed space means being fixed by the composition operator. -/
@[simp]
theorem mem_fixedSpace_iff {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    g ∈ fixedSpace (𝕜 := 𝕜) T hT ↔ Lp.compMeasurePreserving T hT g = g := by
  rw [fixedSpace, LinearMap.mem_fixedSubmodule_iff]
  rw [compMeasurePreservingₗ_apply]

/-- Characterization of fixed points of the `Lᵖ` composition isometry using representatives. -/
@[simp]
theorem compMeasurePreserving_eq_self_iff {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : Lp E p μ) :
    Lp.compMeasurePreserving T hT g = g ↔ (g : Ω → E) ∘ T =ᵐ[μ] g := by
  constructor
  · intro hg
    simpa only [hg] using (Lp.coeFn_compMeasurePreserving g hT).symm
  · intro hg
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving g hT).trans hg

/-- The fixed space of the identity transformation is all of `Lᵖ`. -/
@[simp]
theorem fixedSpace_id :
    fixedSpace (μ := μ) (𝕜 := 𝕜) (E := E) (p := p) id (MeasurePreserving.id μ) = ⊤ := by
  ext g
  simp

/-- Every observable fixed by `T` is fixed by every iterate of `T`. -/
theorem mem_fixedSpace_iterate {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Lp E p μ} (hg : g ∈ fixedSpace (𝕜 := 𝕜) T hT) (n : ℕ) :
    g ∈ fixedSpace (𝕜 := 𝕜) (T^[n]) (hT.iterate n) := by
  rw [mem_fixedSpace_iff] at hg ⊢
  rw [← Lp.compMeasurePreserving_iterate]
  exact IsFixedPt.iterate hg n

end Generic

section Complete

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [NormedRing 𝕜]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Ω}

/-- The map underlying Mathlib's `Lᵖ` composition isometry is Mathlib's composition operator
`MeasureTheory.Lp.compMeasurePreserving`. This is the bridge between the statements phrased with
the isometry, such as the mean ergodic theorem, and the lemmas about representatives, which are
phrased with `MeasureTheory.Lp.compMeasurePreserving`. Together with Mathlib's simp lemma
`LinearIsometry.coe_toContinuousLinearMap` it also normalizes the continuous linear map the
isometry induces. -/
@[simp]
theorem coe_compMeasurePreservingₗᵢ (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ⇑(Lp.compMeasurePreservingₗᵢ 𝕜 T hT) =
      ⇑(Lp.compMeasurePreserving (E := E) (p := p) T hT) := by
  funext g
  exact compMeasurePreservingₗ_apply T hT g

/-- The fixed space is the equalizer of the continuous `Lᵖ` composition operator and the
identity. -/
theorem fixedSpace_eq_eqLocus (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT =
      (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap.toLinearMap.eqLocus
        (1 : Lp E p μ →L[𝕜] Lp E p μ).toLinearMap := by
  ext g
  rw [mem_fixedSpace_iff, LinearMap.mem_eqLocus]
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    coe_compMeasurePreservingₗᵢ, one_apply_eq_self]

/-- The fixed space is closed in `Lᵖ`. -/
theorem isClosed_fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    IsClosed (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT : Set (Lp E p μ)) := by
  rw [fixedSpace_eq_eqLocus]
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap.isClosed_eqLocus
    (1 : Lp E p μ →L[𝕜] Lp E p μ)

variable [CompleteSpace (Lp E p μ)]

instance fixedSpace.completeSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    CompleteSpace (fixedSpace (𝕜 := 𝕜) (E := E) (p := p) T hT) := by
  rw [fixedSpace_eq_eqLocus]
  infer_instance

end Complete

end TauCeti.Probability
