module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Pointwise products of `L²` functions on a finite product measure

For a finite family of σ-finite measures `μ i` and `L²(μ i)` functions `f i`, the pointwise product
`x ↦ ∏ i, f i (x i)` belongs to `L²(Measure.pi μ)`, and the assignment factors the inner product as
a tensor. This is the `Fintype`-indexed analogue of `TauCeti.L2prodMul`, and Part B3/D of the
`OrthogonalL2Bases` roadmap.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]

/-- The pointwise product `x ↦ ∏ i, f i (x i)` of `L²` functions is `L²` for the product measure. -/
theorem memLp_pi_prod {f : ∀ i, α i → 𝕜} (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x : ∀ i, α i => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hmeas : AEStronglyMeasurable (fun x : ∀ i, α i => ∏ i, f i (x i)) (Measure.pi μ) :=
    Finset.aestronglyMeasurable_fun_prod (f := fun i (x : ∀ j, α j) => f i (x i)) _ fun i _ =>
      (hf i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (Integrable.fintype_prod_dep
    (fun i => (memLp_two_iff_integrable_sq_norm (hf i).1).1 (hf i))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_prod, Finset.prod_pow]

end TauCeti
