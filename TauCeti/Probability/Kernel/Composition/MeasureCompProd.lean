/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Pushing the base of a composition-product along a map the kernel factors through

Mathlib's `MeasureTheory.Measure.compProd` records how `μ ⊗ₘ κ` reacts to operations on the
kernel, but not what happens when the *base* measure is pushed forward. In general nothing does:
`(μ ⊗ₘ κ).map (Prod.map f id)` cannot be read off `μ.map f`, because `κ` still sees the finer
information carried by the points of the source. The one case in which it can is exactly the case
in which `κ` itself factors through `f`, and that case is the content of this file.

## Main statements

* `TauCeti.Measure.map_prodMap_compProd_comap` — for `f : W → Y` measurable and `κ : Kernel Y Z`,
  `(μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Measure

variable {W Y Z : Type*} [MeasurableSpace W] [MeasurableSpace Y] [MeasurableSpace Z]

/-- If a kernel factors through a measurable map `f : W → Y`, then pushing the base of the
composition-product forward along `f` gives back the composition-product over the pushed-forward
base: `(μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ`.

Without the factorization hypothesis the left-hand side genuinely depends on more than `μ.map f`,
so the `comap` on the left is not decoration. -/
theorem map_prodMap_compProd_comap (μ : Measure W) [SFinite μ] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] {f : W → Y} (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  have hmap : Measurable (Prod.map f (id : Z → Z)) := hf.prodMap measurable_id
  ext s hs
  rw [MeasureTheory.Measure.map_apply hmap hs,
    MeasureTheory.Measure.compProd_apply (hs.preimage hmap),
    MeasureTheory.Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun w ↦ ?_
  rw [Kernel.comap_apply]
  rfl

end Measure

end TauCeti
