/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Analysis.Fredholm.LevelSet.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth parametrizations of regular Fredholm level sets

At a point where a map between Banach spaces has surjective derivative with complemented kernel,
`TauCeti.levelSetChart` identifies its level set locally with that kernel. This file proves that
the inverse chart is, at the chart origin, as smooth as the original map, and computes its
derivative there: it is the canonical inclusion of the kernel into the ambient space.

The smoothness statement is Tau Ceti's
`HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm`, restricted to
the slice `{c} × ker f'` on which the chart is the implicit function. The derivative statement is
Mathlib's `HasStrictFDerivAt.to_implicitFunctionOfComplemented`, transported along the chart. The
geometric organization follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Appendix A.3.

Together with `ContinuousLinearMap.IsFredholm.closedComplemented_ker_coprod`, which supplies the
complemented kernel of a surjective linearization whose fixed-parameter part is Fredholm, these
are the pointwise smoothness and derivative computation from which the smooth local input to the
parameter projection and Sard--Smale arguments in the analytic Heegaard Floer roadmap is to be
assembled; smooth compatibility of the charts of a whole level set is not proved here.

## Main results

* `TauCeti.contDiffAt_coe_levelSetChart_symm`: the inverse regular-level-set chart, included into
  the ambient Banach space, is smooth at its origin.
* `TauCeti.hasStrictFDerivAt_coe_levelSetChart_symm`: its derivative there is the inclusion of the
  derivative's kernel.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {K E F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E} {c : F}

/-- The inverse regular-level-set chart, followed by the inclusion into the ambient space, is as
smooth as the defining equation at the chart origin. -/
theorem contDiffAt_coe_levelSetChart_symm {n : ℕ∞ω} (hf : HasStrictFDerivAt f f' a)
    (hcont : ContDiffAt K n f a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    ContDiffAt K n
      (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) 0 := by
  subst c
  have hinverse :=
    hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm hcont hf' hker
  have hslice : ContDiffAt K n
      (fun k ↦ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm
        (f a, k)) 0 := by
    have hinner : ContDiffAt K n (fun k : f'.ker ↦ (f a, k)) 0 :=
      contDiffAt_const.prodMk contDiffAt_id
    simpa only [Function.comp_def] using hinverse.comp 0 hinner
  apply hslice.congr_of_eventuallyEq
  filter_upwards [(levelSetChart hf hf' hker rfl).open_target.mem_nhds
    (mem_levelSetChart_target hf hf' hker rfl)] with k hk
  exact levelSetChart_symm_apply hf hf' hker rfl hk

/-- The derivative at the origin of the inverse regular-level-set chart, included into the
ambient space, is the canonical inclusion of the derivative's kernel. -/
theorem hasStrictFDerivAt_coe_levelSetChart_symm (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (ha : f a = c) :
    HasStrictFDerivAt
      (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E))
      f'.ker.subtypeL 0 := by
  subst c
  refine (hf.to_implicitFunctionOfComplemented hf' hker).congr_of_eventuallyEq ?_
  filter_upwards [(levelSetChart hf hf' hker rfl).open_target.mem_nhds
    (mem_levelSetChart_target hf hf' hker rfl),
    hf.eventually_implicitFunctionOfComplemented_eq hf' hker] with k hk hbridge
  rw [levelSetChart_symm_apply hf hf' hker rfl hk, hbridge]

end TauCeti

end
