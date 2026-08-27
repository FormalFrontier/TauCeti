/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Fredholm.LevelSet.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth parametrizations of regular Fredholm level sets

At a point where a map between Banach spaces has surjective derivative with complemented kernel,
`TauCeti.levelSetChart` identifies its level set locally with that kernel. This file proves that
the inverse chart is as smooth as the original map and computes its derivative at the chart
origin: it is the canonical inclusion of the kernel into the ambient space.

The smoothness statement runs through Mathlib's smooth inverse theorem for an
`OpenPartialHomeomorph`. The relevant coordinate change is exactly the map used by Mathlib's
complemented-kernel implicit function theorem: `x ↦ (f x, P (x - a))`, where `P` is a continuous
projection onto the kernel. The derivative statement is Mathlib's
`HasStrictFDerivAt.to_implicitFunctionOfComplemented`, transported along the chart. The geometric
organization follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
Appendix A.3.

Together with `ContinuousLinearMap.IsFredholm.closedComplemented_ker_coprod`, which supplies the
complemented kernel of a surjective linearization whose fixed-parameter part is Fredholm, these
are the smooth local input to the parameter projection and Sard--Smale arguments in the analytic
Heegaard Floer roadmap.

## Main results

* `HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm`: the inverse
  complemented-kernel implicit-function homeomorphism is as smooth as the equation.
* `TauCeti.contDiffAt_coe_levelSetChart_symm`: the inverse regular-level-set chart, included into
  the ambient Banach space, is smooth at its origin.
* `TauCeti.hasStrictFDerivAt_coe_levelSetChart_symm`: its derivative there is the inclusion of the
  derivative's kernel.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace HasStrictFDerivAt

variable {K E F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E}

/-- Mathlib's complemented-kernel implicit-function homeomorphism is as smooth as the original
map at its base point. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hcont : ContDiffAt K n f a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ContDiffAt K n (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker) a := by
  have hcoord : ContDiffAt K n (fun x ↦ (f x, Classical.choose hker (x - a))) a := by
    fun_prop
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [] with x
  exact hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker x

/-- The inverse of Mathlib's complemented-kernel implicit-function homeomorphism is as smooth as
the original map at the image of the base point. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hcont : ContDiffAt K n f a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ContDiffAt K n
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0) := by
  let e := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker
  -- the derivative of the coordinate change, as the equivalence `x ↦ (f' x, P x)`
  let L : E ≃L[K] F × f'.ker :=
    f'.equivProdOfSurjectiveOfIsCompl (Classical.choose hker) hf'
      (LinearMap.range_eq_of_proj (Classical.choose_spec hker))
      (LinearMap.isCompl_of_proj (Classical.choose_spec hker))
  have hinv : e.symm (f a, 0) = a := by
    rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_self hf' hker]
    exact e.left_inv (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)
  refine e.contDiffAt_symm (f₀' := L)
    (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker) ?_ ?_
  · rw [hinv]
    have hcoord : HasStrictFDerivAt (fun x ↦ (f x, Classical.choose hker (x - a)))
        (f'.prod (Classical.choose hker)) a :=
      hf.prodMk <| (Classical.choose hker).hasStrictFDerivAt.comp a
        ((hasStrictFDerivAt_id a).sub_const a)
    have hL : (L : E →L[K] F × f'.ker) = f'.prod (Classical.choose hker) := rfl
    rw [hL]
    refine HasStrictFDerivAt.hasFDerivAt (hcoord.congr_of_eventuallyEq ?_)
    filter_upwards [] with x
    exact (hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker x).symm
  · rw [hinv]
    exact hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented hcont hf' hker

/-- Mathlib names the complemented-kernel implicit function twice, once as
`HasStrictFDerivAt.implicitFunctionOfComplemented` and once as the inverse of
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`. Neither definition is
`@[expose]`d, so the two spellings are identified near the base point through
`HasStrictFDerivAt.eq_implicitFunctionOfComplemented` rather than by unfolding. -/
private theorem eventually_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ k : f'.ker in 𝓝 0,
      hf.implicitFunctionOfComplemented f f' hf' hker (f a) k =
        (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, k) := by
  have htarget : (f a, (0 : f'.ker)) ∈
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker
  have hinv :
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0) = a := by
    rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_self hf' hker]
    exact (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)
  have hslice : ContinuousAt (fun k : f'.ker ↦ (f a, k)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hsymm : ContinuousAt
      (fun k : f'.ker ↦
        (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, k)) 0 :=
    ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).continuousAt_symm
      htarget).comp hslice
  have hmem : ∀ᶠ k : f'.ker in 𝓝 0,
      (f a, k) ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target :=
    hslice.preimage_mem_nhds
      ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).open_target.mem_nhds
        htarget)
  have hnear := hsymm.preimage_mem_nhds
    (show {x | hf.implicitFunctionOfComplemented f f' hf' hker (f x)
        ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker) x).snd = x} ∈
      𝓝 ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0)) by
      rw [hinv]
      exact hf.eq_implicitFunctionOfComplemented hf' hker)
  filter_upwards [hmem, hnear] with k hk hkey
  have hright := (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).right_inv hk
  have hfst : f ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm
      (f a, k)) = f a :=
    (hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker _).symm.trans
      (congrArg Prod.fst hright)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hkey
  rw [hright, hfst] at hkey
  exact hkey

end HasStrictFDerivAt

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
