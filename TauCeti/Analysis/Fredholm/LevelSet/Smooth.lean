/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Fredholm.LevelSet.Basic
public import TauCeti.Analysis.Fredholm.UniversalLevelSet
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Smooth parametrizations of regular Fredholm level sets

At a point where a map between Banach spaces has surjective derivative with complemented kernel,
`TauCeti.levelSetChart` identifies its level set locally with that kernel. This file proves that
the inverse chart is as smooth as the original map and computes its derivative at the chart
origin: it is the canonical inclusion of the kernel into the ambient space.

For a parametrized equation `f : E × Λ → F`, the fixed-parameter derivative need only be
Fredholm. If the total derivative is surjective, then
`ContinuousLinearMap.IsFredholm.closedComplemented_ker_coprod` supplies the complement required by
the smooth level-set theorem. The resulting universal-level-set corollaries are the smooth local
input to the parameter projection and Sard--Smale arguments in the analytic Heegaard Floer
roadmap.

The proof uses Mathlib's smooth inverse theorem for an `OpenPartialHomeomorph`. The relevant
coordinate change is exactly the map used by Mathlib's complemented-kernel implicit function
theorem: `x ↦ (f x, P (x - a))`, where `P` is a continuous projection onto the kernel. The
geometric organization follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Appendix A.3.

## Main results

* `HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm`: the inverse
  complemented-kernel implicit-function homeomorphism is as smooth as the equation.
* `TauCeti.contDiffAt_coe_levelSetChart_symm`: the inverse regular-level-set chart, included into
  the ambient Banach space, is smooth at its origin.
* `TauCeti.hasStrictFDerivAt_coe_levelSetChart_symm`: its derivative there is the inclusion of the
  derivative's kernel.
* `TauCeti.contDiffAt_coe_universalLevelSetChart_symm` and
  `TauCeti.hasStrictFDerivAt_coe_universalLevelSetChart_symm`: the corresponding conclusions for
  a universal Fredholm family.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace ContinuousLinearMap

variable {K E F : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E}

/-- The continuous linear equivalence which is the derivative of the complemented-kernel
implicit-function coordinate change. -/
noncomputable def complementedKernelEquiv (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : E ≃L[K] F × f'.ker :=
  f'.equivProdOfSurjectiveOfIsCompl (Classical.choose hker) hf'
    (LinearMap.range_eq_of_proj (Classical.choose_spec hker))
    (LinearMap.isCompl_of_proj (Classical.choose_spec hker))

/-- The complemented coordinate equivalence evaluates as the derivative paired with the chosen
projection onto its kernel. -/
@[simp]
theorem complementedKernelEquiv_apply (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) (x : E) :
    f'.complementedKernelEquiv hf' hker x = (f' x, Classical.choose hker x) :=
  ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply _ _ _ _

/-- Restricting the inverse complemented-kernel equivalence to the kernel coordinate gives the
canonical inclusion of the kernel into the ambient space. -/
@[simp]
theorem complementedKernelEquiv_symm_comp_inr (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    ((f'.complementedKernelEquiv hf' hker).symm : F × f'.ker →L[K] E).comp
        (ContinuousLinearMap.inr K F f'.ker) = f'.ker.subtypeL := by
  ext k
  apply (f'.complementedKernelEquiv hf' hker).injective
  have hleft : f'.complementedKernelEquiv hf' hker
      (((f'.complementedKernelEquiv hf' hker).symm : F × f'.ker →L[K] E) (0, k)) =
      (0, k) := (f'.complementedKernelEquiv hf' hker).apply_symm_apply (0, k)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hleft,
    complementedKernelEquiv_apply]
  exact Prod.ext k.property.symm (Classical.choose_spec hker k).symm

end ContinuousLinearMap

namespace HasStrictFDerivAt

variable {K E F : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E}

/-- The derivative at the base point of Mathlib's complemented-kernel implicit-function
homeomorphism is the equivalence pairing `f'` with the chosen projection onto `ker f'`. -/
theorem hasStrictFDerivAt_implicitToOpenPartialHomeomorphOfComplemented
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker)
      (f'.complementedKernelEquiv hf' hker : E →L[K] F × f'.ker) a := by
  have hcoord : HasStrictFDerivAt
      (fun x ↦ (f x, Classical.choose hker (x - a)))
      (f'.prod (Classical.choose hker)) a :=
    hf.prodMk <| (Classical.choose hker).hasStrictFDerivAt.comp a
      ((hasStrictFDerivAt_id a).sub_const a)
  have hequiv : (f'.complementedKernelEquiv hf' hker : E →L[K] F × f'.ker) =
      f'.prod (Classical.choose hker) := by
    apply ContinuousLinearMap.ext
    intro x
    exact f'.complementedKernelEquiv_apply hf' hker x
  rw [hequiv]
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [] with x
  exact (hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker x).symm

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
  have hsource : a ∈ e.source :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker
  have htarget : (f a, (0 : f'.ker)) ∈ e.target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker
  have hinv : e.symm (f a, 0) = a := by
    rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_self hf' hker]
    exact e.left_inv hsource
  apply e.contDiffAt_symm (f₀' := f'.complementedKernelEquiv hf' hker) htarget
  · rw [hinv]
    exact (hf.hasStrictFDerivAt_implicitToOpenPartialHomeomorphOfComplemented hf' hker).hasFDerivAt
  · rw [hinv]
    exact hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented hcont hf' hker

/-- The inverse complemented-kernel implicit-function homeomorphism has derivative the inverse
coordinate equivalence at the image of the base point. -/
theorem hasStrictFDerivAt_implicitToOpenPartialHomeomorphOfComplemented_symm
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm
      ((f'.complementedKernelEquiv hf' hker).symm : F × f'.ker →L[K] E) (f a, 0) := by
  let e := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker
  have hsource : a ∈ e.source :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker
  have htarget : (f a, (0 : f'.ker)) ∈ e.target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker
  have hinv : e.symm (f a, 0) = a := by
    rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_self hf' hker]
    exact e.left_inv hsource
  apply e.hasStrictFDerivAt_symm htarget
  rw [hinv]
  exact hf.hasStrictFDerivAt_implicitToOpenPartialHomeomorphOfComplemented hf' hker

end HasStrictFDerivAt

namespace TauCeti

variable {K E F : Type*} [RCLike K]
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
  have hinverse :=
    HasStrictFDerivAt.hasStrictFDerivAt_implicitToOpenPartialHomeomorphOfComplemented_symm
      hf hf' hker
  have hinner : HasStrictFDerivAt (fun k : f'.ker ↦ (f a, k))
      (ContinuousLinearMap.inr K F f'.ker) 0 :=
    (hasStrictFDerivAt_const (x := (0 : f'.ker)) (c := f a)).prodMk
      (hasStrictFDerivAt_id 0)
  have hslice := hinverse.comp 0 hinner
  rw [f'.complementedKernelEquiv_symm_comp_inr hf' hker] at hslice
  apply hslice.congr_of_eventuallyEq
  filter_upwards [(levelSetChart hf hf' hker rfl).open_target.mem_nhds
    (mem_levelSetChart_target hf hf' hker rfl)] with k hk
  exact (levelSetChart_symm_apply hf hf' hker rfl hk).symm

section Universal

variable {E₀ Λ : Type*}
variable [NormedAddCommGroup E₀] [NormedSpace K E₀] [CompleteSpace E₀]
variable [NormedAddCommGroup Λ] [NormedSpace K Λ] [CompleteSpace Λ]
variable {g : E₀ × Λ → F} {D₁ : E₀ →L[K] F} {D₂ : Λ →L[K] F} {p : E₀ × Λ} {d : F}

/-- For a universal equation, a Fredholm fixed-parameter derivative and a surjective total
derivative make the inverse level-set chart smooth at its origin. -/
theorem contDiffAt_coe_universalLevelSetChart_symm {n : ℕ∞ω}
    (hg : HasStrictFDerivAt g (D₁.coprod D₂) p) (hcont : ContDiffAt K n g p)
    (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) (hp : g p = d) :
    ContDiffAt K n
      (fun k ↦ (((levelSetChart hg (LinearMap.range_eq_top.2 hD)
        (hD₁.closedComplemented_ker_coprod hD) hp).symm k : ↥{x | g x = d}) : E₀ × Λ)) 0 :=
  contDiffAt_coe_levelSetChart_symm hg hcont (LinearMap.range_eq_top.2 hD)
    (hD₁.closedComplemented_ker_coprod hD) hp

/-- For a universal equation, the derivative of the inverse level-set chart is the inclusion of
the kernel of the total linearization. -/
theorem hasStrictFDerivAt_coe_universalLevelSetChart_symm
    (hg : HasStrictFDerivAt g (D₁.coprod D₂) p)
    (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) (hp : g p = d) :
    HasStrictFDerivAt
      (fun k ↦ (((levelSetChart hg (LinearMap.range_eq_top.2 hD)
        (hD₁.closedComplemented_ker_coprod hD) hp).symm k : ↥{x | g x = d}) : E₀ × Λ))
      (D₁.coprod D₂).ker.subtypeL 0 :=
  hasStrictFDerivAt_coe_levelSetChart_symm hg (LinearMap.range_eq_top.2 hD)
    (hD₁.closedComplemented_ker_coprod hD) hp

end Universal

end TauCeti

end
