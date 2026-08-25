/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The inverse function theorem with a `C^n` inverse on a whole open set

Mathlib's `ContDiffAt.toOpenPartialHomeomorph` turns a `C^n` map with invertible derivative at a
point into an `OpenPartialHomeomorph`, but `ContDiffAt.to_localInverse` only produces a `C^n`
inverse *at the image point*. Building a partial diffeomorphism of manifolds needs more: the
inverse has to be `C^n` on the whole target.

This file supplies that upgrade. Shrinking the source to the open set where the derivative stays
invertible — invertibility is an open condition by `ContinuousLinearEquiv.isOpen` — makes
`OpenPartialHomeomorph.contDiffAt_symm` applicable at *every* point of the target.

## Main results

* `TauCeti.isOpen_inter_preimage_range_continuousLinearEquiv_fderiv`: on an open set, the points
  where a `C^n` map (`1 ≤ n`) has invertible derivative form an open set.
* `TauCeti.ContDiffOn.exists_openPartialHomeomorph`: a `C^n` map (`1 ≤ n`) on an open set with
  invertible derivative at a point restricts to an `OpenPartialHomeomorph` around that point whose
  inverse is `C^n` on the whole target.

## References

* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The manifold inverse-function theorem".
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {n : WithTop ℕ∞} {g : E → F} {s : Set E} {a : E}

/-- On an open set on which `g` is `C^n` with `1 ≤ n`, the points where the derivative of `g` is a
continuous linear equivalence form an open set: the derivative varies continuously, and the
continuous linear equivalences are open among the continuous linear maps. -/
theorem isOpen_inter_preimage_range_continuousLinearEquiv_fderiv
    (hg : ContDiffOn 𝕂 n g s) (hs : IsOpen s) (hn : 1 ≤ n) :
    IsOpen (s ∩ fderiv 𝕂 g ⁻¹' range ((↑) : (E ≃L[𝕂] F) → E →L[𝕂] F)) :=
  (hg.continuousOn_fderiv_of_isOpen hs hn).isOpen_inter_preimage hs
    ContinuousLinearEquiv.isOpen

/-- **The inverse function theorem, with a `C^n` inverse on the whole target.** A map which is
`C^n` on an open set `s`, with `1 ≤ n`, and whose derivative at `a ∈ s` is a continuous linear
equivalence, coincides on a neighbourhood of `a` with an `OpenPartialHomeomorph` whose source is
contained in `s` and whose inverse is `C^n` on its target. -/
theorem ContDiffOn.exists_openPartialHomeomorph
    (hg : ContDiffOn 𝕂 n g s) (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n)
    {e : E ≃L[𝕂] F} (he : (e : E →L[𝕂] F) = fderiv 𝕂 g a) :
    ∃ Θ : OpenPartialHomeomorph E F, (Θ : E → F) = g ∧ a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      ContDiffOn 𝕂 n Θ.symm Θ.target := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set W := s ∩ fderiv 𝕂 g ⁻¹' range ((↑) : (E ≃L[𝕂] F) → E →L[𝕂] F)
  have hWopen : IsOpen W := isOpen_inter_preimage_range_continuousLinearEquiv_fderiv hg hs hn
  have haW : a ∈ W := ⟨ha, e, he⟩
  -- Every point of `W` has an invertible derivative, witnessed by `HasFDerivAt`.
  have hderiv : ∀ y ∈ W, ∃ e' : E ≃L[𝕂] F, HasFDerivAt g (e' : E →L[𝕂] F) y := by
    rintro y ⟨hy, e', he'⟩
    exact ⟨e', he' ▸ ((hg.differentiableOn hn0).differentiableAt (hs.mem_nhds hy)).hasFDerivAt⟩
  have hgAt : ∀ y ∈ s, ContDiffAt 𝕂 n g y := fun y hy => hg.contDiffAt (hs.mem_nhds hy)
  obtain ⟨e₀, he₀⟩ := hderiv a haW
  refine ⟨((hgAt a ha).toOpenPartialHomeomorph g he₀ hn0).restrOpen W hWopen, rfl, ?_, ?_, ?_⟩
  · exact ⟨(hgAt a ha).mem_toOpenPartialHomeomorph_source he₀ hn0, haW⟩
  · exact fun y hy => (hy.2 : y ∈ W).1
  · intro w hw
    set Θ := ((hgAt a ha).toOpenPartialHomeomorph g he₀ hn0).restrOpen W hWopen
    have hmem : Θ.symm w ∈ W := (Θ.map_target hw).2
    obtain ⟨e', he'⟩ := hderiv _ hmem
    exact (Θ.contDiffAt_symm hw he' (hgAt _ hmem.1)).contDiffWithinAt

end TauCeti
