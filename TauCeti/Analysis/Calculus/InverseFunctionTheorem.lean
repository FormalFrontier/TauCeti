/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# The inverse function theorem with a `C^n` inverse on a whole open set

Mathlib's `ContDiffAt.toOpenPartialHomeomorph` turns a `C^n` map with invertible derivative at a
point into an `OpenPartialHomeomorph`, but `ContDiffAt.to_localInverse` only produces a `C^n`
inverse *at the image point*: `OpenPartialHomeomorph.contDiffAt_symm` needs an invertible
derivative at the point one inverts around, and invertibility is assumed at the base point alone.
Building a partial diffeomorphism of manifolds, or comparing two implicit-function charts of a
level set, needs more: the inverse has to be `C^n` on the whole target.

The invertibility does in fact persist. Mathlib's construction goes through
`ApproximatesLinearOn`: the source of the homeomorphism is an open set on which the map
approximates its derivative `L` at the base point with a constant `c` strictly below `‖L⁻¹‖⁻¹`.
On such a set every Fréchet derivative of the map is within `c` of `L` in norm, hence is still
invertible by `ContinuousLinearMap.isInvertible_of_norm_sub_le_half`. This file extracts that
estimate and runs Mathlib's smooth inverse function theorem at every point of the target.

Two forms are given. The first is about Mathlib's own homeomorphism, over an arbitrary
nontrivially normed field: strict differentiability alone makes derivative invertibility persist,
while inverse `C^n` regularity also assumes the corresponding `C^n` regularity of the map. It is
the form a consumer that cannot choose its homeomorphism — such as the implicit-function chart of
a level set — needs. The second packages the classical statement over `ℝ` or `ℂ`: a `C^n` map with
invertible derivative at a point of an open set `s` restricts to an `OpenPartialHomeomorph` inside
`s` whose inverse is `C^n` on its target.

## Main results

* `ApproximatesLinearOn.norm_sub_le_of_hasFDerivAt`: on a set where `f` approximates `L` with
  constant `c`, every derivative of `f` at an interior point is within `c` of `L`.
* `HasStrictFDerivAt.approximatesLinearOn_toOpenPartialHomeomorph_source`: the source of the
  inverse function theorem's homeomorphism carries the approximation estimate its construction
  chose.
* `HasStrictFDerivAt.isInvertible_of_mem_toOpenPartialHomeomorph_source`: hence the derivative of
  `f` is invertible at every point of that source, not only at the base point.
* `HasStrictFDerivAt.contDiffAt_toOpenPartialHomeomorph_symm` and
  `HasStrictFDerivAt.contDiffOn_toOpenPartialHomeomorph_symm`: the local inverse is `C^n` at every
  point of the target, and hence on the target.
* `TauCeti.ContDiffOn.exists_openPartialHomeomorph`: a `C^n` map (`1 ≤ n`) on an open set with
  invertible derivative at a point restricts to an `OpenPartialHomeomorph` around that point whose
  inverse is `C^n` on the whole target.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The manifold inverse-function theorem".
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff NNReal Topology

section Approximation

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a set on which `f` approximates the continuous linear map `L` with constant `c`, every
Fréchet derivative of `f` at an interior point is within `c` of `L` in operator norm. -/
theorem ApproximatesLinearOn.norm_sub_le_of_hasFDerivAt {f : E → F} {L A : E →L[𝕜] F} {s : Set E}
    {c : ℝ≥0} (hf : ApproximatesLinearOn f L s c) {x : E} (hs : s ∈ 𝓝 x)
    (hA : HasFDerivAt f A x) : ‖A - L‖ ≤ c := by
  exact (hA.sub L.hasFDerivAt).le_of_lipschitzOn hs hf.lipschitzOnWith

namespace HasStrictFDerivAt

variable [CompleteSpace E] {f : E → F} {L : E ≃L[𝕜] F} {a : E}

/-- On the source of the homeomorphism built by the inverse function theorem, `f` approximates its
derivative at the base point with the constant `‖L⁻¹‖⁻¹ / 2` that the construction chose. -/
theorem approximatesLinearOn_toOpenPartialHomeomorph_source
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ApproximatesLinearOn f (L : E →L[𝕜] F) (hf.toOpenPartialHomeomorph f).source
      (‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  have h := (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
  convert h using 1
  exact ApproximatesLinearOn.toOpenPartialHomeomorph_source ..

/-- **The derivative of `f` is invertible throughout the inverse-function neighbourhood.**
Invertibility of the derivative is assumed at the base point only, but it propagates to every
point of the source of `HasStrictFDerivAt.toOpenPartialHomeomorph`. -/
theorem isInvertible_of_mem_toOpenPartialHomeomorph_source
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) {x : E}
    (hx : x ∈ (hf.toOpenPartialHomeomorph f).source) {A : E →L[𝕜] F} (hA : HasFDerivAt f A x) :
    A.IsInvertible := by
  refine ContinuousLinearMap.isInvertible_of_norm_sub_le_half L ?_
  have hbound := hf.approximatesLinearOn_toOpenPartialHomeomorph_source.norm_sub_le_of_hasFDerivAt
    ((hf.toOpenPartialHomeomorph f).open_source.mem_nhds hx) hA
  rwa [← NNReal.coe_le_coe, coe_nnnorm]

/-- **The local inverse of the inverse function theorem is `C^n` at every point of its target.**
The original inverse-function hypotheses provide an invertible derivative only at the base point.
Here we prove the missing invertibility throughout the constructed source, then apply Mathlib's
`OpenPartialHomeomorph.contDiffAt_symm` pointwise on the target. -/
theorem contDiffAt_toOpenPartialHomeomorph_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) {y : F}
    (hy : y ∈ (hf.toOpenPartialHomeomorph f).target)
    (hcont : ContDiffAt 𝕜 n f ((hf.toOpenPartialHomeomorph f).symm y)) :
    ContDiffAt 𝕜 n (hf.toOpenPartialHomeomorph f).symm y := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact contDiffAt_zero.2 ⟨_, (hf.toOpenPartialHomeomorph f).open_target.mem_nhds hy,
      (hf.toOpenPartialHomeomorph f).continuousOn_symm⟩
  set x := (hf.toOpenPartialHomeomorph f).symm y with hx
  have hxs : x ∈ (hf.toOpenPartialHomeomorph f).source :=
    (hf.toOpenPartialHomeomorph f).map_target hy
  have hA : HasFDerivAt f (fderiv 𝕜 f x) x := (hcont.differentiableAt hn).hasFDerivAt
  obtain ⟨A, hA'⟩ := hf.isInvertible_of_mem_toOpenPartialHomeomorph_source hxs hA
  refine (hf.toOpenPartialHomeomorph f).contDiffAt_symm (f₀' := A) hy ?_ ?_
  · simpa [hA'] using hA
  · simpa using hcont

/-- **The inverse function theorem produces a `C^n` inverse.** If `f` is `C^n` on the source of the
homeomorphism built by the inverse function theorem, then the inverse is `C^n` on the target. -/
theorem contDiffOn_toOpenPartialHomeomorph_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    (hcont : ContDiffOn 𝕜 n f (hf.toOpenPartialHomeomorph f).source) :
    ContDiffOn 𝕜 n (hf.toOpenPartialHomeomorph f).symm (hf.toOpenPartialHomeomorph f).target := by
  intro y hy
  refine (hf.contDiffAt_toOpenPartialHomeomorph_symm hy ?_).contDiffWithinAt
  exact hcont.contDiffAt ((hf.toOpenPartialHomeomorph f).open_source.mem_nhds
    ((hf.toOpenPartialHomeomorph f).map_target hy))

end HasStrictFDerivAt

end Approximation

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {n : WithTop ℕ∞} {g : E → F} {s : Set E} {a : E}

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
  have hgAt : ∀ y ∈ s, ContDiffAt 𝕂 n g y := fun y hy => hg.contDiffAt (hs.mem_nhds hy)
  have he₀ : HasFDerivAt g (e : E →L[𝕂] F) a :=
    he ▸ ((hg.differentiableOn hn0).differentiableAt (hs.mem_nhds ha)).hasFDerivAt
  have hstrict := (hgAt a ha).hasStrictFDerivAt' he₀ hn0
  refine ⟨((hgAt a ha).toOpenPartialHomeomorph g he₀ hn0).restrOpen s hs, rfl,
    ⟨(hgAt a ha).mem_toOpenPartialHomeomorph_source he₀ hn0, ha⟩, fun y hy => hy.2, ?_⟩
  intro w hw
  exact (hstrict.contDiffAt_toOpenPartialHomeomorph_symm hw.1 (hgAt _ hw.2)).contDiffWithinAt

end TauCeti

end

end
