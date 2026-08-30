/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the complemented-kernel implicit function theorem

Let `f : E → F` be a map between Banach spaces which is strictly differentiable at `a` with
surjective derivative `f'` whose kernel is complemented. Mathlib's
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented` straightens `f` near `a`: it is
the homeomorphism `x ↦ (f x, P (x - a))` onto a neighbourhood of `(f a, 0)` in `F × ker f'`, where
`P` is the continuous projection onto `ker f'` chosen by the complementation hypothesis, and its
inverse restricted to the slice `{f a} × ker f'` is the implicit function of `f`.

Mathlib records the strict differentiability of that homeomorphism and of its inverse. This file
adds the `C^n` statements, obtained from Mathlib's smooth inverse theorem for an
`OpenPartialHomeomorph`, `OpenPartialHomeomorph.contDiffAt_symm`, and the value of the inverse
homeomorphism at `(f a, 0)`.

Mathlib's `ImplicitFunctionData.contDiffAt_implicitFunction` is a `C^n` implicit function theorem
for the same data. It is not usable here: it is stated over `[RCLike 𝕜]` and assumes `n ≠ 0`,
whereas the results below hold over an arbitrary `[NontriviallyNormedField K]` — the generality in
which the underlying homeomorphism, and its consumer `TauCeti.levelSetChart`, are stated — and for
every `n : ℕ∞ω`. Consumers that are content with `RCLike` scalars and `n ≠ 0` should prefer
Mathlib's lemma.

## Main results

* `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_symm_self`: the inverse
  homeomorphism sends `(f a, 0)` back to the base point `a`.
* `HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented`: the
  complemented-kernel implicit-function homeomorphism is as smooth as the equation, at every point
  where the equation is.
* `HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm`: so is its
  inverse, at the image `(f a, 0)` of the base point.
* `HasStrictFDerivAt.eventually_implicitFunctionOfComplemented_eq`: near `0`, Mathlib's two
  spellings of the implicit function agree.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace HasStrictFDerivAt

variable {K E F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E}

/-- The complemented-kernel implicit-function homeomorphism is the coordinate map
`x ↦ (f x, P (x - a))`, as an equality of functions rather than pointwise. -/
private theorem coe_implicitToOpenPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ⇑(hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker) =
      fun x ↦ (f x, Classical.choose hker (x - a)) :=
  funext (hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker)

/-- The inverse of Mathlib's complemented-kernel implicit-function homeomorphism sends the image
`(f a, 0)` of the base point back to the base point. -/
@[simp]
theorem implicitToOpenPartialHomeomorphOfComplemented_symm_self (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0) = a := by
  rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_self hf' hker]
  exact (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
    (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

/-- Mathlib's complemented-kernel implicit-function homeomorphism is as smooth as the original map
at every point where the original map is smooth. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented {n : ℕ∞ω} {x : E}
    (hf : HasStrictFDerivAt f f' a) (hcont : ContDiffAt K n f x)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ContDiffAt K n (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker) x := by
  rw [hf.coe_implicitToOpenPartialHomeomorphOfComplemented hf' hker]
  fun_prop

/-- The inverse of Mathlib's complemented-kernel implicit-function homeomorphism is as smooth as
the original map at the image of the base point. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hcont : ContDiffAt K n f a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ContDiffAt K n
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0) := by
  set e := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker with he
  -- the derivative of the coordinate change, as the equivalence `x ↦ (f' x, P x)`
  let L : E ≃L[K] F × f'.ker :=
    f'.equivProdOfSurjectiveOfIsCompl (Classical.choose hker) hf'
      (LinearMap.range_eq_of_proj (Classical.choose_spec hker))
      (LinearMap.isCompl_of_proj (Classical.choose_spec hker))
  refine e.contDiffAt_symm (f₀' := L)
    (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker) ?_ ?_
  · rw [he, hf.implicitToOpenPartialHomeomorphOfComplemented_symm_self hf' hker,
      hf.coe_implicitToOpenPartialHomeomorphOfComplemented hf' hker]
    have hL : (L : E →L[K] F × f'.ker) = f'.prod (Classical.choose hker) :=
      ContinuousLinearMap.ext fun x ↦ by
        simp [L, ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply]
    rw [hL]
    exact (hf.prodMk <| (Classical.choose hker).hasStrictFDerivAt.comp a
      ((hasStrictFDerivAt_id a).sub_const a)).hasFDerivAt
  · rw [he, hf.implicitToOpenPartialHomeomorphOfComplemented_symm_self hf' hker]
    exact hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented hcont hf' hker

/- Mathlib names the complemented-kernel implicit function twice, once as
`HasStrictFDerivAt.implicitFunctionOfComplemented` and once as the inverse of
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`. The two are equal by
definition, but neither definition is `@[expose]`d, so downstream they can only be identified
through Mathlib's own API, `HasStrictFDerivAt.eq_implicitFunctionOfComplemented`; that lemma is
itself eventual, which is why the statement below is too. -/

/-- Near `0`, the implicit function of `f` at the value `f a` agrees on the slice
`{f a} × ker f'` with the inverse of the complemented-kernel implicit-function homeomorphism. -/
theorem eventually_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ k : f'.ker in 𝓝 0,
      hf.implicitFunctionOfComplemented f f' hf' hker (f a) k =
        (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, k) := by
  set e := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker with he
  have htarget : (f a, (0 : f'.ker)) ∈ e.target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker
  have hslice : ContinuousAt (fun k : f'.ker ↦ (f a, k)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hsymm : ContinuousAt (fun k : f'.ker ↦ e.symm (f a, k)) 0 :=
    (e.continuousAt_symm htarget).comp hslice
  have hmem : ∀ᶠ k : f'.ker in 𝓝 0, (f a, k) ∈ e.target :=
    hslice.preimage_mem_nhds (e.open_target.mem_nhds htarget)
  have himplicit :
      {x | hf.implicitFunctionOfComplemented f f' hf' hker (f x) (e x).snd = x} ∈
        𝓝 (e.symm (f a, 0)) := by
    rw [he, hf.implicitToOpenPartialHomeomorphOfComplemented_symm_self hf' hker]
    exact hf.eq_implicitFunctionOfComplemented hf' hker
  have hnear := hsymm.preimage_mem_nhds himplicit
  filter_upwards [hmem, hnear] with k hk hkey
  have hright := e.right_inv hk
  have hfst : f (e.symm (f a, k)) = f a :=
    (hf.implicitToOpenPartialHomeomorphOfComplemented_fst hf' hker _).symm.trans
      (congrArg Prod.fst hright)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hkey
  rw [hright, hfst] at hkey
  exact hkey

end HasStrictFDerivAt

end
