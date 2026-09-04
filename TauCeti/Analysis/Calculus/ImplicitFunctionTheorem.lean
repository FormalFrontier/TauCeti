/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
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

Smoothness of the inverse at a point of the target needs the derivative of the coordinate map to
be invertible there. At the base point that is the hypothesis of the theorem; away from it, it is
supplied by `TauCeti.Analysis.Calculus.InverseFunctionTheorem`, on the open neighbourhood
`HasStrictFDerivAt.implicitCoordSource` of the base point that the inverse function theorem itself
produced. So the implicit function is `C^n` on a whole neighbourhood of the origin of the slice,
not only at the origin: enough to compare two implicit-function charts smoothly, which is what a
manifold structure on a level set asks for.

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
* `ContinuousLinearMap.implicitCoordEquiv`: the derivative `x ↦ (f' x, P x)` of the coordinate
  map, as a continuous linear equivalence.
* `HasStrictFDerivAt.implicitCoordSource`: an open neighbourhood of the base point on which the
  derivative of the coordinate map stays invertible.
* `HasStrictFDerivAt.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem`: the
  inverse homeomorphism is `C^n` at every point of the target coming from that neighbourhood.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace ContinuousLinearMap

variable {K E F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- The derivative at the base point of the implicit-function coordinate map
`x ↦ (f x, P (x - a))`, as a continuous linear equivalence `E ≃L[K] F × ker f'`: it is
`x ↦ (f' x, P x)`, where `P` is the projection onto `ker f'` chosen by the complementation
hypothesis. -/
noncomputable def implicitCoordEquiv (f' : E →L[K] F) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : E ≃L[K] F × f'.ker :=
  f'.equivProdOfSurjectiveOfIsCompl (Classical.choose hker) hf'
    (LinearMap.range_eq_of_proj (Classical.choose_spec hker))
    (LinearMap.isCompl_of_proj (Classical.choose_spec hker))

@[simp]
theorem coe_implicitCoordEquiv (f' : E →L[K] F) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    (f'.implicitCoordEquiv hf' hker : E →L[K] F × f'.ker) = f'.prod (Classical.choose hker) :=
  ContinuousLinearMap.ext fun x ↦ by
    simp [implicitCoordEquiv, ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply]

end ContinuousLinearMap

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

/-- The implicit-function coordinate map `x ↦ (f x, P (x - a))` is strictly differentiable at the
base point, with derivative the equivalence `ContinuousLinearMap.implicitCoordEquiv`. -/
theorem hasStrictFDerivAt_implicitCoord (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt (fun x ↦ (f x, Classical.choose hker (x - a)))
      (f'.implicitCoordEquiv hf' hker : E →L[K] F × f'.ker) a := by
  rw [ContinuousLinearMap.coe_implicitCoordEquiv]
  exact hf.prodMk ((Classical.choose hker).hasStrictFDerivAt.comp a
    ((hasStrictFDerivAt_id a).sub_const a))

/-- **The inverse of the implicit-function homeomorphism is `C^n` wherever the coordinate map has
invertible derivative.** Mathlib's `OpenPartialHomeomorph.contDiffAt_symm` asks for an invertible
derivative at the point one inverts around; `A` below is the derivative of the equation there, and
`(A, P)` is the derivative of the coordinate map. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_isInvertible {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented)
    {y : F × f'.ker}
    (hy : y ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y))
    (hAinv : (A.prod (Classical.choose hker)).IsInvertible)
    (hcont : ContDiffAt K n f
      ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y)) :
    ContDiffAt K n (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y := by
  obtain ⟨M, hM⟩ := hAinv
  refine (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).contDiffAt_symm
    (f₀' := M) hy ?_ (hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented hcont hf' hker)
  rw [hf.coe_implicitToOpenPartialHomeomorphOfComplemented hf' hker, hM]
  exact hA.prodMk ((Classical.choose hker).hasFDerivAt.comp _ ((hasFDerivAt_id _).sub_const a))

/-- The inverse of Mathlib's complemented-kernel implicit-function homeomorphism is as smooth as
the original map at the image of the base point. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hcont : ContDiffAt K n f a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    ContDiffAt K n
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm (f a, 0) := by
  have hbase := hf.implicitToOpenPartialHomeomorphOfComplemented_symm_self hf' hker
  refine hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_isInvertible hf' hker
    (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker) (A := f') ?_ ?_ ?_
  · rw [hbase]; exact hf.hasFDerivAt
  · exact ⟨f'.implicitCoordEquiv hf' hker, ContinuousLinearMap.coe_implicitCoordEquiv ..⟩
  · rw [hbase]; exact hcont

/-! ### The neighbourhood on which the coordinate map stays invertible -/

/-- An open neighbourhood of the base point on which the derivative of the implicit-function
coordinate map `x ↦ (f x, P (x - a))` is still invertible: the source of the homeomorphism that
the inverse function theorem builds from that map. Like Mathlib's implicit-function homeomorphism
itself, it is a choice, and is described only through the lemmas below. -/
noncomputable def implicitCoordSource (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : Set E :=
  ((hf.hasStrictFDerivAt_implicitCoord hf' hker).toOpenPartialHomeomorph
    fun x ↦ (f x, Classical.choose hker (x - a))).source

theorem isOpen_implicitCoordSource (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : IsOpen (hf.implicitCoordSource hf' hker) :=
  OpenPartialHomeomorph.open_source _

theorem mem_implicitCoordSource (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : a ∈ hf.implicitCoordSource hf' hker :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- **The derivative of the coordinate map stays invertible on
`HasStrictFDerivAt.implicitCoordSource`.** If `f` has derivative `A` at a point of that
neighbourhood, then `(A, P)` is a continuous linear equivalence, exactly as `(f', P)` is at the
base point. -/
theorem isInvertible_prod_of_mem_implicitCoordSource (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) {x : E}
    (hx : x ∈ hf.implicitCoordSource hf' hker) {A : E →L[K] F} (hA : HasFDerivAt f A x) :
    (A.prod (Classical.choose hker)).IsInvertible := by
  have : CompleteSpace f'.ker := hker.isClosed.completeSpace_coe
  exact (hf.hasStrictFDerivAt_implicitCoord hf'
    hker).isInvertible_of_mem_toOpenPartialHomeomorph_source hx
      (hA.prodMk ((Classical.choose hker).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)))

/-- **The implicit function is `C^n` on a whole neighbourhood of the origin of the slice.** The
inverse of the implicit-function homeomorphism is `C^n` at every point of its target whose
preimage lies in `HasStrictFDerivAt.implicitCoordSource`. -/
theorem contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented)
    {y : F × f'.ker}
    (hy : y ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target)
    (hmem : (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y ∈
      hf.implicitCoordSource hf' hker)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y))
    (hcont : ContDiffAt K n f
      ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y)) :
    ContDiffAt K n (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).symm y :=
  hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_isInvertible hf' hker hy hA
    (hf.isInvertible_prod_of_mem_implicitCoordSource hf' hker hmem hA) hcont

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
