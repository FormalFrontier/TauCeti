/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Local normal form of a Fredholm map

This file gives the Lyapunov--Schmidt finite-dimensional reduction of a nonlinear map at a point
where its derivative is Fredholm. A Fredholm package splits the domain and codomain into
essential parts, on which the derivative is invertible, and finite-dimensional inessential
parts. Projecting the nonlinear map to the essential codomain and retaining the inessential
domain coordinate gives a local homeomorphism. In those coordinates the original map has the
form

`(r, k) ↦ r + q(r, k)`,

where `q` takes values in the finite-dimensional codomain complement. Thus all failure of
surjectivity is confined to the finite-dimensional codomain complement; after fixing `r`, the
remaining variable `k` also ranges over a finite-dimensional space. This is the local reduction
used in the proof of Sard--Smale in Lane F0 of the analytic Heegaard Floer roadmap.

The construction follows S. Smale, *An infinite dimensional version of Sard's theorem*,
Amer. J. Math. 87 (1965), 861--866, and McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, Appendix A. The inverse-function step is Mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph`; the linear splittings are Mathlib's
`ContinuousLinearMap.FredholmPackage`.

## Main declarations

* `ContinuousLinearMap.FredholmPackage.normalFormLinearEquiv`: the linear coordinate change
  determined by a Fredholm package.
* `ContinuousLinearMap.FredholmPackage.normalFormMap`: the nonlinear coordinate map.
* `ContinuousLinearMap.FredholmPackage.normalForm`: the local homeomorphism defined by that map.
* `ContinuousLinearMap.FredholmPackage.obstructionMap`: the finite-dimensional remainder in the
  complementary codomain direction.
* `ContinuousLinearMap.FredholmPackage.apply_normalForm_symm`: reconstruction of the original map
  from its essential coordinate and obstruction map.
* `ContinuousLinearMap.FredholmPackage.hasStrictFDerivAt_obstructionMap_self`: the obstruction has
  zero derivative at the base point.
-/

public section

noncomputable section

open Set

namespace ContinuousLinearMap.FredholmPackage

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {T : E →L[𝕜] F} (pkg : ContinuousLinearMap.FredholmPackage T)

/-! ### Linear and nonlinear coordinates -/

/-- The linear coordinate change associated to a Fredholm package. It first splits the domain as
the essential summand and the finite-dimensional kernel summand, then uses the package's
equivalence on the essential coordinate. -/
def normalFormLinearEquiv :
    E ≃L[𝕜] (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decDom.isTopCompl).symm.trans
    (pkg.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 pkg.decDom.X₀))

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The essential coordinate of the linear normal form is the projection of `T x` to the
essential codomain summand. -/
@[simp]
theorem normalFormLinearEquiv_fst (x : E) :
    (pkg.normalFormLinearEquiv x).1 = pkg.decCodom.proj (T x) := by
  simp [normalFormLinearEquiv, pkg.eq_equiv]

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The inessential coordinate of the linear normal form is the projection of `x` to the
finite-dimensional kernel summand. -/
@[simp]
theorem normalFormLinearEquiv_snd (x : E) :
    (pkg.normalFormLinearEquiv x).2 =
      pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm x := by
  simp [normalFormLinearEquiv]

/-- The nonlinear normal-form coordinate map at `a`. Its first coordinate is the projection of
`f x` to the essential codomain summand; its second remembers the finite-dimensional kernel
coordinate of `x - a`. -/
def normalFormMap (f : E → F) (a : E) (x : E) :
    pkg.decCodom.X₁ × pkg.decDom.X₀ :=
  (pkg.decCodom.proj (f x),
    ((ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
      (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀)) (x - a))

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The two components of the nonlinear normal-form coordinate map. -/
@[simp]
theorem normalFormMap_apply (f : E → F) (a x : E) :
    pkg.normalFormMap f a x =
      (pkg.decCodom.proj (f x),
        ((ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
          (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀)) (x - a)) := by
  unfold normalFormMap
  rfl

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The normal-form coordinate map evaluated at its base point. -/
theorem normalFormMap_self (f : E → F) (a : E) :
    pkg.normalFormMap f a a = (pkg.decCodom.proj (f a), 0) := by
  simp [normalFormMap]

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The derivative of the nonlinear normal-form coordinate map at its base point is precisely the
linear coordinate equivalence associated to the Fredholm package. -/
theorem hasStrictFDerivAt_normalFormMap {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.normalFormMap f a)
      (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀) a := by
  have hfst : HasStrictFDerivAt (fun x ↦ pkg.decCodom.proj (f x))
      (pkg.decCodom.proj.comp T) a :=
    pkg.decCodom.proj.hasStrictFDerivAt.comp a hf
  have hsnd : HasStrictFDerivAt
      (fun x ↦ ((ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
        (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀)) (x - a))
      ((ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
        (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀)) a := by
    let L := (ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
      (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀)
    simpa only [L, map_sub] using
      L.hasStrictFDerivAt.sub_const (L a)
  have hprod := hfst.prodMk hsnd
  have hmap : HasStrictFDerivAt (pkg.normalFormMap f a)
      ((pkg.decCodom.proj.comp T).prod
        ((ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decDom.X₀).comp
          (pkg.normalFormLinearEquiv : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀))) a := by
    apply hprod.congr_of_eventuallyEq
    filter_upwards [] with x
    exact (pkg.normalFormMap_apply f a x).symm
  apply hmap.congr_fderiv
  ext x
  · exact congrArg Subtype.val (pkg.normalFormLinearEquiv_fst x).symm
  · rfl

/-- The local homeomorphism putting a map into Fredholm normal-form coordinates near a point where
its derivative is represented by `pkg`. -/
def normalForm {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) :
    OpenPartialHomeomorph E (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (pkg.hasStrictFDerivAt_normalFormMap hf).toOpenPartialHomeomorph _

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The Fredholm normal-form homeomorphism agrees with the normal-form coordinate map everywhere;
its source only controls where the inverse laws apply. -/
@[simp]
theorem normalForm_apply {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) (x : E) :
    pkg.normalForm hf x = pkg.normalFormMap f a x :=
  congrFun (HasStrictFDerivAt.toOpenPartialHomeomorph_coe _) x

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The base point belongs to the source of the Fredholm normal-form homeomorphism. -/
theorem mem_normalForm_source {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) :
    a ∈ (pkg.normalForm hf).source :=
  (pkg.hasStrictFDerivAt_normalFormMap hf).mem_toOpenPartialHomeomorph_source

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The normal-form coordinate of the base point belongs to the target of the local
homeomorphism. -/
theorem normalForm_self_mem_target {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) :
    (pkg.decCodom.proj (f a), 0) ∈ (pkg.normalForm hf).target := by
  rw [← pkg.normalFormMap_self f a, ← pkg.normalForm_apply hf]
  exact (pkg.normalForm hf).map_source (pkg.mem_normalForm_source hf)

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- Applying the inverse normal-form coordinate map to the coordinate of the base point returns
the base point. -/
@[simp]
theorem normalForm_symm_self {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) :
    (pkg.normalForm hf).symm
      (pkg.decCodom.X₁.projectionOnto pkg.decCodom.X₀ pkg.decCodom.isTopCompl.isCompl (f a), 0) =
        a := by
  change (pkg.normalForm hf).symm (pkg.decCodom.proj (f a), 0) = a
  rw [← pkg.normalFormMap_self f a, ← pkg.normalForm_apply hf]
  exact (pkg.normalForm hf).left_inv (pkg.mem_normalForm_source hf)

/-! ### The finite-dimensional obstruction map -/

/-- The inessential-codomain component of `f` in Fredholm normal-form coordinates. Its codomain is
finite dimensional by `pkg.decCodom.finite_X₀`; this is the finite-dimensional map to which Sard's
theorem is applied in the proof of Sard--Smale. Values outside the target of `pkg.normalForm hf`
are irrelevant, as for any `OpenPartialHomeomorph` inverse. -/
def obstructionMap {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    (y : pkg.decCodom.X₁ × pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
    (f ((pkg.normalForm hf).symm y))

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The obstruction map is the complementary-codomain projection of `f` after applying the
inverse normal-form coordinates. -/
@[simp]
theorem obstructionMap_apply {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    (y : pkg.decCodom.X₁ × pkg.decDom.X₀) :
    pkg.obstructionMap hf y =
      pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
        (f ((pkg.normalForm hf).symm y)) := by
  unfold obstructionMap
  rfl

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- In normal-form coordinates, the essential component of `f` is the first coordinate. -/
theorem proj_apply_normalForm_symm {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    {y : pkg.decCodom.X₁ × pkg.decDom.X₀} (hy : y ∈ (pkg.normalForm hf).target) :
    pkg.decCodom.proj (f ((pkg.normalForm hf).symm y)) = y.1 := by
  have hright := (pkg.normalForm hf).right_inv hy
  rw [pkg.normalForm_apply hf] at hright
  exact congrArg Prod.fst hright

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- **Fredholm local normal form.** On the target of the normal-form chart, the original map is
the sum of its essential coordinate and the finite-dimensional obstruction. -/
theorem apply_normalForm_symm {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    {y : pkg.decCodom.X₁ × pkg.decDom.X₀} (hy : y ∈ (pkg.normalForm hf).target) :
    f ((pkg.normalForm hf).symm y) =
      (y.1 : F) + (pkg.obstructionMap hf y : F) := by
  let e : (pkg.decCodom.X₁ × pkg.decCodom.X₀) ≃L[𝕜] F :=
    Submodule.prodEquivOfIsTopCompl _ _ pkg.decCodom.isTopCompl
  have hsplit := e.apply_symm_apply (f ((pkg.normalForm hf).symm y))
  rw [Submodule.prodEquivOfIsTopCompl_symm_apply,
    pkg.proj_apply_normalForm_symm hf hy] at hsplit
  simpa [e, obstructionMap, Submodule.prodEquivOfIsTopCompl_apply] using hsplit.symm

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The inverse normal-form coordinates have derivative inverse to the linear normal-form
equivalence at the coordinate of the base point. -/
theorem hasStrictFDerivAt_normalForm_symm_self {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.normalForm hf).symm
      (pkg.normalFormLinearEquiv.symm :
        (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)
      (pkg.decCodom.proj (f a), 0) := by
  refine OpenPartialHomeomorph.hasStrictFDerivAt_symm (pkg.normalForm hf)
    (pkg.normalForm_self_mem_target hf) ?_
  simp only [Submodule.coe_projectionOntoL]
  rw [pkg.normalForm_symm_self hf]
  apply (pkg.hasStrictFDerivAt_normalFormMap hf).congr_of_eventuallyEq
  filter_upwards [] with x
  exact (pkg.normalForm_apply hf x).symm

omit [CompleteSpace 𝕜] [CompleteSpace F] in
/-- The finite-dimensional obstruction has zero derivative at the coordinate of the base point.
This is the differential statement that the chosen essential coordinate absorbs the entire
linear part of `f`. -/
theorem hasStrictFDerivAt_obstructionMap_self {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.obstructionMap hf)
      (0 : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] pkg.decCodom.X₀)
      (pkg.decCodom.proj (f a), 0) := by
  let P := pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
  have hinv := pkg.hasStrictFDerivAt_normalForm_symm_self hf
  have hf' : HasStrictFDerivAt f T
      ((pkg.normalForm hf).symm (pkg.decCodom.proj (f a), 0)) := by
    simpa only [Submodule.coe_projectionOntoL, pkg.normalForm_symm_self hf] using hf
  have hcomp : HasStrictFDerivAt
      (fun y ↦ P (f ((pkg.normalForm hf).symm y)))
      (P.comp (T.comp (pkg.normalFormLinearEquiv.symm :
        (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)))
      (pkg.decCodom.proj (f a), 0) :=
    P.hasStrictFDerivAt.comp _ (hf'.comp _ hinv)
  have hzero : P.comp (T.comp (pkg.normalFormLinearEquiv.symm :
      (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    simp [P, pkg.eq_equiv]
  apply (hcomp.congr_fderiv hzero).congr_of_eventuallyEq
  filter_upwards [] with y
  exact (pkg.obstructionMap_apply hf y).symm

end ContinuousLinearMap.FredholmPackage

end
