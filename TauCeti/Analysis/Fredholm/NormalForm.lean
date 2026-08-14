/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Local normal form of a Fredholm map

This file gives the Lyapunov--Schmidt finite-dimensional reduction of a nonlinear map at a point
where its derivative is Fredholm. A Fredholm package splits the domain and codomain into
essential parts, on which the derivative is invertible, and finite-dimensional inessential
parts. Projecting the nonlinear map to the essential codomain and retaining the inessential
domain coordinate gives a local homeomorphism. This is the first-order, topological part of the
finite-dimensional reduction; applying Sard additionally requires neighborhood `C^k` regularity
of the chart and obstruction under corresponding hypotheses on the original map. In these
coordinates the original map has the form

`(r, k) ↦ r + q(r, k)`,

where `q` takes values in the finite-dimensional codomain complement. Thus all failure of
surjectivity is confined to the finite-dimensional codomain complement; after fixing `r`, the
remaining variable `k` also ranges over a finite-dimensional space. This is the normal-form
ingredient of the Sard--Smale argument in Lane F0 of the analytic Heegaard Floer roadmap.

The construction follows S. Smale, *An infinite dimensional version of Sard's theorem*,
Amer. J. Math. 87 (1965), 861--866, and McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, Appendix A. The local chart is Mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph`; the linear splittings are Mathlib's
`ContinuousLinearMap.FredholmPackage`.

## Main declarations

* `ContinuousLinearMap.FredholmPackage.normalFormEquivL`: the linear coordinate change
  determined by a Fredholm package.
* `ContinuousLinearMap.FredholmPackage.normalFormMap`: the nonlinear coordinate map.
* `ContinuousLinearMap.FredholmPackage.normalFormOpenPartialHomeomorph`: the local homeomorphism
  defined by that map.
* `ContinuousLinearMap.FredholmPackage.obstructionMap`: the remainder valued in the
  finite-dimensional complementary codomain direction.
* `ContinuousLinearMap.FredholmPackage.apply_normalFormOpenPartialHomeomorph_symm`:
  reconstruction of the original map from its essential coordinate and obstruction map.
* `ContinuousLinearMap.FredholmPackage.hasStrictFDerivAt_obstructionMap_self`: the obstruction has
  zero derivative at the base point.
-/

public section

noncomputable section

open Set

namespace ContinuousLinearMap.FredholmPackage

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F} (pkg : ContinuousLinearMap.FredholmPackage T)

/-! ### Linear and nonlinear coordinates -/

/-- The linear coordinate change associated to a Fredholm package. It first splits the domain as
the essential summand and the finite-dimensional kernel summand, then uses the package's
equivalence on the essential coordinate. -/
def normalFormEquivL :
    E ≃L[𝕜] (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decDom.isTopCompl).symm.trans
    (pkg.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 pkg.decDom.X₀))

omit [CompleteSpace E] in
/-- The essential coordinate of the linear normal form is the projection of `T x` to the
essential codomain summand. -/
@[simp]
theorem normalFormEquivL_fst (x : E) :
    (pkg.normalFormEquivL x).1 = pkg.decCodom.proj (T x) := by
  simp [normalFormEquivL, pkg.eq_equiv]

omit [CompleteSpace E] in
/-- The inessential coordinate of the linear normal form is the projection of `x` to the
finite-dimensional kernel summand. -/
@[simp]
theorem normalFormEquivL_snd (x : E) :
    (pkg.normalFormEquivL x).2 =
      pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm x := by
  simp [normalFormEquivL]

omit [CompleteSpace E] in
/-- The inverse linear normal-form coordinates reassemble the essential and inessential domain
components. -/
@[simp]
theorem normalFormEquivL_symm_apply (y : pkg.decCodom.X₁ × pkg.decDom.X₀) :
    pkg.normalFormEquivL.symm y = (pkg.equiv.symm y.1 : E) + (y.2 : E) := by
  simp [normalFormEquivL]

/-- The nonlinear normal-form coordinate map at `a`. Its first coordinate is the projection of
`f x` to the essential codomain summand; its second remembers the finite-dimensional kernel
coordinate of `x - a`. -/
def normalFormMap (f : E → F) (a : E) (x : E) :
    pkg.decCodom.X₁ × pkg.decDom.X₀ :=
  (pkg.decCodom.proj (f x),
    pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm (x - a))

omit [CompleteSpace E] in
/-- The two components of the nonlinear normal-form coordinate map. -/
@[simp]
theorem normalFormMap_apply (f : E → F) (a x : E) :
    pkg.normalFormMap f a x =
      (pkg.decCodom.proj (f x),
        pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm (x - a)) := by
  unfold normalFormMap
  rfl

omit [CompleteSpace E] in
/-- The normal-form coordinate map evaluated at its base point. -/
theorem normalFormMap_self (f : E → F) (a : E) :
    pkg.normalFormMap f a a = (pkg.decCodom.proj (f a), 0) := by
  simp [normalFormMap]

omit [CompleteSpace E] in
/-- The derivative of the nonlinear normal-form coordinate map at any point is the product of the
projected derivative of `f` and the fixed projection onto the inessential domain summand. -/
theorem hasStrictFDerivAt_normalFormMap_of {f : E → F} {a x : E} {T' : E →L[𝕜] F}
    (hf : HasStrictFDerivAt f T' x) :
    HasStrictFDerivAt (pkg.normalFormMap f a)
      ((pkg.decCodom.proj.comp T').prod
        (pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm)) x := by
  have hfst : HasStrictFDerivAt (fun x ↦ pkg.decCodom.proj (f x))
      (pkg.decCodom.proj.comp T') x :=
    pkg.decCodom.proj.hasStrictFDerivAt.comp x hf
  let P := pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm
  have hsnd : HasStrictFDerivAt
      (fun x ↦ P (x - a)) P x := by
    simpa only [map_sub] using P.hasStrictFDerivAt.sub_const (P a)
  exact hfst.prodMk hsnd

omit [CompleteSpace E] in
/-- The product of the two linear normal-form projections agrees with the explicit linear
coordinate equivalence supplied by the Fredholm package. -/
private theorem prod_projection_eq_normalFormEquivL :
    (pkg.decCodom.proj.comp T).prod
        (pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm) =
      (pkg.normalFormEquivL : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀) := by
  ext x
  · exact congrArg Subtype.val (pkg.normalFormEquivL_fst x).symm
  · exact congrArg Subtype.val (pkg.normalFormEquivL_snd x).symm

omit [CompleteSpace E] in
/-- The derivative of the nonlinear normal-form coordinate map at its base point is precisely the
linear coordinate equivalence associated to the Fredholm package. -/
theorem hasStrictFDerivAt_normalFormMap {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.normalFormMap f a)
      (pkg.normalFormEquivL : E →L[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀) a :=
  (pkg.hasStrictFDerivAt_normalFormMap_of hf).congr_fderiv
    pkg.prod_projection_eq_normalFormEquivL

/-- The local homeomorphism putting a map into Fredholm normal-form coordinates near a point where
its derivative is represented by `pkg`. -/
def normalFormOpenPartialHomeomorph {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a) :
    OpenPartialHomeomorph E (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (pkg.hasStrictFDerivAt_normalFormMap hf).toOpenPartialHomeomorph _

/-- The Fredholm normal-form homeomorphism agrees with the normal-form coordinate map everywhere;
its source only controls where the inverse laws apply. -/
@[simp]
theorem normalFormOpenPartialHomeomorph_apply {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) (x : E) :
    pkg.normalFormOpenPartialHomeomorph hf x = pkg.normalFormMap f a x :=
  congrFun (HasStrictFDerivAt.toOpenPartialHomeomorph_coe _) x

/-- The base point belongs to the source of the Fredholm normal-form homeomorphism. -/
theorem mem_normalFormOpenPartialHomeomorph_source {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    a ∈ (pkg.normalFormOpenPartialHomeomorph hf).source :=
  (pkg.hasStrictFDerivAt_normalFormMap hf).mem_toOpenPartialHomeomorph_source

/-- The normal-form coordinate of the base point belongs to the target of the local
homeomorphism. -/
theorem normalFormOpenPartialHomeomorph_self_mem_target {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    (pkg.decCodom.proj (f a), 0) ∈ (pkg.normalFormOpenPartialHomeomorph hf).target := by
  rw [← pkg.normalFormMap_self f a, ← pkg.normalFormOpenPartialHomeomorph_apply hf]
  exact (pkg.normalFormOpenPartialHomeomorph hf).map_source
    (pkg.mem_normalFormOpenPartialHomeomorph_source hf)

/-- Applying the inverse normal-form coordinate map to the coordinate of the base point returns
the base point. -/
@[simp]
theorem normalFormOpenPartialHomeomorph_symm_self {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    (pkg.normalFormOpenPartialHomeomorph hf).symm
      (pkg.decCodom.X₁.projectionOnto pkg.decCodom.X₀ pkg.decCodom.isTopCompl.isCompl (f a), 0) =
        a := by
  rw [← Submodule.coe_projectionOntoL pkg.decCodom.isTopCompl,
    ← pkg.normalFormMap_self f a,
    ← pkg.normalFormOpenPartialHomeomorph_apply hf]
  exact (pkg.normalFormOpenPartialHomeomorph hf).left_inv
    (pkg.mem_normalFormOpenPartialHomeomorph_source hf)

/-! ### The finite-dimensional obstruction map -/

/-- The inessential-codomain component of `f` in Fredholm normal-form coordinates. Its codomain is
finite dimensional by `pkg.decCodom.finite_X₀`; fixing the first coordinate restricts it to a map
between the finite-dimensional spaces `pkg.decDom.X₀` and `pkg.decCodom.X₀`. Applying Sard to
that slice additionally requires suitable neighborhood regularity. Values outside the target of
`pkg.normalFormOpenPartialHomeomorph hf` are irrelevant, as for any
`OpenPartialHomeomorph` inverse. -/
def obstructionMap {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    (y : pkg.decCodom.X₁ × pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
    (f ((pkg.normalFormOpenPartialHomeomorph hf).symm y))

/-- The obstruction map is the complementary-codomain projection of `f` after applying the
inverse normal-form coordinates. -/
@[simp]
theorem obstructionMap_apply {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    (y : pkg.decCodom.X₁ × pkg.decDom.X₀) :
    pkg.obstructionMap hf y =
      pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
        (f ((pkg.normalFormOpenPartialHomeomorph hf).symm y)) := by
  unfold obstructionMap
  rfl

/-- In normal-form coordinates, the essential component of `f` is the first coordinate. -/
theorem proj_apply_normalFormOpenPartialHomeomorph_symm {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a)
    {y : pkg.decCodom.X₁ × pkg.decDom.X₀}
    (hy : y ∈ (pkg.normalFormOpenPartialHomeomorph hf).target) :
    pkg.decCodom.proj (f ((pkg.normalFormOpenPartialHomeomorph hf).symm y)) = y.1 := by
  have hright := (pkg.normalFormOpenPartialHomeomorph hf).right_inv hy
  rw [pkg.normalFormOpenPartialHomeomorph_apply hf] at hright
  exact congrArg Prod.fst hright

/-- **Fredholm local normal form.** On the target of the normal-form chart, the original map is
the sum of its essential coordinate and the finite-dimensional obstruction. -/
theorem apply_normalFormOpenPartialHomeomorph_symm {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a)
    {y : pkg.decCodom.X₁ × pkg.decDom.X₀}
    (hy : y ∈ (pkg.normalFormOpenPartialHomeomorph hf).target) :
    f ((pkg.normalFormOpenPartialHomeomorph hf).symm y) =
      (y.1 : F) + (pkg.obstructionMap hf y : F) := by
  let e : (pkg.decCodom.X₁ × pkg.decCodom.X₀) ≃L[𝕜] F :=
    Submodule.prodEquivOfIsTopCompl _ _ pkg.decCodom.isTopCompl
  have hsplit := e.apply_symm_apply (f ((pkg.normalFormOpenPartialHomeomorph hf).symm y))
  rw [Submodule.prodEquivOfIsTopCompl_symm_apply,
    pkg.proj_apply_normalFormOpenPartialHomeomorph_symm hf hy] at hsplit
  simpa [e, obstructionMap, Submodule.prodEquivOfIsTopCompl_apply] using hsplit.symm

/-- The inverse normal-form coordinates have derivative inverse to the linear normal-form
equivalence at the coordinate of the base point. -/
theorem hasStrictFDerivAt_normalFormOpenPartialHomeomorph_symm_self {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.normalFormOpenPartialHomeomorph hf).symm
      (pkg.normalFormEquivL.symm :
        (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)
      (pkg.decCodom.proj (f a), 0) := by
  have hinv := (pkg.hasStrictFDerivAt_normalFormMap hf).to_localInverse
  rw [HasStrictFDerivAt.localInverse_def] at hinv
  simpa only [normalFormOpenPartialHomeomorph, normalFormMap_self] using hinv

/-- The finite-dimensional obstruction has zero derivative at the coordinate of the base point.
This is the differential statement that the chosen essential coordinate absorbs the entire
linear part of `f`. -/
theorem hasStrictFDerivAt_obstructionMap_self {f : E → F} {a : E}
    (hf : HasStrictFDerivAt f T a) :
    HasStrictFDerivAt (pkg.obstructionMap hf)
      (0 : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] pkg.decCodom.X₀)
      (pkg.decCodom.proj (f a), 0) := by
  let P := pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
  have hinv := pkg.hasStrictFDerivAt_normalFormOpenPartialHomeomorph_symm_self hf
  have hf' : HasStrictFDerivAt f T
      ((pkg.normalFormOpenPartialHomeomorph hf).symm (pkg.decCodom.proj (f a), 0)) := by
    simpa only [Submodule.coe_projectionOntoL,
      pkg.normalFormOpenPartialHomeomorph_symm_self hf] using hf
  have hcomp : HasStrictFDerivAt
      (fun y ↦ P (f ((pkg.normalFormOpenPartialHomeomorph hf).symm y)))
      (P.comp (T.comp (pkg.normalFormEquivL.symm :
        (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)))
      (pkg.decCodom.proj (f a), 0) :=
    P.hasStrictFDerivAt.comp _ (hf'.comp _ hinv)
  have hzero : P.comp (T.comp (pkg.normalFormEquivL.symm :
      (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[𝕜] E)) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    change P (T (pkg.normalFormEquivL.symm y)) = 0
    apply Submodule.projectionOntoL_apply_eq_zero_of_mem_right
    exact pkg.range_eq.le (LinearMap.mem_range_self (T : E →ₗ[𝕜] F) _)
  apply (hcomp.congr_fderiv hzero).congr_of_eventuallyEq
  filter_upwards [] with y
  exact (pkg.obstructionMap_apply hf y).symm

end ContinuousLinearMap.FredholmPackage

end
