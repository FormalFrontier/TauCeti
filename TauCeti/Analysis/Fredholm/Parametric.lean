/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.Index
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The parameter projection of a universal linearization

A transversality argument in Floer theory never perturbs a single equation; it perturbs a whole
family. One writes the equation as `f x l = 0` for `x` in a Banach space `E` of maps and `l` in a
Banach space `Λ` of parameters -- almost complex structures, Hamiltonians, metrics -- and studies
the **universal zero set** `{(x, l) | f x l = 0}` rather than any one fibre. Linearizing at a
solution turns that geometric picture into a purely linear one: the total derivative is a
continuous linear map `E × Λ →L[𝕜] F`, its restriction `D₁` to `E × 0` is the linearization of the
single equation at the fixed parameter, its restriction `D₂` to `0 × Λ` records how the equation
moves with the parameter, the kernel of the total derivative is the tangent space to the universal
zero set when the nonlinear hypotheses make that zero set a manifold (and is its candidate tangent
space in general), and the projection to `Λ` of that kernel is the linearization of "forget the
solution, remember the parameter".

This file analyses that projection. Writing the total derivative as a coproduct
`D₁.coprod D₂ : E × Λ →L[𝕜] F`, which by `ContinuousLinearMap.coprod_comp_inl_inr` is no loss of
generality, `TauCeti.parameterProj D₁ D₂` is the restriction of `Prod.snd` to
`(D₁.coprod D₂).ker`, and the two theorems that transversality arguments run on are:

* the projection is **surjective exactly when `D₁` is**, provided the total linearization is
  surjective -- so a parameter is a regular value of the projection exactly when the equation it
  indexes is regular;
* over Banach spaces the projection is **Fredholm whenever `D₁` is Fredholm**, and if the total
  linearization is surjective it has the **same index as `D₁`** -- so the parametrized problem
  carries the same expected dimension count as the unparametrized one.

Together these are the linear engine of the parametric transversality theorem (McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3). A further step can feed the
projection to the Sard--Smale theorem of `TauCeti.Analysis.Fredholm.SardSmale`; besides a smooth
chart on the universal zero set, its residual-set conclusion requires real scalars, second
countability of the domain, and the stated `C^k` threshold. At a regular parameter,
`TauCeti.Analysis.Fredholm.LevelSet` supplies a chart modelled on a finite-dimensional space whose
dimension is the index of `D₁`. This file supplies only the linear half of that chain.

## The exact sequence

Everything below is read off one four-term exact sequence of `𝕜`-modules,
```text
0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁,
```
whose maps are `x ↦ (x, 0)` (`TauCeti.kerCoprodHom`), the parameter projection, and the map
induced by `D₂` (`TauCeti.parameterToCoker`). Its exactness at `ker (D₁.coprod D₂)` and at `Λ` is
`TauCeti.exact_kerCoprodHom_parameterProj` and
`TauCeti.exact_parameterProj_parameterToCoker`; both hold with no hypothesis at all.

Exactness at `ker (D₁.coprod D₂)` says that the kernel of the projection is `ker D₁`: a point of
the universal zero set over a *fixed* parameter is a solution of the equation that parameter
indexes. Exactness at `Λ` says that the range of the projection consists of the parameter
directions whose infinitesimal effect `D₂ l` on the equation is already achievable by moving the
solution.

Surjectivity of the total linearization says exactly that `range D₁ ⊔ range D₂ = ⊤`, that is, that
the last map above is onto (`TauCeti.parameterToCoker_surjective_iff_coprod_surjective`). Extending
the sequence by `→ 0` on the right then identifies the cokernel of the projection with the
cokernel of `D₁` (`TauCeti.quotientRangeParameterProjEquiv`), and the surjectivity criterion is
the degenerate case of that identification.

The index statement needs neither completeness nor the Fredholm property, because
`TauCeti.ContinuousLinearMap.index` is a difference of two `Module.finrank`s and the sequence
matches both of them. The Fredholm statement additionally assumes that `D₁` is Fredholm and asks
for Banach spaces, then certifies the two dimensions finite through
`ContinuousLinearMap.IsFredholm.of_finite_ker_coker`.

## Main declarations

* `TauCeti.parameterProj`: the projection to the parameter space of the kernel of a total
  linearization `D₁.coprod D₂`.
* `TauCeti.exact_kerCoprodHom_parameterProj` and `TauCeti.exact_parameterProj_parameterToCoker`:
  the exact sequence above.
* `TauCeti.kerEquivKerParameterProj`: the kernel of the projection is `ker D₁`.
* `TauCeti.range_parameterProj`: its range is the preimage of `range D₁` under `D₂`.
* `TauCeti.parameterToCoker_surjective_iff_coprod_surjective`: the total linearization is onto
  exactly when the parameter directions span the cokernel of `D₁`.
* `TauCeti.quotientRangeParameterProjEquiv`: for a surjective total linearization, the cokernel of
  the projection is the cokernel of `D₁`.
* `TauCeti.parameterProj_surjective_iff`: for a surjective total linearization, the projection is
  surjective exactly when `D₁` is.
* `TauCeti.index_parameterProj`: for a surjective total linearization, the
  projection has the same index as `D₁`.
* `TauCeti.isFredholm_parameterProj`: over Banach spaces, if `D₁` is Fredholm then the projection
  is Fredholm.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace TauCeti

open Module

section Topological

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E Λ F : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]
variable [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]
variable (D₁ : E →L[𝕜] F) (D₂ : Λ →L[𝕜] F)

/-- The **parameter projection** of the total linearization `D₁.coprod D₂ : E × Λ →L[𝕜] F`: the
restriction to its kernel of the projection `E × Λ →L[𝕜] Λ`.

The kernel of the total linearization is the candidate tangent space to the universal zero set of
a parametrized equation; under the nonlinear hypotheses making that zero set a manifold, it is
its tangent space. This map is then the linearization of the projection of that zero set to the
space of parameters. Every continuous linear map out of `E × Λ` is of the form `D₁.coprod D₂`,
by `ContinuousLinearMap.coprod_comp_inl_inr`, so the coproduct source is no restriction. -/
def parameterProj : (D₁.coprod D₂).ker →L[𝕜] Λ :=
  (ContinuousLinearMap.snd 𝕜 E Λ).domRestrict (D₁.coprod D₂).ker

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The parameter projection reads off the parameter component of a candidate tangent vector. -/
@[simp]
theorem parameterProj_apply (v : (D₁.coprod D₂).ker) : parameterProj D₁ D₂ v = (v : E × Λ).2 :=
  (rfl)

/-! ### Exactness at the candidate tangent space: the kernel of the projection -/

/-- The embedding `x ↦ (x, 0)` of `ker D₁` into the kernel of the total linearization: the formal
tangent directions to the universal zero set along which the parameter does not move. -/
def kerCoprodHom : D₁.ker →L[𝕜] (D₁.coprod D₂).ker :=
  (ContinuousLinearMap.inl 𝕜 E Λ).restrict fun _ hx => by simpa [LinearMap.mem_ker] using hx

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The embedding sends `x` to the pair `(x, 0)`. -/
@[simp]
theorem kerCoprodHom_apply (x : D₁.ker) : (kerCoprodHom D₁ D₂ x : E × Λ) = ((x : E), 0) :=
  (rfl)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The embedding `x ↦ (x, 0)` is injective, which is exactness of the sequence at `ker D₁`. -/
theorem kerCoprodHom_injective : Function.Injective (kerCoprodHom D₁ D₂) := by
  intro x y hxy
  apply Subtype.ext
  exact LinearMap.inl_injective (R := 𝕜) (M := E) (M₂ := Λ)
    (by simpa [kerCoprodHom] using congrArg Subtype.val hxy)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The formal tangent directions along which the parameter does not move are exactly the
solutions of the linearized equation at the fixed parameter. -/
@[simp]
theorem range_kerCoprodHom :
    LinearMap.range (kerCoprodHom D₁ D₂ : D₁.ker →ₗ[𝕜] (D₁.coprod D₂).ker) =
      (parameterProj D₁ D₂).ker := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hv
    obtain ⟨⟨x, l⟩, hk⟩ := v
    have hl : l = 0 := by simpa using hv
    subst hl
    have hx : x ∈ D₁.ker := by simpa [LinearMap.mem_ker] using hk
    exact ⟨⟨x, hx⟩, rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- Exactness of `0 → ker D₁ → ker (D₁.coprod D₂) → Λ` at the middle term. -/
theorem exact_kerCoprodHom_parameterProj :
    Function.Exact (kerCoprodHom D₁ D₂) (parameterProj D₁ D₂) :=
  LinearMap.exact_iff.mpr (range_kerCoprodHom D₁ D₂).symm

/-- **The kernel of the parameter projection is the kernel of `D₁`**, embedded by `x ↦ (x, 0)`. -/
private def kerParameterProjInverse :
    (parameterProj D₁ D₂).ker →L[𝕜] D₁.ker :=
  ((ContinuousLinearMap.fst 𝕜 E Λ).comp (D₁.coprod D₂).ker.subtypeL).restrict fun v hv => by
    have hl : (v : E × Λ).2 = 0 := by simpa [LinearMap.mem_ker] using hv
    simpa [LinearMap.mem_ker, hl] using v.property

private def kerCoprodHomToKer :
    D₁.ker →L[𝕜] (parameterProj D₁ D₂).ker :=
  (kerCoprodHom D₁ D₂).codRestrict _ fun x => by simp [LinearMap.mem_ker]

/-- The continuous linear identification of `ker D₁` with the kernel of the projection. -/
def kerEquivKerParameterProj :
    D₁.ker ≃L[𝕜] (parameterProj D₁ D₂).ker :=
  ContinuousLinearEquiv.equivOfInverse (kerCoprodHomToKer D₁ D₂)
    (kerParameterProjInverse D₁ D₂)
    (fun x => by ext; simp [kerCoprodHomToKer, kerParameterProjInverse])
    (fun v => by
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · simp [kerCoprodHomToKer, kerParameterProjInverse]
      · have hv : ((v : (D₁.coprod D₂).ker) : E × Λ).2 = 0 := by
          have hv' : parameterProj D₁ D₂ (v : (D₁.coprod D₂).ker) = 0 := v.property
          simpa only [parameterProj_apply] using hv'
        simpa [kerCoprodHomToKer, kerParameterProjInverse] using hv.symm)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The identification of `ker D₁` with the kernel of the projection is `x ↦ (x, 0)`. -/
@[simp]
theorem kerEquivKerParameterProj_apply (x : D₁.ker) :
    ((kerEquivKerParameterProj D₁ D₂ x : (D₁.coprod D₂).ker) : E × Λ) = ((x : E), 0) := by
  simp [kerEquivKerParameterProj, kerCoprodHomToKer]

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The inverse identification takes the first component of a vector in the projection kernel. -/
@[simp]
theorem kerEquivKerParameterProj_symm_apply (v : (parameterProj D₁ D₂).ker) :
    (((kerEquivKerParameterProj D₁ D₂).symm v : D₁.ker) : E) =
      ((v : (D₁.coprod D₂).ker) : E × Λ).1 := by
  simp [kerEquivKerParameterProj, kerParameterProjInverse]

/-! ### Exactness at the parameter space: the range of the projection -/

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The range of the parameter projection is the set of parameter directions whose infinitesimal
effect `D₂ l` on the equation can already be undone by moving the solution.

No hypothesis on `D₁` or on the total linearization is needed. -/
@[simp]
theorem range_parameterProj :
    (parameterProj D₁ D₂).range = D₁.range.comap (D₂ : Λ →ₗ[𝕜] F) := by
  ext l
  simp only [LinearMap.mem_range, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    parameterProj_apply]
  constructor
  · rintro ⟨⟨⟨x, m⟩, hk⟩, rfl⟩
    exact ⟨-x, by
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right (by simpa using hk)⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨(-x, l), by simp [hx]⟩, rfl⟩

/-- The map `Λ → F ⧸ range D₁` induced by `D₂`: it measures how far the infinitesimal effect of a
parameter direction is from being achievable by moving the solution. -/
noncomputable def parameterToCoker : Λ →ₗ[𝕜] F ⧸ D₁.range :=
  D₁.range.mkQ ∘ₗ (D₂ : Λ →ₗ[𝕜] F)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/-- The induced map sends a parameter direction to the class of its infinitesimal effect. -/
@[simp]
theorem parameterToCoker_apply (l : Λ) : parameterToCoker D₁ D₂ l = D₁.range.mkQ (D₂ l) :=
  (rfl)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The kernel of the map induced by `D₂` is the range of the parameter projection: this is
`TauCeti.range_parameterProj` read in the quotient. -/
@[simp]
theorem ker_parameterToCoker :
    LinearMap.ker (parameterToCoker D₁ D₂) = (parameterProj D₁ D₂).range := by
  rw [parameterToCoker, LinearMap.ker_comp, Submodule.ker_mkQ, range_parameterProj]

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- Exactness of `ker (D₁.coprod D₂) → Λ → F ⧸ range D₁` at the middle term. -/
theorem exact_parameterProj_parameterToCoker :
    Function.Exact (parameterProj D₁ D₂) (parameterToCoker D₁ D₂) :=
  LinearMap.exact_iff.mpr (ker_parameterToCoker D₁ D₂)

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- **The total linearization is surjective exactly when the parameter directions span the
cokernel of `D₁`.**

This is the criterion transversality arguments verify in practice: one exhibits enough
perturbations of the equation to cover every obstruction to solving the linearized equation. -/
theorem parameterToCoker_surjective_iff_coprod_surjective :
    Function.Surjective (parameterToCoker D₁ D₂) ↔ Function.Surjective (D₁.coprod D₂) := by
  -- `LinearMap.range_eq_top` is stated for the coercion of `D₁.coprod D₂` to a plain linear map,
  -- whose `DFunLike` coercion is only definitionally the one in the goal, so `rw` cannot reach it
  -- on the right-hand side; a typed `have` bridges the two coercions once and for all.
  have hcoprod : Function.Surjective (D₁.coprod D₂) ↔ (D₁.coprod D₂).range = ⊤ :=
    (LinearMap.range_eq_top (f := (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))).symm
  rw [hcoprod, ← LinearMap.range_eq_top, parameterToCoker, LinearMap.range_comp,
    Submodule.map_mkQ_eq_top, ContinuousLinearMap.range_coprod]

/-! ### The cokernel of the projection -/

/-- The cokernel of the parameter projection is the range of the map from parameters into the
cokernel of `D₁`. -/
noncomputable def quotientRangeParameterProjEquivRange :
    (Λ ⧸ (parameterProj D₁ D₂).range) ≃ₗ[𝕜] LinearMap.range (parameterToCoker D₁ D₂) :=
  (Submodule.quotEquivOfEq _ _ (ker_parameterToCoker D₁ D₂).symm).trans
    (LinearMap.quotKerEquivRange (parameterToCoker D₁ D₂))

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The range equivalence sends the class of `l` to the image of `l` in the cokernel. -/
@[simp]
theorem quotientRangeParameterProjEquivRange_mk (l : Λ) :
    ((quotientRangeParameterProjEquivRange D₁ D₂ (Submodule.Quotient.mk l) :
      LinearMap.range (parameterToCoker D₁ D₂)) : F ⧸ D₁.range) = D₁.range.mkQ (D₂ l) := by
  simp only [quotientRangeParameterProjEquivRange, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
    parameterToCoker_apply]

/-- **For a surjective total linearization, the cokernel of the parameter projection is the
cokernel of `D₁`**, identified by the map induced by `D₂`.

`TauCeti.ker_parameterToCoker` identifies the kernel of the map from parameters to the cokernel
with `range (parameterProj D₁ D₂)`, making the descended map on the quotient injective.
Surjectivity of the total linearization is what makes that descended map onto. -/
noncomputable def quotientRangeParameterProjEquiv (hD : Function.Surjective (D₁.coprod D₂)) :
    (Λ ⧸ (parameterProj D₁ D₂).range) ≃ₗ[𝕜] F ⧸ D₁.range :=
  (Submodule.quotEquivOfEq _ _ (ker_parameterToCoker D₁ D₂).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).mpr hD))

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The cokernel equivalence sends the class of `l` to the class of `D₂ l`. -/
@[simp]
theorem quotientRangeParameterProjEquiv_mk (hD : Function.Surjective (D₁.coprod D₂)) (l : Λ) :
    quotientRangeParameterProjEquiv D₁ D₂ hD (Submodule.Quotient.mk l) =
      Submodule.Quotient.mk (D₂ l) :=
  by simp [quotientRangeParameterProjEquiv]

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- If `D₁` is onto, then so is the parameter projection, with no hypothesis on the total
linearization. -/
theorem range_parameterProj_eq_top_of_range_eq_top (hD₁ : D₁.range = ⊤) :
    (parameterProj D₁ D₂).range = ⊤ := by
  rw [range_parameterProj, hD₁, Submodule.comap_top]

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The `Function.Surjective` form of
`TauCeti.range_parameterProj_eq_top_of_range_eq_top`. -/
theorem parameterProj_surjective_of_surjective (hD₁ : Function.Surjective D₁) :
    Function.Surjective (parameterProj D₁ D₂) :=
  LinearMap.range_eq_top.mp
    (range_parameterProj_eq_top_of_range_eq_top D₁ D₂ (LinearMap.range_eq_top.mpr hD₁))

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- Assuming the total linearization is surjective, the parameter projection is onto exactly when
`D₁` is. In the nonlinear application, this says that a parameter is a regular value of the
projection from the universal zero set precisely when the equation it indexes is regular. -/
theorem range_parameterProj_eq_top_iff (hD : (D₁.coprod D₂).range = ⊤) :
    (parameterProj D₁ D₂).range = ⊤ ↔ D₁.range = ⊤ := by
  rw [ContinuousLinearMap.range_coprod] at hD
  refine ⟨fun h => ?_, range_parameterProj_eq_top_of_range_eq_top D₁ D₂⟩
  refine top_unique ?_
  rw [← hD]
  refine sup_le le_rfl ?_
  rintro _ ⟨l, rfl⟩
  have hl : l ∈ (parameterProj D₁ D₂).range := h.ge Submodule.mem_top
  rwa [range_parameterProj] at hl

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup Λ]
  [ContinuousSMul 𝕜 Λ] [ContinuousSMul 𝕜 F] in
/-- The `Function.Surjective` form of `TauCeti.range_parameterProj_eq_top_iff`. -/
theorem parameterProj_surjective_iff (hD : Function.Surjective (D₁.coprod D₂)) :
    Function.Surjective (parameterProj D₁ D₂) ↔ Function.Surjective D₁ := by
  have h := range_parameterProj_eq_top_iff D₁ D₂ (LinearMap.range_eq_top.mpr hD)
  rw [LinearMap.range_eq_top, LinearMap.range_eq_top] at h
  exact h

end Topological

section Normed

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable (D₁ : E →L[𝕜] F) (D₂ : Λ →L[𝕜] F)

/-- The kernel of the parameter projection has the same dimension as the kernel of `D₁`. -/
@[simp]
theorem finrank_ker_parameterProj :
    finrank 𝕜 ((parameterProj D₁ D₂).ker) = finrank 𝕜 D₁.ker :=
  (kerEquivKerParameterProj D₁ D₂).toLinearEquiv.finrank_eq.symm

/-- The kernel of the parameter projection is finite dimensional as soon as that of `D₁` is. -/
theorem finiteDimensional_ker_parameterProj [FiniteDimensional 𝕜 D₁.ker] :
    FiniteDimensional 𝕜 ((parameterProj D₁ D₂).ker) :=
  (kerEquivKerParameterProj D₁ D₂).toLinearEquiv.finiteDimensional

/-- For a surjective total linearization, the cokernel of the parameter projection has the same
dimension as the cokernel of `D₁`. -/
theorem finrank_quotient_range_parameterProj (hD : Function.Surjective (D₁.coprod D₂)) :
    finrank 𝕜 (Λ ⧸ (parameterProj D₁ D₂).range) = finrank 𝕜 (F ⧸ D₁.range) :=
  (quotientRangeParameterProjEquiv D₁ D₂ hD).finrank_eq

/-- The cokernel of the parameter projection is finite dimensional as soon as that of `D₁` is;
surjectivity of the total linearization is not needed. -/
theorem finiteDimensional_quotient_range_parameterProj
    [FiniteDimensional 𝕜 (F ⧸ D₁.range)] :
    FiniteDimensional 𝕜 (Λ ⧸ (parameterProj D₁ D₂).range) :=
  (quotientRangeParameterProjEquivRange D₁ D₂).symm.finiteDimensional

/-! ### The index and the Fredholm property -/

/-- **The parameter projection of a surjective total linearization has the same index as `D₁`.**

Under the hypotheses needed to apply `TauCeti.Analysis.Fredholm.LevelSet`, this equality gives the
dimension of the finite-dimensional model space for a regular fibre.

Neither operator is assumed Fredholm: both sides are differences of `Module.finrank`s, and the
exact sequence matches the four dimensions in pairs, junk values included. -/
theorem index_parameterProj (hD : Function.Surjective (D₁.coprod D₂)) :
    ContinuousLinearMap.index (parameterProj D₁ D₂) = ContinuousLinearMap.index D₁ := by
  rw [ContinuousLinearMap.index_eq_finrank_sub, ContinuousLinearMap.index_eq_finrank_sub,
    finrank_ker_parameterProj, finrank_quotient_range_parameterProj D₁ D₂ hD]

section Banach

variable [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace Λ]

/-- **The parameter projection is Fredholm** as soon as `D₁` is, over Banach spaces. When the
total linearization is surjective, `TauCeti.index_parameterProj` also identifies
their indices.

Applying Sard--Smale in the nonlinear setting is a further step requiring a suitable smooth chart,
real scalars, second countability, and the theorem's `C^k` threshold. -/
theorem isFredholm_parameterProj (hD₁ : ContinuousLinearMap.IsFredholm D₁) :
    ContinuousLinearMap.IsFredholm (parameterProj D₁ D₂) := by
  have hker := hD₁.finite_ker
  have hcoker := hD₁.finite_coker
  exact .of_finite_ker_coker _ (finiteDimensional_ker_parameterProj D₁ D₂)
    (finiteDimensional_quotient_range_parameterProj D₁ D₂)

end Banach

end Normed

end TauCeti
