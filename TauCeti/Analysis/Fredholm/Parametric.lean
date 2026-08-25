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
* the projection is **Fredholm of the same index as `D₁`** -- so the parametrized problem carries
  the same expected dimension count as the unparametrized one.

Together these are the linear engine of the parametric transversality theorem (McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3). Once a smooth chart on the
universal zero set is supplied, feeding the projection to the Sard--Smale theorem of
`TauCeti.Analysis.Fredholm.SardSmale` says that for a residual set of parameters the equation that
parameter indexes is regular, and its solution set is a manifold of dimension the index of `D₁`
by `TauCeti.Analysis.Fredholm.LevelSet`. This file supplies only the linear half of that chain; the
required chart is not proved here.

## The exact sequence

Everything below is read off one four-term exact sequence of `𝕜`-modules,
```text
0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁,
```
whose maps are `x ↦ (x, 0)` (`TauCeti.kerCoprodHom`), the parameter projection, and the map
induced by `D₂` (`TauCeti.cokerParameterMap`). Its exactness at `ker (D₁.coprod D₂)` and at `Λ` is
`TauCeti.exact_kerCoprodHom_parameterProj` and
`TauCeti.exact_parameterProj_cokerParameterMap`; both hold with no hypothesis at all.

Exactness at `ker (D₁.coprod D₂)` says that the kernel of the projection is `ker D₁`: a point of
the universal zero set over a *fixed* parameter is a solution of the equation that parameter
indexes. Exactness at `Λ` says that the range of the projection consists of the parameter
directions whose infinitesimal effect `D₂ l` on the equation is already achievable by moving the
solution.

The one hypothesis that ever enters is surjectivity of the total linearization, which says exactly
that `range D₁ ⊔ range D₂ = ⊤`, that is, that the last map above is onto
(`TauCeti.surjective_cokerParameterMap_iff`). Extending the sequence by `→ 0` on the right then
identifies the cokernel of the projection with the cokernel of `D₁`
(`TauCeti.quotientRangeParameterProjEquiv`), and the surjectivity criterion is the degenerate case
of that identification.

The index statement needs neither completeness nor the Fredholm property, because
`TauCeti.ContinuousLinearMap.index` is a difference of two `Module.finrank`s and the sequence
matches both of them; only the Fredholm statement itself, which certifies those two dimensions
finite through `ContinuousLinearMap.IsFredholm.of_finite_ker_coker`, asks for Banach spaces.

## Main declarations

* `TauCeti.parameterProj`: the projection to the parameter space of the kernel of a total
  linearization `D₁.coprod D₂`.
* `TauCeti.exact_kerCoprodHom_parameterProj` and `TauCeti.exact_parameterProj_cokerParameterMap`:
  the exact sequence above.
* `TauCeti.kerParameterProjEquiv`: the kernel of the projection is `ker D₁`.
* `TauCeti.range_parameterProj`: its range is the preimage of `range D₁` under `D₂`.
* `TauCeti.surjective_cokerParameterMap_iff`: the total linearization is onto exactly when the
  parameter directions span the cokernel of `D₁`.
* `TauCeti.quotientRangeParameterProjEquiv`: for a surjective total linearization, the cokernel of
  the projection is the cokernel of `D₁`.
* `TauCeti.surjective_parameterProj_iff`: for a surjective total linearization, the projection is
  surjective exactly when `D₁` is.
* `TauCeti.index_parameterProj`: for a surjective total linearization, the projection has the same
  index as `D₁`.
* `TauCeti.isFredholm_parameterProj`: over Banach spaces, for a surjective total linearization with
  `D₁` Fredholm, the projection is Fredholm.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable (D₁ : E →L[𝕜] F) (D₂ : Λ →L[𝕜] F)

/-- The **parameter projection** of the total linearization `D₁.coprod D₂ : E × Λ →L[𝕜] F`: the
restriction to its kernel of the projection `E × Λ →L[𝕜] Λ`.

The kernel of the total linearization is the candidate tangent space to the universal zero set of
a parametrized equation; under the nonlinear hypotheses making that zero set a manifold, it is
its tangent space. This map is then the linearization of the projection of that zero set to the
space of parameters. Every continuous linear map out of `E × Λ` is of the form `D₁.coprod D₂`,
by `ContinuousLinearMap.coprod_comp_inl_inr`, so the coproduct source is no restriction. -/
def parameterProj : (D₁.coprod D₂).ker →L[𝕜] Λ :=
  (ContinuousLinearMap.snd 𝕜 E Λ).comp (D₁.coprod D₂).ker.subtypeL

/-- The parameter projection reads off the parameter component of a candidate tangent vector. -/
@[simp]
theorem parameterProj_apply (v : (D₁.coprod D₂).ker) : parameterProj D₁ D₂ v = (v : E × Λ).2 :=
  (rfl)

/-! ### Exactness at the candidate tangent space: the kernel of the projection -/

/-- The embedding `x ↦ (x, 0)` of `ker D₁` into the kernel of the total linearization: the formal
tangent directions to the universal zero set along which the parameter does not move. -/
def kerCoprodHom : D₁.ker →ₗ[𝕜] (D₁.coprod D₂).ker where
  toFun x := ⟨((x : E), 0), by simp⟩
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The embedding sends `x` to the pair `(x, 0)`. -/
@[simp]
theorem kerCoprodHom_apply (x : D₁.ker) : (kerCoprodHom D₁ D₂ x : E × Λ) = ((x : E), 0) :=
  (rfl)

/-- The embedding `x ↦ (x, 0)` is injective, which is exactness of the sequence at `ker D₁`. -/
theorem kerCoprodHom_injective : Function.Injective (kerCoprodHom D₁ D₂) := by
  intro x y hxy
  have h : ((x : E), (0 : Λ)) = ((y : E), (0 : Λ)) := by
    simpa using congrArg (fun v : (D₁.coprod D₂).ker => (v : E × Λ)) hxy
  exact Subtype.ext (congrArg Prod.fst h)

/-- The formal tangent directions along which the parameter does not move are exactly the
solutions of the linearized equation at the fixed parameter. -/
theorem range_kerCoprodHom :
    LinearMap.range (kerCoprodHom D₁ D₂) = (parameterProj D₁ D₂).ker := by
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

/-- Exactness of `0 → ker D₁ → ker (D₁.coprod D₂) → Λ` at the middle term. -/
theorem exact_kerCoprodHom_parameterProj :
    Function.Exact (kerCoprodHom D₁ D₂) (parameterProj D₁ D₂) :=
  LinearMap.exact_iff.mpr (range_kerCoprodHom D₁ D₂).symm

/-- **The kernel of the parameter projection is the kernel of `D₁`**, embedded by `x ↦ (x, 0)`. -/
noncomputable def kerParameterProjEquiv :
    D₁.ker ≃ₗ[𝕜] (parameterProj D₁ D₂).ker :=
  (LinearEquiv.ofInjective _ (kerCoprodHom_injective D₁ D₂)).trans
    (LinearEquiv.ofEq _ _ (range_kerCoprodHom D₁ D₂))

/-- The identification of `ker D₁` with the kernel of the projection is `x ↦ (x, 0)`. -/
@[simp]
theorem kerParameterProjEquiv_apply (x : D₁.ker) :
    ((kerParameterProjEquiv D₁ D₂ x : (D₁.coprod D₂).ker) : E × Λ) = ((x : E), 0) :=
  (rfl)

/-- The kernel of the parameter projection has the same dimension as the kernel of `D₁`. -/
theorem finrank_ker_parameterProj :
    finrank 𝕜 ((parameterProj D₁ D₂).ker) = finrank 𝕜 D₁.ker :=
  (kerParameterProjEquiv D₁ D₂).finrank_eq.symm

/-- The kernel of the parameter projection is finite dimensional as soon as that of `D₁` is. -/
theorem finiteDimensional_ker_parameterProj [FiniteDimensional 𝕜 D₁.ker] :
    FiniteDimensional 𝕜 ((parameterProj D₁ D₂).ker) :=
  (kerParameterProjEquiv D₁ D₂).finiteDimensional

/-! ### Exactness at the parameter space: the range of the projection -/

/-- The range of the parameter projection is the set of parameter directions whose infinitesimal
effect `D₂ l` on the equation can already be undone by moving the solution.

No hypothesis on `D₁` or on the total linearization is needed. -/
theorem range_parameterProj :
    (parameterProj D₁ D₂).range = D₁.range.comap (D₂ : Λ →ₗ[𝕜] F) := by
  ext l
  simp only [LinearMap.mem_range, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    parameterProj_apply]
  constructor
  · rintro ⟨⟨⟨x, m⟩, hk⟩, rfl⟩
    exact ⟨-x, by simpa [eq_comm, neg_eq_iff_add_eq_zero, add_comm] using hk⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨(-x, l), by simp [hx]⟩, rfl⟩

/-- A parameter direction lies in the range of the parameter projection exactly when its
infinitesimal effect on the equation is achievable by moving the solution. -/
theorem mem_range_parameterProj_iff {l : Λ} :
    l ∈ (parameterProj D₁ D₂).range ↔ D₂ l ∈ D₁.range := by
  rw [range_parameterProj]; rfl

/-- The map `Λ → F ⧸ range D₁` induced by `D₂`: it measures how far the infinitesimal effect of a
parameter direction is from being achievable by moving the solution. -/
noncomputable def cokerParameterMap : Λ →ₗ[𝕜] F ⧸ D₁.range :=
  D₁.range.mkQ ∘ₗ (D₂ : Λ →ₗ[𝕜] F)

/-- The induced map sends a parameter direction to the class of its infinitesimal effect. -/
@[simp]
theorem cokerParameterMap_apply (l : Λ) : cokerParameterMap D₁ D₂ l = D₁.range.mkQ (D₂ l) :=
  (rfl)

/-- The kernel of the map induced by `D₂` is the range of the parameter projection: this is
`TauCeti.range_parameterProj` read in the quotient. -/
theorem ker_cokerParameterMap :
    LinearMap.ker (cokerParameterMap D₁ D₂) = (parameterProj D₁ D₂).range := by
  rw [cokerParameterMap, LinearMap.ker_comp, Submodule.ker_mkQ, range_parameterProj]

/-- Exactness of `ker (D₁.coprod D₂) → Λ → F ⧸ range D₁` at the middle term. -/
theorem exact_parameterProj_cokerParameterMap :
    Function.Exact (parameterProj D₁ D₂) (cokerParameterMap D₁ D₂) :=
  LinearMap.exact_iff.mpr (ker_cokerParameterMap D₁ D₂)

/-- **The total linearization is surjective exactly when the parameter directions span the
cokernel of `D₁`.**

This is the criterion transversality arguments verify in practice: one exhibits enough
perturbations of the equation to cover every obstruction to solving the linearized equation. -/
theorem surjective_cokerParameterMap_iff :
    Function.Surjective (cokerParameterMap D₁ D₂) ↔ Function.Surjective (D₁.coprod D₂) := by
  constructor
  · intro h y
    obtain ⟨l, hl⟩ := h (D₁.range.mkQ y)
    obtain ⟨x, hx⟩ := (Submodule.Quotient.eq _).mp (by simpa using hl)
    have hx' : D₁ x = D₂ l - y := hx
    refine ⟨(-x, l), ?_⟩
    simp only [ContinuousLinearMap.coprod_apply, map_neg, hx']
    abel
  · intro h y
    obtain ⟨v, rfl⟩ := D₁.range.mkQ_surjective y
    obtain ⟨⟨x, l⟩, hx⟩ := h v
    refine ⟨l, ?_⟩
    simp only [cokerParameterMap_apply, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    have hxx : D₂ l - v = -D₁ x := by rw [← hx]; simp
    rw [hxx]
    exact D₁.range.neg_mem (LinearMap.mem_range_self (D₁ : E →ₗ[𝕜] F) x)

/-! ### The cokernel of the projection -/

/-- **For a surjective total linearization, the cokernel of the parameter projection is the
cokernel of `D₁`**, identified by the map induced by `D₂`.

Injectivity of that induced map is `TauCeti.ker_cokerParameterMap`, which holds unconditionally;
surjectivity of the total linearization is what makes it onto. -/
noncomputable def quotientRangeParameterProjEquiv (hD : Function.Surjective (D₁.coprod D₂)) :
    (Λ ⧸ (parameterProj D₁ D₂).range) ≃ₗ[𝕜] F ⧸ D₁.range :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerParameterMap D₁ D₂).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ ((surjective_cokerParameterMap_iff D₁ D₂).mpr hD))

/-- The cokernel equivalence sends the class of `l` to the class of `D₂ l`. -/
@[simp]
theorem quotientRangeParameterProjEquiv_mk (hD : Function.Surjective (D₁.coprod D₂)) (l : Λ) :
    quotientRangeParameterProjEquiv D₁ D₂ hD (Submodule.Quotient.mk l) =
      Submodule.Quotient.mk (D₂ l) :=
  (rfl)

/-- For a surjective total linearization, the cokernel of the parameter projection has the same
dimension as the cokernel of `D₁`. -/
theorem finrank_quotient_range_parameterProj (hD : Function.Surjective (D₁.coprod D₂)) :
    finrank 𝕜 (Λ ⧸ (parameterProj D₁ D₂).range) = finrank 𝕜 (F ⧸ D₁.range) :=
  (quotientRangeParameterProjEquiv D₁ D₂ hD).finrank_eq

/-- For a surjective total linearization, the cokernel of the parameter projection is finite
dimensional as soon as that of `D₁` is. -/
theorem finiteDimensional_quotient_range_parameterProj (hD : Function.Surjective (D₁.coprod D₂))
    [FiniteDimensional 𝕜 (F ⧸ D₁.range)] :
    FiniteDimensional 𝕜 (Λ ⧸ (parameterProj D₁ D₂).range) :=
  (quotientRangeParameterProjEquiv D₁ D₂ hD).symm.finiteDimensional

/-- Assuming the total linearization is surjective, the parameter projection is onto exactly when
`D₁` is. In the nonlinear application, this says that a parameter is a regular value of the
projection from the universal zero set precisely when the equation it indexes is regular. -/
theorem range_parameterProj_eq_top_iff (hD : (D₁.coprod D₂).range = ⊤) :
    (parameterProj D₁ D₂).range = ⊤ ↔ D₁.range = ⊤ := by
  rw [ContinuousLinearMap.range_coprod] at hD
  refine ⟨fun h => ?_, fun h => by rw [range_parameterProj, h, Submodule.comap_top]⟩
  refine top_unique ?_
  rw [← hD]
  refine sup_le le_rfl ?_
  rintro _ ⟨l, rfl⟩
  exact (mem_range_parameterProj_iff D₁ D₂).mp (h ▸ Submodule.mem_top)

/-- The `Function.Surjective` form of `TauCeti.range_parameterProj_eq_top_iff`. -/
theorem surjective_parameterProj_iff (hD : Function.Surjective (D₁.coprod D₂)) :
    Function.Surjective (parameterProj D₁ D₂) ↔ Function.Surjective D₁ := by
  have h := range_parameterProj_eq_top_iff D₁ D₂ (LinearMap.range_eq_top.mpr hD)
  rw [LinearMap.range_eq_top, LinearMap.range_eq_top] at h
  exact h

/-! ### The index and the Fredholm property -/

/-- **The parameter projection of a surjective total linearization has the same index as `D₁`.**

Consequently, once the nonlinear hypotheses of `TauCeti.Analysis.Fredholm.LevelSet` and a smooth
manifold chart on the universal zero set are supplied, the corresponding regular fibre has
dimension `index D₁`.

Neither operator is assumed Fredholm: both sides are differences of `Module.finrank`s, and the
exact sequence matches the four dimensions in pairs, junk values included. -/
theorem index_parameterProj (hD : Function.Surjective (D₁.coprod D₂)) :
    ContinuousLinearMap.index (parameterProj D₁ D₂) = ContinuousLinearMap.index D₁ := by
  rw [ContinuousLinearMap.index_eq_finrank_sub, ContinuousLinearMap.index_eq_finrank_sub,
    finrank_ker_parameterProj, finrank_quotient_range_parameterProj D₁ D₂ hD]

section Banach

variable [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace Λ]

/-- **The parameter projection of a surjective total linearization is Fredholm** as soon as `D₁`
is, over Banach spaces; by `TauCeti.index_parameterProj` its index is that of `D₁`.

After supplying a smooth manifold chart on the universal zero set, this is the hypothesis under
which the Sard--Smale theorem applies to its projection to the parameter space, which is the step
the parametric transversality theorem turns on. -/
theorem isFredholm_parameterProj (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    ContinuousLinearMap.IsFredholm (parameterProj D₁ D₂) := by
  have hker := hD₁.finite_ker
  have hcoker := hD₁.finite_coker
  exact .of_finite_ker_coker _ (finiteDimensional_ker_parameterProj D₁ D₂)
    (finiteDimensional_quotient_range_parameterProj D₁ D₂ hD)

end Banach

end TauCeti
