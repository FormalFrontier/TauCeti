/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# Complex-linear real maps are exactly `ℂ`-linear maps

`TauCeti.AlmostComplexStructure.complexModule` turns an almost complex structure `J` on a real
module `V` (a real-linear `J` with `J ∘ J = -1`) into a genuine complex vector space structure,
with multiplication by `i` acting as `J`. That is the *object*-level half of the classical
dictionary (McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1). This
file supplies the *morphism*-level half: a real-linear map `F : V →ₗ[ℝ] W` intertwines two almost
complex structures, `F ∘ J = J' ∘ F` (`TauCeti.IsComplexLinearMap`), exactly when it is
`ℂ`-linear for the induced complex module structures `J.complexModule` and `J'.complexModule`.

This is the linear-algebra core of the statement that a smooth map between almost complex
manifolds is `J`-holomorphic precisely when its differential is `ℂ`-linear: the pointwise
differential is a real-linear map, and `J`-holomorphicity is exactly `ℂ`-linearity of that
differential for the fiberwise complex structures.

## Main declarations

* `TauCeti.IsComplexLinearMap.map_complexModule_smul`: a complex-linear real map respects the
  induced complex scalar action, `F (z • v) = z • F v`.
* `TauCeti.isComplexLinearMap_iff_complexModule_map_smul`: `F` intertwines `J` and `J'` iff it is
  `ℂ`-linear for the induced complex structures.
* `TauCeti.IsComplexLinearMap.toComplexLinearMap`: a complex-linear real map packaged as a genuine
  `ℂ`-linear map `V →ₗ[ℂ] W`.
* `TauCeti.isComplexLinearMap_restrictScalars`: restricting a `ℂ`-linear map to the real scalars
  gives a complex-linear real map.
* `TauCeti.complexLinearMapEquiv`: the bijection between complex-linear real maps and `ℂ`-linear
  maps, the morphism-level statement of the `J ↔ Module ℂ` dictionary.

The `Module ℂ V` and `Module ℂ W` instances are the non-canonical `complexModule` structures, so
they are introduced with `letI` exactly as in `ComplexModule.lean`, `Finrank.lean`, and
`Hermitian.lean`.
-/

public section

namespace TauCeti

variable {V W : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A complex-linear real map respects the induced complex scalar action: under the complex module
structures `J.complexModule` and `J'.complexModule`, `F (z • v) = z • F v`. -/
theorem IsComplexLinearMap.map_complexModule_smul {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F)
    (z : ℂ) (v : V) :
    letI := J.complexModule
    letI := J'.complexModule
    F (z • v) = z • F v := by
  let := J.complexModule
  let := J'.complexModule
  rw [J.complexModule_smul_def z v, J'.complexModule_smul_def z (F v), map_add, map_smul,
    map_smul, (isComplexLinearMap_iff_apply J J' F).mp hF v]

/-- A real-linear map intertwines `J` and `J'` exactly when it is `ℂ`-linear for the induced
complex module structures: `F (z • v) = z • F v` for all complex scalars `z`. -/
theorem isComplexLinearMap_iff_complexModule_map_smul (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (F : V →ₗ[ℝ] W) :
    IsComplexLinearMap J J' F ↔
      letI := J.complexModule
      letI := J'.complexModule
      ∀ (z : ℂ) (v : V), F (z • v) = z • F v := by
  let := J.complexModule
  let := J'.complexModule
  refine ⟨fun hF z v => hF.map_complexModule_smul z v, fun h => ?_⟩
  refine (isComplexLinearMap_iff_apply J J' F).mpr fun v => ?_
  have hv := h Complex.I v
  rwa [J.complexModule_I_smul, J'.complexModule_I_smul] at hv

/-- A complex-linear real map packaged as a genuine `ℂ`-linear map `V →ₗ[ℂ] W`, for the complex
module structures `J.complexModule` and `J'.complexModule` induced by the almost complex
structures. Its underlying function is the original map (`toComplexLinearMap_apply`). -/
@[expose] noncomputable def IsComplexLinearMap.toComplexLinearMap {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) :
    letI := J.complexModule
    letI := J'.complexModule
    V →ₗ[ℂ] W :=
  letI := J.complexModule
  letI := J'.complexModule
  { toFun := F
    map_add' := F.map_add
    map_smul' := fun z v => hF.map_complexModule_smul z v }

@[simp]
theorem IsComplexLinearMap.toComplexLinearMap_apply {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) (v : V) :
    letI := J.complexModule
    letI := J'.complexModule
    hF.toComplexLinearMap v = F v :=
  rfl

/-- Restricting a `ℂ`-linear map (for the induced complex module structures) to the real scalars
gives a real-linear map that intertwines `J` and `J'`. -/
theorem isComplexLinearMap_restrictScalars (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (G : letI := J.complexModule; letI := J'.complexModule; V →ₗ[ℂ] W) :
    letI := J.complexModule
    letI := J'.complexModule
    letI := J.complexModule_isScalarTower
    letI := J'.complexModule_isScalarTower
    IsComplexLinearMap J J' (G.restrictScalars ℝ) := by
  let := J.complexModule
  let := J'.complexModule
  let := J.complexModule_isScalarTower
  let := J'.complexModule_isScalarTower
  refine (isComplexLinearMap_iff_apply J J' _).mpr fun v => ?_
  simp only [LinearMap.restrictScalars_apply]
  rw [← J.complexModule_I_smul v, ← J'.complexModule_I_smul (G v), map_smul]

/-- Packaging a complex-linear real map as a `ℂ`-linear map and then forgetting back down to the
real scalars recovers the original map. -/
@[simp]
theorem IsComplexLinearMap.restrictScalars_toComplexLinearMap {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) :
    letI := J.complexModule
    letI := J'.complexModule
    letI := J.complexModule_isScalarTower
    letI := J'.complexModule_isScalarTower
    hF.toComplexLinearMap.restrictScalars ℝ = F := by
  let := J.complexModule
  let := J'.complexModule
  let := J.complexModule_isScalarTower
  let := J'.complexModule_isScalarTower
  exact LinearMap.ext fun _ => rfl

/-- Forgetting a `ℂ`-linear map down to the real scalars and repackaging recovers the original
`ℂ`-linear map. -/
@[simp]
theorem toComplexLinearMap_isComplexLinearMap_restrictScalars (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (G : letI := J.complexModule; letI := J'.complexModule; V →ₗ[ℂ] W) :
    letI := J.complexModule
    letI := J'.complexModule
    letI := J.complexModule_isScalarTower
    letI := J'.complexModule_isScalarTower
    (isComplexLinearMap_restrictScalars J J' G).toComplexLinearMap = G := by
  let := J.complexModule
  let := J'.complexModule
  let := J.complexModule_isScalarTower
  let := J'.complexModule_isScalarTower
  exact LinearMap.ext fun _ => rfl

/-- The morphism-level form of the dictionary between almost complex structures and complex module
structures: real-linear maps intertwining `J` and `J'` are in bijection with `ℂ`-linear maps for
the induced complex module structures `J.complexModule` and `J'.complexModule`. -/
@[expose] noncomputable def complexLinearMapEquiv (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) :
    letI := J.complexModule
    letI := J'.complexModule
    {F : V →ₗ[ℝ] W // IsComplexLinearMap J J' F} ≃ (V →ₗ[ℂ] W) :=
  letI := J.complexModule
  letI := J'.complexModule
  letI := J.complexModule_isScalarTower
  letI := J'.complexModule_isScalarTower
  { toFun := fun F => F.2.toComplexLinearMap
    invFun := fun G => ⟨G.restrictScalars ℝ, isComplexLinearMap_restrictScalars J J' G⟩
    left_inv := fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
    right_inv := fun _ => LinearMap.ext fun _ => rfl }

@[simp]
theorem complexLinearMapEquiv_apply_apply (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (Fc : letI := J.complexModule; letI := J'.complexModule;
      {F : V →ₗ[ℝ] W // IsComplexLinearMap J J' F}) (v : V) :
    letI := J.complexModule
    letI := J'.complexModule
    complexLinearMapEquiv J J' Fc v = (Fc : V →ₗ[ℝ] W) v :=
  rfl

@[simp]
theorem complexLinearMapEquiv_symm_apply (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (G : letI := J.complexModule; letI := J'.complexModule; V →ₗ[ℂ] W) (v : V) :
    letI := J.complexModule
    letI := J'.complexModule
    letI := J.complexModule_isScalarTower
    letI := J'.complexModule_isScalarTower
    ((complexLinearMapEquiv J J').symm G : V →ₗ[ℝ] W) v = G v :=
  rfl

end TauCeti
