/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# Complex-linear and complex-antilinear parts of a real-linear map

Fix real vector spaces (or modules) `V` and `W` equipped with almost complex structures, that
is, real-linear endomorphisms `J : V →ₗ[ℝ] V` and `J' : W →ₗ[ℝ] W` with `J ∘ J = -1` and
`J' ∘ J' = -1`. A real-linear map `F : V →ₗ[ℝ] W` is **complex linear** (with respect to the
pair `(J, J')`) when it commutes with the structures, `F ∘ J = J' ∘ F`, and **complex
antilinear** when it anticommutes, `F ∘ J = -(J' ∘ F)`.

Every real-linear map splits canonically as the sum of a complex-linear and a complex-antilinear
map,
```
F = complexLinearPart J J' F + complexAntilinearPart J J' F,
```
with `complexLinearPart J J' F = ½ (F - J' ∘ F ∘ J)` and
`complexAntilinearPart J J' F = ½ (F + J' ∘ F ∘ J)`. This is the pointwise linearization at the
heart of the holomorphic theory: a smooth map between almost complex manifolds is
`J`-holomorphic exactly when its differential is complex linear, equivalently when its
complex-antilinear part `∂̄` vanishes. This file develops the linear-algebra layer of that
statement, before any smoothness or bundle structure is introduced.

## Main definitions

* `TauCeti.IsComplexLinear J J' F`: the commutation condition `F ∘ J = J' ∘ F`.
* `TauCeti.IsComplexAntilinear J J' F`: the anticommutation condition `F ∘ J = -(J' ∘ F)`.
* `TauCeti.complexLinearPart J J' F`: the complex-linear part `½ (F - J' ∘ F ∘ J)` (the `∂`
  operator).
* `TauCeti.complexAntilinearPart J J' F`: the complex-antilinear part `½ (F + J' ∘ F ∘ J)`
  (the `∂̄` operator).
* `TauCeti.complexLinearPartLinearMap J J'` /
  `TauCeti.complexAntilinearPartLinearMap J J'`: the corresponding real-linear operators on
  `V →ₗ[ℝ] W` (these become genuine projections only under `J ∘ J = -1` and `J' ∘ J' = -1`).
* `TauCeti.complexLinearMaps J J'` / `TauCeti.complexAntilinearMaps J J'`: the real subspaces of
  complex-linear and complex-antilinear maps.

## Main results

* `TauCeti.complexLinearPart_add_complexAntilinearPart`: the decomposition `∂ + ∂̄ = id`.
* `TauCeti.complexLinearPart_isComplexLinear` /
  `TauCeti.complexAntilinearPart_isComplexAntilinear`: the two parts land in their named classes.
* `TauCeti.isComplexLinear_iff_complexAntilinearPart_eq_zero`: `F` is complex linear iff its
  complex-antilinear part vanishes (the `∂̄ F = 0` characterization).
* `TauCeti.isCompl_complexLinearMaps`: the complex-linear and complex-antilinear maps are
  complementary subspaces of all real-linear maps.
* `TauCeti.isComplexLinear_arrowCongr_iff`: complex-linearity is preserved and reflected by
  conjugating source, target, and map along real-linear equivalences.

The sign conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Section 2.2, specialized to the pointwise real-linear setting.
-/

public section

namespace TauCeti

variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]

/-- A real-linear map `F : V →ₗ[ℝ] W` is complex linear for the pair of almost complex
structures `(J, J')` when it intertwines them: `F ∘ J = J' ∘ F`. -/
@[expose] def IsComplexLinear (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) : Prop :=
  F ∘ₗ J = J' ∘ₗ F

/-- A real-linear map `F : V →ₗ[ℝ] W` is complex antilinear for the pair of almost complex
structures `(J, J')` when it anti-intertwines them: `F ∘ J = -(J' ∘ F)`. -/
@[expose] def IsComplexAntilinear (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) : Prop :=
  F ∘ₗ J = -(J' ∘ₗ F)

variable {J : V →ₗ[ℝ] V} {J' : W →ₗ[ℝ] W} {J'' : U →ₗ[ℝ] U}

/-- Complex linearity restated as its defining commutation equation `F ∘ J = J' ∘ F`. -/
@[simp, grind =]
theorem isComplexLinear_iff {F : V →ₗ[ℝ] W} :
    IsComplexLinear J J' F ↔ F ∘ₗ J = J' ∘ₗ F := Iff.rfl

/-- Complex antilinearity restated as its defining anticommutation equation
`F ∘ J = -(J' ∘ F)`. -/
@[simp, grind =]
theorem isComplexAntilinear_iff {F : V →ₗ[ℝ] W} :
    IsComplexAntilinear J J' F ↔ F ∘ₗ J = -(J' ∘ₗ F) := Iff.rfl

/-- The pointwise form of complex linearity: `F (J v) = J' (F v)`. -/
theorem IsComplexLinear.apply {F : V →ₗ[ℝ] W} (h : IsComplexLinear J J' F) (v : V) :
    F (J v) = J' (F v) := by
  have h' : F ∘ₗ J = J' ∘ₗ F := h
  have := LinearMap.congr_fun h' v
  simpa using this

/-- A real-linear map intertwining `J` and `J'` pointwise is complex linear. -/
theorem isComplexLinear_of_apply {F : V →ₗ[ℝ] W} (h : ∀ v, F (J v) = J' (F v)) :
    IsComplexLinear J J' F :=
  LinearMap.ext fun v => by simpa using h v

/-- Raw complex-linearity is preserved and reflected by conjugating source and target along
linear equivalences. -/
@[simp]
theorem isComplexLinear_arrowCongr_iff {V₂ W₂ : Type*}
    [AddCommGroup V₂] [Module ℝ V₂] [AddCommGroup W₂] [Module ℝ W₂]
    {F : V →ₗ[ℝ] W} (eV : V ≃ₗ[ℝ] V₂) (eW : W ≃ₗ[ℝ] W₂) :
    IsComplexLinear (eV.conj J) (eW.conj J') (eV.arrowCongr eW F) ↔
      IsComplexLinear J J' F := by
  constructor
  · intro hF
    refine isComplexLinear_of_apply fun v => ?_
    have h := hF.apply (eV v)
    simpa [LinearEquiv.arrowCongr_apply] using congrArg eW.symm h
  · intro hF
    refine isComplexLinear_of_apply fun v => ?_
    simp [LinearEquiv.arrowCongr_apply, hF.apply]

/-- The pointwise form of complex antilinearity: `F (J v) = -(J' (F v))`. -/
theorem IsComplexAntilinear.apply {F : V →ₗ[ℝ] W} (h : IsComplexAntilinear J J' F) (v : V) :
    F (J v) = -(J' (F v)) := by
  have h' : F ∘ₗ J = -(J' ∘ₗ F) := h
  have := LinearMap.congr_fun h' v
  simpa using this

/-- A real-linear map anti-intertwining `J` and `J'` pointwise is complex antilinear. -/
theorem isComplexAntilinear_of_apply {F : V →ₗ[ℝ] W} (h : ∀ v, F (J v) = -(J' (F v))) :
    IsComplexAntilinear J J' F :=
  LinearMap.ext fun v => by simpa using h v

/-- The identity map is complex linear. -/
theorem isComplexLinear_id : IsComplexLinear J J (LinearMap.id) := by
  simp [IsComplexLinear]

/-- The zero map is complex linear. -/
theorem isComplexLinear_zero : IsComplexLinear J J' (0 : V →ₗ[ℝ] W) := by
  simp [IsComplexLinear]

/-- The zero map is complex antilinear. -/
theorem isComplexAntilinear_zero : IsComplexAntilinear J J' (0 : V →ₗ[ℝ] W) := by
  simp [IsComplexAntilinear]

/-- The negation of a complex-linear map is complex linear. -/
theorem IsComplexLinear.neg {F : V →ₗ[ℝ] W} (h : IsComplexLinear J J' F) :
    IsComplexLinear J J' (-F) :=
  isComplexLinear_of_apply fun v => by simp [h.apply v]

/-- Complex-linearity is unchanged after negating both source and target endomorphisms. -/
theorem IsComplexLinear.neg_neg {F : V →ₗ[ℝ] W} (h : IsComplexLinear J J' F) :
    IsComplexLinear (-J) (-J') F :=
  isComplexLinear_of_apply fun v => by simp [h.apply v]

/-- If a map is complex-linear after negating both endomorphisms, then it was complex-linear
before the sign change. -/
theorem IsComplexLinear.of_neg_neg {F : V →ₗ[ℝ] W}
    (h : IsComplexLinear (-J) (-J') F) : IsComplexLinear J J' F :=
  isComplexLinear_of_apply fun v => by
    simpa using congrArg Neg.neg (h.apply v)

/-- The negation of a complex-antilinear map is complex antilinear. -/
theorem IsComplexAntilinear.neg {F : V →ₗ[ℝ] W} (h : IsComplexAntilinear J J' F) :
    IsComplexAntilinear J J' (-F) :=
  isComplexAntilinear_of_apply fun v => by simp [h.apply v]

/-- Complex-antilinearity is unchanged after negating both source and target endomorphisms. -/
theorem IsComplexAntilinear.neg_neg {F : V →ₗ[ℝ] W} (h : IsComplexAntilinear J J' F) :
    IsComplexAntilinear (-J) (-J') F :=
  isComplexAntilinear_of_apply fun v => by simp [h.apply v]

/-- If a map is complex-antilinear after negating both endomorphisms, then it was
complex-antilinear before the sign change. -/
theorem IsComplexAntilinear.of_neg_neg {F : V →ₗ[ℝ] W}
    (h : IsComplexAntilinear (-J) (-J') F) : IsComplexAntilinear J J' F :=
  isComplexAntilinear_of_apply fun v => by
    simpa using congrArg Neg.neg (h.apply v)

/-- The composite of two complex-linear maps is complex linear. -/
theorem IsComplexLinear.comp {F : V →ₗ[ℝ] W} {G : W →ₗ[ℝ] U}
    (hG : IsComplexLinear J' J'' G) (hF : IsComplexLinear J J' F) :
    IsComplexLinear J J'' (G ∘ₗ F) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, hG.apply (F v)]

/-- The composite of two complex-antilinear maps is complex linear. -/
theorem IsComplexAntilinear.comp {F : V →ₗ[ℝ] W} {G : W →ₗ[ℝ] U}
    (hG : IsComplexAntilinear J' J'' G) (hF : IsComplexAntilinear J J' F) :
    IsComplexLinear J J'' (G ∘ₗ F) :=
  isComplexLinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, map_neg, hG.apply (F v), _root_.neg_neg]

/-- A complex-linear map after a complex-antilinear map is complex antilinear. -/
theorem IsComplexLinear.comp_antilinear {F : V →ₗ[ℝ] W} {G : W →ₗ[ℝ] U}
    (hG : IsComplexLinear J' J'' G) (hF : IsComplexAntilinear J J' F) :
    IsComplexAntilinear J J'' (G ∘ₗ F) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, map_neg, hG.apply (F v)]

/-- A complex-antilinear map after a complex-linear map is complex antilinear. -/
theorem IsComplexAntilinear.comp_linear {F : V →ₗ[ℝ] W} {G : W →ₗ[ℝ] U}
    (hG : IsComplexAntilinear J' J'' G) (hF : IsComplexLinear J J' F) :
    IsComplexAntilinear J J'' (G ∘ₗ F) :=
  isComplexAntilinear_of_apply fun v => by
    simp only [LinearMap.comp_apply, hF.apply v, hG.apply (F v)]

/-- The complex-linear-part operator `F ↦ ∂F` as a real-linear map on `V →ₗ[ℝ] W`. -/
@[expose] noncomputable def complexLinearPartLinearMap (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) :
    (V →ₗ[ℝ] W) →ₗ[ℝ] (V →ₗ[ℝ] W) where
  toFun F := (2⁻¹ : ℝ) • (F - J' ∘ₗ F ∘ₗ J)
  map_add' F G := by
    ext v
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, map_add]
    module
  map_smul' c F := by
    ext v
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul]
    simp [RingHom.id_apply, smul_sub, smul_smul, mul_comm]

/-- The complex-antilinear-part operator `F ↦ ∂̄F` as a real-linear map on `V →ₗ[ℝ] W`. -/
@[expose] noncomputable def complexAntilinearPartLinearMap (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) :
    (V →ₗ[ℝ] W) →ₗ[ℝ] (V →ₗ[ℝ] W) where
  toFun F := (2⁻¹ : ℝ) • (F + J' ∘ₗ F ∘ₗ J)
  map_add' F G := by
    ext v
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
    module
  map_smul' c F := by
    ext v
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, map_smul]
    simp [RingHom.id_apply, smul_add, smul_smul, mul_comm]

/-- The defining formula for `complexLinearPartLinearMap J J'` on an input map. -/
@[simp]
theorem complexLinearPartLinearMap_apply (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexLinearPartLinearMap J J' F = (2⁻¹ : ℝ) • (F - J' ∘ₗ F ∘ₗ J) :=
  rfl

/-- The defining formula for `complexAntilinearPartLinearMap J J'` on an input map. -/
@[simp]
theorem complexAntilinearPartLinearMap_apply (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexAntilinearPartLinearMap J J' F = (2⁻¹ : ℝ) • (F + J' ∘ₗ F ∘ₗ J) :=
  rfl

/-- The complex-linear part `∂F = ½ (F - J' ∘ F ∘ J)` of a real-linear map. -/
@[expose] noncomputable def complexLinearPart (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] W :=
  complexLinearPartLinearMap J J' F

/-- The complex-antilinear part `∂̄F = ½ (F + J' ∘ F ∘ J)` of a real-linear map. -/
@[expose] noncomputable def complexAntilinearPart (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    V →ₗ[ℝ] W :=
  complexAntilinearPartLinearMap J J' F

/-- The defining formula for the complex-linear part as a linear-map equality. -/
theorem complexLinearPart_def (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexLinearPart J J' F = (2⁻¹ : ℝ) • (F - J' ∘ₗ F ∘ₗ J) :=
  rfl

/-- The defining formula for the complex-antilinear part as a linear-map equality. -/
theorem complexAntilinearPart_def (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexAntilinearPart J J' F = (2⁻¹ : ℝ) • (F + J' ∘ₗ F ∘ₗ J) :=
  rfl

/-- The pointwise formula for the complex-linear part:
`∂F v = 1/2 • (F v - J' (F (J v)))`. -/
@[simp]
theorem complexLinearPart_apply (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) (v : V) :
    complexLinearPart J J' F v = (2⁻¹ : ℝ) • (F v - J' (F (J v))) := by
  simp [complexLinearPart]

/-- The pointwise formula for the complex-antilinear part:
`∂̄F v = 1/2 • (F v + J' (F (J v)))`. -/
@[simp]
theorem complexAntilinearPart_apply (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) (v : V) :
    complexAntilinearPart J J' F v = (2⁻¹ : ℝ) • (F v + J' (F (J v))) := by
  simp [complexAntilinearPart]

/-- The canonical decomposition `∂F + ∂̄F = F`. -/
@[simp]
theorem complexLinearPart_add_complexAntilinearPart (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W)
    (F : V →ₗ[ℝ] W) :
    complexLinearPart J J' F + complexAntilinearPart J J' F = F := by
  ext v
  simp only [LinearMap.add_apply, complexLinearPart_apply, complexAntilinearPart_apply]
  module

/-- The complex-linear-part and complex-antilinear-part operators add to the identity. -/
@[simp]
theorem complexLinearPartLinearMap_add_complexAntilinearPartLinearMap
    (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) :
    complexLinearPartLinearMap J J' + complexAntilinearPartLinearMap J J' = LinearMap.id := by
  ext F v
  exact LinearMap.congr_fun (complexLinearPart_add_complexAntilinearPart J J' F) v

/-- The complex-linear part is additive in `F`. -/
@[simp]
theorem complexLinearPart_add (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F G : V →ₗ[ℝ] W) :
    complexLinearPart J J' (F + G)
      = complexLinearPart J J' F + complexLinearPart J J' G :=
  map_add (complexLinearPartLinearMap J J') F G

/-- The complex-antilinear part is additive in `F`. -/
@[simp]
theorem complexAntilinearPart_add (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F G : V →ₗ[ℝ] W) :
    complexAntilinearPart J J' (F + G)
      = complexAntilinearPart J J' F + complexAntilinearPart J J' G :=
  map_add (complexAntilinearPartLinearMap J J') F G

/-- The complex-linear part commutes with real scalar multiplication in `F`. -/
@[simp]
theorem complexLinearPart_smul (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (c : ℝ) (F : V →ₗ[ℝ] W) :
    complexLinearPart J J' (c • F) = c • complexLinearPart J J' F :=
  map_smul (complexLinearPartLinearMap J J') c F

/-- The complex-antilinear part commutes with real scalar multiplication in `F`. -/
@[simp]
theorem complexAntilinearPart_smul (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (c : ℝ) (F : V →ₗ[ℝ] W) :
    complexAntilinearPart J J' (c • F) = c • complexAntilinearPart J J' F :=
  map_smul (complexAntilinearPartLinearMap J J') c F

/-- The complex-linear part of the zero map is zero. -/
@[simp]
theorem complexLinearPart_zero (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) :
    complexLinearPart J J' (0 : V →ₗ[ℝ] W) = 0 :=
  map_zero (complexLinearPartLinearMap J J')

/-- The complex-antilinear part of the zero map is zero. -/
@[simp]
theorem complexAntilinearPart_zero (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) :
    complexAntilinearPart J J' (0 : V →ₗ[ℝ] W) = 0 :=
  map_zero (complexAntilinearPartLinearMap J J')

/-- The complex-linear part commutes with negation in `F`. -/
@[simp]
theorem complexLinearPart_neg (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexLinearPart J J' (-F) = -complexLinearPart J J' F :=
  map_neg (complexLinearPartLinearMap J J') F

/-- The complex-antilinear part commutes with negation in `F`. -/
@[simp]
theorem complexAntilinearPart_neg (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) (F : V →ₗ[ℝ] W) :
    complexAntilinearPart J J' (-F) = -complexAntilinearPart J J' F :=
  map_neg (complexAntilinearPartLinearMap J J') F

/-- Applying an almost complex structure twice negates, in pointwise form. -/
private theorem sq_apply (hsq : J ∘ₗ J = -LinearMap.id) (v : V) : J (J v) = -v := by
  have := LinearMap.congr_fun hsq v
  simpa using this

/-- The complex-linear part really is complex linear. -/
theorem complexLinearPart_isComplexLinear (hJ : J ∘ₗ J = -LinearMap.id)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[ℝ] W) :
    IsComplexLinear J J' (complexLinearPart J J' F) := by
  refine isComplexLinear_of_apply fun v => ?_
  simp only [complexLinearPart_apply, sq_apply hJ, sq_apply hJ', map_smul, map_sub, map_neg]
  module

/-- The complex-antilinear part really is complex antilinear. -/
theorem complexAntilinearPart_isComplexAntilinear (hJ : J ∘ₗ J = -LinearMap.id)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[ℝ] W) :
    IsComplexAntilinear J J' (complexAntilinearPart J J' F) := by
  refine isComplexAntilinear_of_apply fun v => ?_
  simp only [complexAntilinearPart_apply, sq_apply hJ, sq_apply hJ', map_smul, map_add, map_neg]
  module

/-- A real-linear map is complex linear exactly when its complex-antilinear part vanishes:
the linear-algebra shadow of "`F` is `J`-holomorphic iff `∂̄F = 0`". -/
theorem isComplexLinear_iff_complexAntilinearPart_eq_zero
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[ℝ] W) :
    IsComplexLinear J J' F ↔ complexAntilinearPart J J' F = 0 := by
  constructor
  · intro h
    ext v
    have hv := h.apply v
    simp only [complexAntilinearPart_apply, LinearMap.zero_apply, hv, sq_apply hJ']
    module
  · intro h
    refine isComplexLinear_of_apply fun v => ?_
    have hv : complexAntilinearPart J J' F v = 0 := by simp [h]
    rw [complexAntilinearPart_apply] at hv
    have hv2 : F v + J' (F (J v)) = 0 := by
      have h2 : (2 : ℝ) • ((2⁻¹ : ℝ) • (F v + J' (F (J v)))) = (2 : ℝ) • (0 : W) := by rw [hv]
      rwa [smul_smul, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_smul, smul_zero] at h2
    have e1 : F v = -(J' (F (J v))) := eq_neg_of_add_eq_zero_left hv2
    rw [e1, map_neg, sq_apply hJ', neg_neg]

/-- A real-linear map is complex antilinear exactly when its complex-linear part vanishes. -/
theorem isComplexAntilinear_iff_complexLinearPart_eq_zero
    (hJ' : J' ∘ₗ J' = -LinearMap.id) (F : V →ₗ[ℝ] W) :
    IsComplexAntilinear J J' F ↔ complexLinearPart J J' F = 0 := by
  constructor
  · intro h
    ext v
    have hv := h.apply v
    simp only [complexLinearPart_apply, LinearMap.zero_apply, hv, map_neg, sq_apply hJ']
    module
  · intro h
    refine isComplexAntilinear_of_apply fun v => ?_
    have hv : complexLinearPart J J' F v = 0 := by simp [h]
    rw [complexLinearPart_apply] at hv
    have hv2 : F v - J' (F (J v)) = 0 := by
      have h2 : (2 : ℝ) • ((2⁻¹ : ℝ) • (F v - J' (F (J v)))) = (2 : ℝ) • (0 : W) := by rw [hv]
      rwa [smul_smul, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_smul, smul_zero] at h2
    have e1 : F v = J' (F (J v)) := sub_eq_zero.mp hv2
    rw [e1, sq_apply hJ', neg_neg]

/-- A complex-linear map equals its own complex-linear part. -/
theorem IsComplexLinear.complexLinearPart_eq {F : V →ₗ[ℝ] W} (h : IsComplexLinear J J' F)
    (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexLinearPart J J' F = F := by
  have hz : complexAntilinearPart J J' F = 0 :=
    (isComplexLinear_iff_complexAntilinearPart_eq_zero hJ' F).mp h
  have hsum := complexLinearPart_add_complexAntilinearPart J J' F
  rw [hz, add_zero] at hsum
  exact hsum

/-- The complex-antilinear part of a complex-linear map vanishes. -/
theorem IsComplexLinear.complexAntilinearPart_eq_zero {F : V →ₗ[ℝ] W}
    (h : IsComplexLinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexAntilinearPart J J' F = 0 :=
  (isComplexLinear_iff_complexAntilinearPart_eq_zero hJ' F).mp h

/-- A complex-antilinear map equals its own complex-antilinear part. -/
theorem IsComplexAntilinear.complexAntilinearPart_eq {F : V →ₗ[ℝ] W}
    (h : IsComplexAntilinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexAntilinearPart J J' F = F := by
  have hz : complexLinearPart J J' F = 0 :=
    (isComplexAntilinear_iff_complexLinearPart_eq_zero hJ' F).mp h
  have hsum := complexLinearPart_add_complexAntilinearPart J J' F
  rw [hz, zero_add] at hsum
  exact hsum

/-- The complex-linear part of a complex-antilinear map vanishes. -/
theorem IsComplexAntilinear.complexLinearPart_eq_zero {F : V →ₗ[ℝ] W}
    (h : IsComplexAntilinear J J' F) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    complexLinearPart J J' F = 0 :=
  (isComplexAntilinear_iff_complexLinearPart_eq_zero hJ' F).mp h

/-- Uniqueness of the complex-linear/antilinear decomposition: if `F = A + B` with `A` complex
linear and `B` complex antilinear, then `A` and `B` are the canonical parts of `F`. -/
theorem complexLinearPart_eq_and_complexAntilinearPart_eq_of_decomp
    (hJ' : J' ∘ₗ J' = -LinearMap.id) {F A B : V →ₗ[ℝ] W}
    (hA : IsComplexLinear J J' A) (hB : IsComplexAntilinear J J' B) (hF : F = A + B) :
    A = complexLinearPart J J' F ∧ B = complexAntilinearPart J J' F := by
  refine ⟨?_, ?_⟩
  · rw [hF, complexLinearPart_add, hA.complexLinearPart_eq hJ',
      hB.complexLinearPart_eq_zero hJ', add_zero]
  · rw [hF, complexAntilinearPart_add, hA.complexAntilinearPart_eq_zero hJ',
      hB.complexAntilinearPart_eq hJ', zero_add]

/-- The real subspace of complex-linear maps `V →ₗ[ℝ] W` for the pair `(J, J')`. -/
def complexLinearMaps (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) : Submodule ℝ (V →ₗ[ℝ] W) where
  carrier := {F | IsComplexLinear J J' F}
  zero_mem' := isComplexLinear_zero
  add_mem' {F G} hF hG := by
    have hF' : IsComplexLinear J J' F := hF
    have hG' : IsComplexLinear J J' G := hG
    exact isComplexLinear_of_apply fun v => by
      simp only [LinearMap.add_apply, map_add, hF'.apply v, hG'.apply v]
  smul_mem' c {F} hF := by
    have hF' : IsComplexLinear J J' F := hF
    exact isComplexLinear_of_apply fun v => by
      simp only [LinearMap.smul_apply, map_smul, hF'.apply v]

/-- The real subspace of complex-antilinear maps `V →ₗ[ℝ] W` for the pair `(J, J')`. -/
def complexAntilinearMaps (J : V →ₗ[ℝ] V) (J' : W →ₗ[ℝ] W) : Submodule ℝ (V →ₗ[ℝ] W) where
  carrier := {F | IsComplexAntilinear J J' F}
  zero_mem' := isComplexAntilinear_zero
  add_mem' {F G} hF hG := by
    have hF' : IsComplexAntilinear J J' F := hF
    have hG' : IsComplexAntilinear J J' G := hG
    exact isComplexAntilinear_of_apply fun v => by
      simp only [LinearMap.add_apply, map_add, hF'.apply v, hG'.apply v]
      abel
  smul_mem' c {F} hF := by
    have hF' : IsComplexAntilinear J J' F := hF
    exact isComplexAntilinear_of_apply fun v => by
      simp only [LinearMap.smul_apply, map_smul, hF'.apply v]
      module

@[simp]
theorem mem_complexLinearMaps {F : V →ₗ[ℝ] W} :
    F ∈ complexLinearMaps J J' ↔ IsComplexLinear J J' F := Iff.rfl

@[simp]
theorem mem_complexAntilinearMaps {F : V →ₗ[ℝ] W} :
    F ∈ complexAntilinearMaps J J' ↔ IsComplexAntilinear J J' F := Iff.rfl

/-- For genuine almost complex structures, every real-linear map splits uniquely as a
complex-linear plus a complex-antilinear map: the two subspaces are complementary. -/
theorem isCompl_complexLinearMaps (hJ : J ∘ₗ J = -LinearMap.id) (hJ' : J' ∘ₗ J' = -LinearMap.id) :
    IsCompl (complexLinearMaps J J') (complexAntilinearMaps J J') := by
  constructor
  · rw [Submodule.disjoint_def]
    intro F hFlin hFanti
    have hlin : IsComplexLinear J J' F := hFlin
    have hanti : IsComplexAntilinear J J' F := hFanti
    have hlin_zero := hlin.complexAntilinearPart_eq_zero hJ'
    have hanti_zero := hanti.complexLinearPart_eq_zero hJ'
    simpa [hlin_zero, hanti_zero] using
      (complexLinearPart_add_complexAntilinearPart J J' F).symm
  · rw [codisjoint_iff, eq_top_iff]
    intro F _
    rw [Submodule.mem_sup]
    exact ⟨complexLinearPart J J' F,
      mem_complexLinearMaps.mpr (complexLinearPart_isComplexLinear hJ hJ' F),
      complexAntilinearPart J J' F,
      mem_complexAntilinearMaps.mpr (complexAntilinearPart_isComplexAntilinear hJ hJ' F),
      complexLinearPart_add_complexAntilinearPart J J' F⟩

end TauCeti
