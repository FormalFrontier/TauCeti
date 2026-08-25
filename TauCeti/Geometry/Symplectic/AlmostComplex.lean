/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Almost complex structures and compatible symplectic forms

This file starts the pointwise linear-algebra API for the analytic Heegaard Floer roadmap.
It records almost complex structures on real modules, symplectic bilinear forms, and the
standard tameness and compatibility predicates between them.

These are the fiberwise definitions used before introducing smooth bundles, almost complex
manifolds, and `J`-holomorphic maps. The smooth manifold layer should reuse these predicates
on tangent fibers rather than restating the linear algebra.

## Main declarations

* `TauCeti.AlmostComplexStructure`: a real-linear endomorphism `J` with `J^2 = -1`.
* `TauCeti.IsComplexLinearMap`: a real-linear map intertwining two almost complex structures.
* `TauCeti.SymplecticForm`: an alternating, nondegenerate real bilinear form.
* `TauCeti.SymplecticForm.apply_smul_add_smul`: evaluation of a symplectic form on the plane
  spanned by two vectors, and `TauCeti.SymplecticForm.exists_apply_eq_one`: existence of a
  hyperbolic partner for every nonzero vector.
* `TauCeti.SymplecticForm.Tames`: the positivity condition `0 < ω v (J v)` for `v ≠ 0`.
* `TauCeti.SymplecticForm.Compatible`: `J`-invariance plus positivity of `ω(·, J ·)`.
* `TauCeti.AlmostComplexStructure.product`: the standard almost complex structure on
  `V × V`, sending `(x, y)` to `(-y, x)`.

The definitions follow the standard conventions in McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Section 2.2, specialized here to the
pointwise real-linear setting.
-/

public section

namespace TauCeti

open LinearMap

variable {V W X : Type*}

/-- A pointwise almost complex structure is a real-linear endomorphism whose square is `-1`.

This is the fiberwise object underlying an almost complex structure on a real vector bundle or
manifold. Smoothness is deliberately not bundled here; the analytic roadmap needs the linear
algebra separately on each tangent space. -/
structure AlmostComplexStructure (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The real-linear endomorphism usually denoted `J`. -/
  toLinearMap : V →ₗ[ℝ] V
  /-- The defining identity `J ∘ J = -1`. -/
  square_neg : toLinearMap.comp toLinearMap = -LinearMap.id

namespace AlmostComplexStructure

variable [AddCommGroup V] [Module ℝ V]

/-- The underlying linear map determines an almost complex structure: the only data is the
endomorphism, the defining identity being a proposition. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : AlmostComplexStructure V → (V →ₗ[ℝ] V)) := by
  rintro ⟨L, hL⟩ ⟨L', hL'⟩ h
  subst h
  rfl

instance : CoeFun (AlmostComplexStructure V) fun _ => V → V :=
  ⟨fun J => J.toLinearMap⟩

/-- Applying `J` twice gives `-v`. -/
@[simp]
lemma apply_apply (J : AlmostComplexStructure V) (v : V) : J (J v) = -v := by
  have h := LinearMap.congr_fun J.square_neg v
  simpa using h

/-- The underlying linear map of an almost complex structure is injective. -/
lemma injective (J : AlmostComplexStructure V) : Function.Injective J := by
  intro v w h
  have h' : J (J v) = J (J w) := congrArg J h
  simpa using h'

/-- The underlying linear map of an almost complex structure is surjective. -/
lemma surjective (J : AlmostComplexStructure V) : Function.Surjective J := by
  intro v
  exact ⟨-J v, by simp⟩

/-- The linear equivalence attached to an almost complex structure.

Its inverse is `-J`; this is often the convenient way to move bilinear-form statements across
`J`. -/
@[expose] def linearEquiv (J : AlmostComplexStructure V) : V ≃ₗ[ℝ] V where
  toLinearMap := J.toLinearMap
  invFun v := -J v
  left_inv v := by simp
  right_inv v := by simp

@[simp]
lemma linearEquiv_apply (J : AlmostComplexStructure V) (v : V) :
    J.linearEquiv v = J v := rfl

@[simp]
lemma linearEquiv_symm_apply (J : AlmostComplexStructure V) (v : V) :
    J.linearEquiv.symm v = -J v := rfl

@[simp]
lemma map_eq_zero_iff (J : AlmostComplexStructure V) {v : V} :
    J v = 0 ↔ v = 0 :=
  J.injective.eq_iff' J.toLinearMap.map_zero

lemma map_ne_zero_iff (J : AlmostComplexStructure V) {v : V} :
    J v ≠ 0 ↔ v ≠ 0 :=
  not_congr J.map_eq_zero_iff

/-- Two almost complex structures agreeing pointwise are equal. -/
@[ext]
lemma ext {J K : AlmostComplexStructure V} (h : ∀ v, J v = K v) : J = K := by
  cases J
  cases K
  congr 1
  exact LinearMap.ext h

/-- The negation of an almost complex structure is again an almost complex structure. -/
@[expose] def neg (J : AlmostComplexStructure V) : AlmostComplexStructure V where
  toLinearMap := -J.toLinearMap
  square_neg := by
    ext v
    simp

instance : Neg (AlmostComplexStructure V) :=
  ⟨neg⟩

@[simp]
lemma neg_toLinearMap (J : AlmostComplexStructure V) :
    (-J).toLinearMap = -J.toLinearMap := rfl

@[simp]
lemma neg_apply (J : AlmostComplexStructure V) (v : V) :
    (-J) v = -J v := rfl

/-- The standard almost complex structure on `V × V`, sending `(x, y)` to `(-y, x)`. -/
@[expose] def product (V : Type*) [AddCommGroup V] [Module ℝ V] :
    AlmostComplexStructure (V × V) where
  toLinearMap :=
    { toFun := fun v => (-v.2, v.1)
      map_add' := by intro v w; ext <;> simp [add_comm]
      map_smul' := by intro c v; ext <;> simp }
  square_neg := by
    ext v <;> simp

@[simp]
lemma product_apply (v : V × V) :
    product V v = (-v.2, v.1) := rfl

end AlmostComplexStructure

section ComplexLinearMap

variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup X] [Module ℝ X]

/-- A real-linear map is complex-linear with respect to two fixed pointwise
almost complex structures if it intertwines them. -/
@[expose] def IsComplexLinearMap (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (F : V →ₗ[ℝ] W) : Prop :=
  F.comp J.toLinearMap = J'.toLinearMap.comp F

/-- The bundled almost-complex predicate is the raw complex-linearity predicate applied to the
underlying endomorphisms. -/
lemma isComplexLinearMap_iff_isComplexLinear (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (F : V →ₗ[ℝ] W) :
    IsComplexLinearMap J J' F ↔ IsComplexLinear J.toLinearMap J'.toLinearMap F :=
  Iff.rfl

/-- Rewrite complex-linearity of a real-linear map as the pointwise equation
`F (J v) = J' (F v)`. -/
lemma isComplexLinearMap_iff_apply (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (F : V →ₗ[ℝ] W) :
    IsComplexLinearMap J J' F ↔ ∀ v, F (J v) = J' (F v) :=
  LinearMap.ext_iff

/-- Complex-linearity for almost complex structures is membership in the existing submodule of
raw-linear complex-linear maps. -/
lemma isComplexLinearMap_iff_mem_complexLinearMaps (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (F : V →ₗ[ℝ] W) :
    IsComplexLinearMap J J' F ↔ F ∈ complexLinearMaps J.toLinearMap J'.toLinearMap := by
  rw [isComplexLinearMap_iff_isComplexLinear, mem_complexLinearMaps]

/-- The zero map is complex-linear for any source and target almost complex structures. -/
@[simp]
lemma isComplexLinearMap_zero (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W) :
    IsComplexLinearMap J J' (0 : V →ₗ[ℝ] W) :=
  isComplexLinear_zero

/-- Complex-linear maps are closed under addition. -/
lemma IsComplexLinearMap.add {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {F G : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F)
    (hG : IsComplexLinearMap J J' G) : IsComplexLinearMap J J' (F + G) := by
  rw [isComplexLinearMap_iff_mem_complexLinearMaps] at hF hG ⊢
  exact (complexLinearMaps J.toLinearMap J'.toLinearMap).add_mem hF hG

/-- Complex-linear maps are closed under negation. -/
lemma IsComplexLinearMap.neg {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap J J' (-F) :=
  IsComplexLinear.neg hF

/-- Negating a map preserves and reflects complex-linearity. -/
@[simp]
lemma isComplexLinearMap_neg_iff {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {F : V →ₗ[ℝ] W} :
    IsComplexLinearMap J J' (-F) ↔ IsComplexLinearMap J J' F :=
  ⟨fun hF => by simpa using hF.neg, fun hF => hF.neg⟩

/-- Complex-linearity is unchanged after negating both the source and target almost complex
structures. -/
lemma IsComplexLinearMap.neg_neg {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap (-J) (-J') F := by
  rw [isComplexLinearMap_iff_isComplexLinear] at hF ⊢
  simpa [AlmostComplexStructure.neg_toLinearMap] using
    (IsComplexLinear.neg_neg (J := J.toLinearMap) (J' := J'.toLinearMap) (F := F) hF)

/-- If a map is complex-linear after negating both structures, then it was complex-linear before
the sign change. -/
lemma IsComplexLinearMap.of_neg_neg {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W}
    (hF : IsComplexLinearMap (-J) (-J') F) : IsComplexLinearMap J J' F := by
  rw [isComplexLinearMap_iff_isComplexLinear] at hF ⊢
  exact IsComplexLinear.of_neg_neg (by simpa [AlmostComplexStructure.neg_toLinearMap] using hF)

/-- Negating both almost complex structures leaves the complex-linearity condition unchanged. -/
@[simp]
lemma isComplexLinearMap_neg_neg_iff {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} :
    IsComplexLinearMap (-J) (-J') F ↔ IsComplexLinearMap J J' F :=
  ⟨fun hF => hF.of_neg_neg, fun hF => hF.neg_neg⟩

/-- Complex-linear maps are closed under subtraction. -/
lemma IsComplexLinearMap.sub {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {F G : V →ₗ[ℝ] W} (hF : IsComplexLinearMap J J' F)
    (hG : IsComplexLinearMap J J' G) : IsComplexLinearMap J J' (F - G) := by
  rw [isComplexLinearMap_iff_mem_complexLinearMaps] at hF hG ⊢
  exact (complexLinearMaps J.toLinearMap J'.toLinearMap).sub_mem hF hG

/-- Complex-linear maps are closed under real scalar multiplication. -/
lemma IsComplexLinearMap.smul {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {F : V →ₗ[ℝ] W} (c : ℝ) (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap J J' (c • F) := by
  rw [isComplexLinearMap_iff_mem_complexLinearMaps] at hF ⊢
  exact (complexLinearMaps J.toLinearMap J'.toLinearMap).smul_mem c hF

/-- The identity map is complex-linear with respect to the same almost complex structure. -/
@[simp]
lemma isComplexLinearMap_id (J : AlmostComplexStructure V) :
    IsComplexLinearMap J J (LinearMap.id : V →ₗ[ℝ] V) :=
  isComplexLinear_id

/-- Complex-linear maps are closed under composition. -/
lemma IsComplexLinearMap.comp {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {J'' : AlmostComplexStructure X} {F : V →ₗ[ℝ] W} {G : W →ₗ[ℝ] X}
    (hG : IsComplexLinearMap J' J'' G) (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap J J'' (G.comp F) :=
  IsComplexLinear.comp hG hF

/-- An almost complex structure is complex-linear as a map from its module to itself. -/
@[simp]
lemma AlmostComplexStructure.isComplexLinearMap_toLinearMap (J : AlmostComplexStructure V) :
    IsComplexLinearMap J J J.toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  rfl

/-- Precomposing a complex-linear map by the source almost complex structure again gives a
complex-linear map. -/
lemma IsComplexLinearMap.comp_almostComplexStructure_toLinearMap
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W}
    (hF : IsComplexLinearMap J J' F) :
    IsComplexLinearMap J J' (F.comp J.toLinearMap) :=
  hF.comp J.isComplexLinearMap_toLinearMap

/-- If precomposition by the source almost complex structure is complex-linear, then the original
map was complex-linear. -/
lemma IsComplexLinearMap.of_comp_almostComplexStructure_toLinearMap
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W}
    (hF : IsComplexLinearMap J J' (F.comp J.toLinearMap)) :
    IsComplexLinearMap J J' F := by
  rw [isComplexLinearMap_iff_apply] at hF ⊢
  intro v
  have hrot : -F v = J' (F (J v)) := by
    calc
      -F v = F (-v) := (map_neg F v).symm
      _ = F (J (J v)) := by rw [J.apply_apply]
      _ = J' (F (J v)) := hF v
  have hneg : -J' (F v) = -F (J v) := by
    calc
      -J' (F v) = J' (-F v) := (map_neg J'.toLinearMap (F v)).symm
      _ = J' (J' (F (J v))) := congrArg J' hrot
      _ = -F (J v) := J'.apply_apply (F (J v))
  exact neg_injective hneg.symm

/-- Precomposition by the source almost complex structure preserves and reflects
complex-linearity. -/
@[simp]
lemma isComplexLinearMap_comp_almostComplexStructure_toLinearMap_iff
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {F : V →ₗ[ℝ] W} :
    IsComplexLinearMap J J' (F.comp J.toLinearMap) ↔ IsComplexLinearMap J J' F :=
  ⟨fun hF => hF.of_comp_almostComplexStructure_toLinearMap,
    fun hF => hF.comp_almostComplexStructure_toLinearMap⟩

end ComplexLinearMap

/-- The ordered pairing `B (F v) (F (J₀ v))` of an alternating bilinear form `B` is unchanged when
both arguments are precomposed by a source almost complex structure `J₀`: rotating the source by
`J₀` sends the pair `(v, J₀ v)` to `(J₀ v, -v)`, and alternation leaves the pairing unchanged.

Only alternation of `B` is used, so the statement lives at the `LinearMap.BilinForm` level; the
`SymplecticForm` corollary is `SymplecticForm.symplecticForm_comp_almostComplexStructure`. -/
lemma bilinForm_comp_almostComplexStructure {U V : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] {B : LinearMap.BilinForm ℝ V} (hB : B.IsAlt)
    (J₀ : AlmostComplexStructure U) (F : U →ₗ[ℝ] V) (v : U) :
    B ((F.comp J₀.toLinearMap) v) ((F.comp J₀.toLinearMap) (J₀ v)) = B (F v) (F (J₀ v)) := by
  have h1 : (F.comp J₀.toLinearMap) v = F (J₀ v) := rfl
  have h2 : (F.comp J₀.toLinearMap) (J₀ v) = -F v :=
    calc
      (F.comp J₀.toLinearMap) (J₀ v) = F (J₀ (J₀ v)) := rfl
      _ = F (-v) := by rw [J₀.apply_apply]
      _ = -F v := by rw [map_neg]
  rw [h1, h2]
  simpa using hB.neg_eq (F (J₀ v)) (F v)

/-- A symplectic form on a real module is an alternating, nondegenerate bilinear form.

This is the pointwise linear-algebra notion. Closedness of a differential form belongs to the
manifold layer and is not bundled here. -/
structure SymplecticForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The underlying real bilinear form. -/
  toBilinForm : LinearMap.BilinForm ℝ V
  /-- Symplectic forms are alternating. -/
  isAlt : toBilinForm.IsAlt
  /-- Symplectic forms are nondegenerate. -/
  nondegenerate : toBilinForm.Nondegenerate

namespace SymplecticForm

variable [AddCommGroup V] [Module ℝ V]

/-- The underlying bilinear form determines a symplectic form: the only data is the form, the
alternating and nondegeneracy conditions being propositions. -/
theorem toBilinForm_injective :
    Function.Injective (toBilinForm : SymplecticForm V → LinearMap.BilinForm ℝ V) := by
  rintro ⟨B, _, _⟩ ⟨B', _, _⟩ h
  subst h
  rfl

instance : CoeFun (SymplecticForm V) fun _ => V → V → ℝ :=
  ⟨fun ω v w => ω.toBilinForm v w⟩

/-- A symplectic form vanishes on the diagonal. -/
@[simp]
lemma self_eq_zero (ω : SymplecticForm V) (v : V) : ω v v = 0 :=
  ω.isAlt.self_eq_zero v

/-- A symplectic form is skew-symmetric in the usual additive form. -/
lemma neg_eq (ω : SymplecticForm V) (v w : V) :
    -ω v w = ω w v :=
  ω.isAlt.neg_eq v w

/-- Bilinear expansion of `ω` on the plane spanned by a pair of vectors: only the mixed term
`ω x y` survives. -/
lemma apply_smul_add_smul (ω : SymplecticForm V) (x y : V) (a b c d : ℝ) :
    ω (a • x + b • y) (c • x + d • y) = (a * d - b * c) * ω x y := by
  have hyx : ω y x = -ω x y := (ω.neg_eq x y).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    self_eq_zero, hyx]
  ring

/-- The ordered area density `ω (F v) (F (J₀ v))` is unchanged when both arguments are
precomposed by a source almost complex structure `J₀`: rotating the source by `J₀` sends the
pair `(v, J₀ v)` to `(J₀ v, -v)`, which has the same symplectic area. This is the
`SymplecticForm` corollary of `bilinForm_comp_almostComplexStructure`. -/
lemma symplecticForm_comp_almostComplexStructure {U : Type*} [AddCommGroup U] [Module ℝ U]
    (ω : SymplecticForm V) (J₀ : AlmostComplexStructure U) (F : U →ₗ[ℝ] V) (v : U) :
    ω ((F.comp J₀.toLinearMap) v) ((F.comp J₀.toLinearMap) (J₀ v)) = ω (F v) (F (J₀ v)) :=
  bilinForm_comp_almostComplexStructure ω.isAlt J₀ F v

/-- A symplectic form is reflexive as an orthogonality relation. -/
lemma isRefl (ω : SymplecticForm V) : ω.toBilinForm.IsRefl :=
  ω.isAlt.isRefl

/-- Nondegeneracy can be tested on the left variable for a symplectic form. -/
lemma separatingLeft (ω : SymplecticForm V) :
    ω.toBilinForm.SeparatingLeft :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ω.isRefl).mp ω.nondegenerate

/-- Nondegeneracy can be tested on the right variable for a symplectic form. -/
lemma separatingRight (ω : SymplecticForm V) :
    ω.toBilinForm.SeparatingRight :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingRight ω.isRefl).mp ω.nondegenerate

/-- Nondegeneracy supplies a **hyperbolic partner**: every nonzero vector `x` admits a vector `y`
with `ω x y = 1`. -/
lemma exists_apply_eq_one (ω : SymplecticForm V) {x : V} (hx : x ≠ 0) : ∃ y : V, ω x y = 1 := by
  obtain ⟨y, hy⟩ : ∃ y : V, ω x y ≠ 0 := by
    by_contra hcon
    exact hx (ω.separatingLeft x fun y => not_not.1 fun hne => hcon ⟨y, hne⟩)
  exact ⟨(ω x y)⁻¹ • y, by simp [inv_mul_cancel₀ hy]⟩

/-- The bilinear form `ω(J ·, J ·)`. -/
@[expose] def pullback (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    LinearMap.BilinForm ℝ V :=
  ω.toBilinForm.comp J.toLinearMap J.toLinearMap

@[simp]
lemma pullback_apply (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    ω.pullback J v w = ω (J v) (J w) := rfl

/-- A symplectic form is `J`-invariant when `ω(Jv, Jw) = ω(v, w)`. -/
@[expose] def Invariant (ω : SymplecticForm V) (J : AlmostComplexStructure V) : Prop :=
  ω.pullback J = ω.toBilinForm

lemma invariant_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    ω.Invariant J ↔ ∀ v w, ω (J v) (J w) = ω v w :=
  LinearMap.ext_iff₂

/-- The bilinear form `g(v,w) = ω(v, Jw)` associated to `ω` and `J`. -/
@[expose] def associatedBilinForm (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    LinearMap.BilinForm ℝ V :=
  LinearMap.BilinForm.compRight ω.toBilinForm J.toLinearMap

@[simp]
lemma associatedBilinForm_apply
    (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v w : V) :
    ω.associatedBilinForm J v w = ω v (J w) := rfl

/-- `ω` tames `J` if `ω(v, Jv)` is positive on every nonzero vector. -/
@[expose] def Tames (ω : SymplecticForm V) (J : AlmostComplexStructure V) : Prop :=
  ∀ v, v ≠ 0 → 0 < ω v (J v)

lemma tames_iff_associated_pos (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    ω.Tames J ↔ (ω.associatedBilinForm J).toQuadraticMap.PosDef :=
  ⟨fun h v hv => by
      simpa [associatedBilinForm, LinearMap.BilinMap.toQuadraticMap_apply] using h v hv,
    fun h v hv => by
      simpa [associatedBilinForm, LinearMap.BilinMap.toQuadraticMap_apply] using h v hv⟩

/-- `ω` is compatible with `J` if it is `J`-invariant and `ω(·, J ·)` is positive definite. -/
structure Compatible (ω : SymplecticForm V) (J : AlmostComplexStructure V) : Prop where
  /-- The form is invariant under applying `J` to both variables. -/
  invariant : ω.Invariant J
  /-- The associated quadratic form `v ↦ ω(v, Jv)` is positive definite. -/
  positive : (ω.associatedBilinForm J).toQuadraticMap.PosDef

/-- Compatibility is equivalently `J`-invariance plus tameness. -/
lemma compatible_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    ω.Compatible J ↔ ω.Invariant J ∧ ω.Tames J :=
  ⟨fun h => ⟨h.invariant, (ω.tames_iff_associated_pos J).mpr h.positive⟩,
    fun h => ⟨h.1, (ω.tames_iff_associated_pos J).mp h.2⟩⟩

/-- Build compatibility from `J`-invariance and the named tameness predicate. -/
lemma Compatible.of_tames {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hinvariant : ω.Invariant J) (htames : ω.Tames J) : ω.Compatible J :=
  (ω.compatible_iff J).mpr ⟨hinvariant, htames⟩

lemma Compatible.tames {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (h : ω.Compatible J) : ω.Tames J :=
  (ω.tames_iff_associated_pos J).mpr h.positive

lemma Compatible.invariant_apply {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (h : ω.Compatible J) (v w : V) : ω (J v) (J w) = ω v w :=
  (ω.invariant_iff J).mp h.invariant v w

/-- For a `J`-invariant form, the associated bilinear form is symmetric pointwise. Only invariance
is needed. -/
lemma Invariant.associatedBilinForm_apply_swap
    {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hinv : ω.Invariant J) (v w : V) : ω v (J w) = ω w (J v) := by
  calc
    ω v (J w) = -ω (J w) v := by rw [ω.neg_eq]
    _ = ω w (J v) := by simpa using (ω.invariant_iff J).mp hinv w (J v)

/-- For a compatible pair, the associated bilinear form is symmetric pointwise. -/
lemma Compatible.associatedBilinForm_apply_swap
    {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (h : ω.Compatible J) (v w : V) : ω v (J w) = ω w (J v) :=
  h.invariant.associatedBilinForm_apply_swap v w

/-- For a `J`-invariant form, the associated bilinear form `ω(·, J ·)` is symmetric. Only
invariance is needed. -/
lemma Invariant.associatedBilinForm_isSymm
    {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hinv : ω.Invariant J) : (ω.associatedBilinForm J).IsSymm :=
  ⟨fun v w => hinv.associatedBilinForm_apply_swap v w⟩

/-- For a compatible pair, the associated bilinear form `ω(·, J ·)` is symmetric. -/
lemma Compatible.associatedBilinForm_isSymm
    {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (h : ω.Compatible J) : (ω.associatedBilinForm J).IsSymm :=
  h.invariant.associatedBilinForm_isSymm

/-- Applying the almost complex structure to both entries preserves the diagonal of the
associated bilinear form. -/
lemma associatedBilinForm_apply_apply_self_eq (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) (v : V) :
    ω.associatedBilinForm J (J v) (J v) = ω.associatedBilinForm J v v := by
  calc
    ω.associatedBilinForm J (J v) (J v) = ω (J v) (-v) := by
      rw [associatedBilinForm_apply, AlmostComplexStructure.apply_apply]
    _ = -ω (J v) v := by
      exact map_neg (ω.toBilinForm (J v)) v
    _ = ω v (J v) := by
      rw [← ω.neg_eq v (J v)]
      simp
    _ = ω.associatedBilinForm J v v := by
      rw [associatedBilinForm_apply]

lemma Compatible.associated_pos {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (h : ω.Compatible J) {v : V} (hv : v ≠ 0) : 0 < ω v (J v) :=
  h.tames v hv

end SymplecticForm

namespace IsComplexLinearMap

variable {U : Type*} [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]
variable {J₀ : AlmostComplexStructure U} {J : AlmostComplexStructure V}
variable {F : U →ₗ[ℝ] V} {ω : SymplecticForm V}

/-- For a complex-linear map from any complex source, the associated-bilinear-form diagonal
of the image of `J₀ v` equals that of the image of `v`. -/
lemma associatedBilinForm_apply_apply_self_eq
    (hF : IsComplexLinearMap J₀ J F) (v : U) :
    ω.associatedBilinForm J (F (J₀ v)) (F (J₀ v)) =
      ω.associatedBilinForm J (F v) (F v) := by
  rw [(isComplexLinearMap_iff_apply J₀ J F).mp hF v]
  exact ω.associatedBilinForm_apply_apply_self_eq J (F v)

/-- For a complex-linear map from any complex source, the associated-bilinear-form diagonal
of an image vector is the symplectic area density of the ordered pair `(F v, F (J₀ v))`. -/
lemma associatedBilinForm_apply_self_eq_symplecticForm
    (hF : IsComplexLinearMap J₀ J F) (v : U) :
    ω.associatedBilinForm J (F v) (F v) = ω (F v) (F (J₀ v)) := by
  rw [SymplecticForm.associatedBilinForm_apply,
    (isComplexLinearMap_iff_apply J₀ J F).mp hF v]

end IsComplexLinearMap

end TauCeti
