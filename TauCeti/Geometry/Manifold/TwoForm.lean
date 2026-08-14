/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Smooth differential two-forms on manifolds

This file defines smooth real differential two-forms on a manifold. A `SmoothTwoForm` is a smooth
section of the bundle of continuous bilinear forms on the tangent bundle, with the fiberwise
alternation law. Its value at a point is exposed as Mathlib's algebraic `LinearMap.BilinForm`, so
the existing alternating-form API applies without duplicating it.

This is the differential-form prerequisite for Lane F2.1 of the analytic Heegaard Floer roadmap,
whose next manifold-level target is a symplectic manifold: a smooth two-form which is closed and
fiberwise nondegenerate. Mathlib has exterior derivatives on normed vector spaces, but not on
manifolds, so closedness is deliberately not represented by a placeholder here. The smooth
two-form, closedness, and nondegeneracy are kept as separate layers, matching the roadmap's rule
that analytic hypotheses remain unbundled until the object itself is available.

The file provides the additive and real-scalar API for two-forms and proves that evaluating a
smooth two-form on two smooth vector fields along a smooth map gives a smooth real-valued
function. That evaluation theorem is the immediate input needed to define the energy and area of
manifold-valued pseudoholomorphic curves.

## Main declarations

* `TauCeti.SmoothTwoForm`: a smooth alternating bilinear form on tangent fibers.
* `TauCeti.SmoothTwoForm.bilinFormAt`: the algebraic alternating bilinear form at a point.
* `TauCeti.SmoothTwoForm.contMDiff_apply`: smooth evaluation on two smooth vector fields.
* `TauCeti.SmoothTwoForm.const`: the constant smooth two-form on a model vector space.

The definition follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.2.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth differential two-form on a manifold is a smooth section of the bundle of continuous
bilinear forms on the tangent bundle which vanishes when both arguments agree. -/
structure SmoothTwoForm (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The underlying smooth section of continuous bilinear forms on tangent fibers. -/
  toContMDiffSection :
    ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
  /-- The form vanishes when its two arguments agree. -/
  isAlt : ∀ x v, toContMDiffSection x v v = 0

namespace SmoothTwoForm

attribute [simp] isAlt

variable {form form' : SmoothTwoForm I M}

/-- A smooth two-form is evaluated as `form x v w`. -/
instance : CoeFun (SmoothTwoForm I M) fun _ =>
    (x : M) → TangentSpace I x → TangentSpace I x → ℝ :=
  ⟨fun form x v w ↦ form.toContMDiffSection x v w⟩

/-- The continuous bilinear form underlying `form` at `x`, regarded as an algebraic bilinear
form. -/
def bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (form.toContMDiffSection x).toBilinForm

@[simp]
lemma bilinFormAt_apply (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    form.bilinFormAt x v w = form x v w := (rfl)

/-- The pointwise algebraic bilinear form is alternating. -/
lemma isAlt_bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    (form.bilinFormAt x).IsAlt :=
  fun v ↦ form.isAlt x v

/-- The underlying smooth bilinear section determines a smooth two-form. -/
theorem toContMDiffSection_injective :
    Function.Injective
      (toContMDiffSection : SmoothTwoForm I M →
        ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) ∞
          (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) := by
  rintro ⟨B, _⟩ ⟨C, _⟩ h
  subst h
  rfl

/-- Two smooth two-forms agreeing on every pair of tangent vectors are equal. -/
@[ext]
lemma ext (h : ∀ (x : M) (v w : TangentSpace I x), form x v w = form' x v w) :
    form = form' := by
  apply toContMDiffSection_injective
  apply ContMDiffSection.ext
  intro x
  ext v w
  exact h x v w

section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth two-form on two smooth tangent fields along a smooth map gives a smooth
real-valued function. -/
lemma contMDiff_apply {n : ℕ∞ω} [ENat.LEInfty n] (form : SmoothTwoForm I M)
    {b : N → M}
    {V W : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (V y)))
    (hW : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (W y))) :
    ContMDiff I' 𝓘(ℝ) n (fun y ↦ form (b y) (V y) (W y)) := by
  have hb : ContMDiff I' I n b := fun y ↦ by
    have hy := hV y
    rw [← contMDiffWithinAt_univ] at hy ⊢
    exact (contMDiffWithinAt_totalSpace.mp hy).1
  have hform := (form.toContMDiffSection.contMDiff.of_le ENat.LEInfty.out).comp hb
  have htotal := ContMDiff.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M ℝ) (b := b) hform hV hW
  intro y
  have hy := htotal y
  rw [← contMDiffWithinAt_univ] at hy ⊢
  simp only [contMDiffWithinAt_totalSpace] at hy
  exact hy.2

end Evaluation

/-- A continuous alternating bilinear form defines a constant smooth two-form on its model vector
space. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    SmoothTwoForm (modelWithCornersSelf ℝ V) V where
  toContMDiffSection :=
    ⟨fun _ ↦ B, by
      intro x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      -- The base and fiber components of the constant section are the projections of an explicit
      -- pair, so `dsimp only` reduces the goal to the coordinate expression rewritten below.
      dsimp only
      have hcoord : (fun y : V =>
          ContinuousLinearMap.inCoordinates V (TangentSpace 𝓘(ℝ, V)) (V →L[ℝ] ℝ)
            (fun b : V => TangentSpace 𝓘(ℝ, V) b →L[ℝ] ℝ) x y x y B) = fun _ => B := by
        funext y
        ext v w
        simp only [ContinuousLinearMap.inCoordinates, TangentBundle.symmL_model_space,
          ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
        have htan : y ∈ (trivializationAt V (TangentSpace 𝓘(ℝ, V)) x).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
          exact Set.mem_univ y
        have htriv : y ∈ (trivializationAt ℝ (Bundle.Trivial V ℝ) x).baseSet := by
          simp
        have hhom : y ∈ (trivializationAt (V →L[ℝ] ℝ)
            (fun b : V => TangentSpace 𝓘(ℝ, V) b →L[ℝ] ℝ) x).baseSet := by
          rw [hom_trivializationAt_baseSet]
          exact ⟨htan, htriv⟩
        rw [Trivialization.linearMapAt_apply, ite_eq_left hhom, hom_trivializationAt_apply]
        simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
          Trivial.continuousLinearMapAt_trivialization, TangentBundle.symmL_model_space,
          ContinuousLinearMap.id_comp]
        rfl
      rw [hcoord]
      exact contMDiffAt_const⟩
  isAlt _ v := hB v

/-- The smooth bilinear section of a constant two-form has its defining value in every fiber. -/
@[simp]
lemma const_toContMDiffSection_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x : V) :
    (const B hB).toContMDiffSection x = B :=
  (rfl)

/-- The pointwise bilinear form of a constant smooth two-form is its defining bilinear form with
continuity forgotten. -/
@[simp]
lemma const_bilinFormAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) (x : V) :
    (const B hB).bilinFormAt x = B.toBilinForm := by
  ext v w
  rfl

/-- The zero smooth two-form. -/
protected def zero : SmoothTwoForm I M where
  toContMDiffSection := 0
  isAlt x v := by simp

instance : Zero (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.zero⟩

@[simp]
lemma zero_toContMDiffSection :
    (0 : SmoothTwoForm I M).toContMDiffSection = 0 := (rfl)

lemma zero_apply (x : M) (v w : TangentSpace I x) :
    (0 : SmoothTwoForm I M) x v w = 0 := (rfl)

/-- The sum of two smooth two-forms. -/
protected def add (form form' : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContMDiffSection := form.toContMDiffSection + form'.toContMDiffSection
  isAlt x v := by simp

instance : Add (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.add⟩

@[simp]
lemma add_toContMDiffSection (form form' : SmoothTwoForm I M) :
    (form + form').toContMDiffSection =
      form.toContMDiffSection + form'.toContMDiffSection := (rfl)

lemma add_apply (form form' : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (form + form') x v w = form x v w + form' x v w := by
  rfl

/-- The negative of a smooth two-form. -/
protected def neg (form : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContMDiffSection := -form.toContMDiffSection
  isAlt x v := by simp

instance : Neg (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.neg⟩

@[simp]
lemma neg_toContMDiffSection (form : SmoothTwoForm I M) :
    (-form).toContMDiffSection = -form.toContMDiffSection := (rfl)

lemma neg_apply (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (-form) x v w = -form x v w := by
  rfl

/-- The difference of two smooth two-forms. -/
protected def sub (form form' : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContMDiffSection := form.toContMDiffSection - form'.toContMDiffSection
  isAlt x v := by simp

instance : Sub (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.sub⟩

@[simp]
lemma sub_toContMDiffSection (form form' : SmoothTwoForm I M) :
    (form - form').toContMDiffSection =
      form.toContMDiffSection - form'.toContMDiffSection := (rfl)

lemma sub_apply (form form' : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (form - form') x v w = form x v w - form' x v w := by
  rfl

/-- The real scalar multiple of a smooth two-form. -/
protected def smul (c : ℝ) (form : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContMDiffSection := c • form.toContMDiffSection
  isAlt x v := by simp

instance : SMul ℝ (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.smul⟩

@[simp]
lemma smul_toContMDiffSection (c : ℝ) (form : SmoothTwoForm I M) :
    (c • form).toContMDiffSection = c • form.toContMDiffSection := (rfl)

lemma smul_apply (c : ℝ) (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (c • form) x v w = c * form x v w := by
  rfl

/-- Smooth two-forms form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (SmoothTwoForm I M) :=
  -- The `ℕ`- and `ℤ`-actions are fixed to be the real action along the cast, so their
  -- compatibility obligations below are the real-scalar lemma `smul_toContMDiffSection`
  -- composed with `Nat.cast_smul_eq_nsmul` / `Int.cast_smul_eq_zsmul` on sections.
  letI : SMul ℕ (SmoothTwoForm I M) := ⟨fun n form ↦ (n : ℝ) • form⟩
  letI : SMul ℤ (SmoothTwoForm I M) := ⟨fun n form ↦ (n : ℝ) • form⟩
  Function.Injective.addCommGroup toContMDiffSection toContMDiffSection_injective
    zero_toContMDiffSection add_toContMDiffSection neg_toContMDiffSection
    sub_toContMDiffSection
    (fun form n ↦
      (smul_toContMDiffSection (n : ℝ) form).trans
        (Nat.cast_smul_eq_nsmul ℝ n form.toContMDiffSection))
    (fun form n ↦
      (smul_toContMDiffSection (n : ℝ) form).trans
        (Int.cast_smul_eq_zsmul ℝ n form.toContMDiffSection))

/-- Smooth two-forms form a real vector space under pointwise scalar multiplication. -/
instance : Module ℝ (SmoothTwoForm I M) :=
  Function.Injective.module ℝ
    { toFun := toContMDiffSection
      map_zero' := zero_toContMDiffSection
      map_add' := add_toContMDiffSection }
    toContMDiffSection_injective
    smul_toContMDiffSection

end SmoothTwoForm

end TauCeti

end
