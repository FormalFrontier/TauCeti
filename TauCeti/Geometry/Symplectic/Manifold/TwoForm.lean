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
  toContinuousBilinForm :
    ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
  /-- The form vanishes when its two arguments agree. -/
  alternating : ∀ x v, toContinuousBilinForm x v v = 0

namespace SmoothTwoForm

variable {form form' : SmoothTwoForm I M}

/-- A smooth two-form is evaluated as `form x v w`. -/
instance : CoeFun (SmoothTwoForm I M) fun _ =>
    (x : M) → TangentSpace I x → TangentSpace I x → ℝ :=
  ⟨fun form x v w ↦ form.toContinuousBilinForm x v w⟩

/-- The continuous bilinear form underlying `form` at `x`, regarded as an algebraic bilinear
form. -/
def bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) where
  toFun v := (form.toContinuousBilinForm x v).toLinearMap
  map_add' v w := by
    ext u
    simp
  map_smul' c v := by
    ext u
    simp

@[simp]
lemma bilinFormAt_apply (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    form.bilinFormAt x v w = form x v w := (rfl)

/-- The pointwise algebraic bilinear form is alternating. -/
lemma isAlt_bilinFormAt (form : SmoothTwoForm I M) (x : M) :
    (form.bilinFormAt x).IsAlt :=
  fun v ↦ form.alternating x v

/-- A smooth two-form vanishes on the diagonal. -/
@[simp]
lemma self_eq_zero (form : SmoothTwoForm I M) (x : M) (v : TangentSpace I x) :
    form x v v = 0 :=
  form.alternating x v

/-- A smooth two-form is skew-symmetric in the usual additive form. -/
lemma neg_eq (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    -form x v w = form x w v :=
  (form.isAlt_bilinFormAt x).neg_eq v w

/-- The underlying smooth bilinear section determines a smooth two-form. -/
theorem toContinuousBilinForm_injective :
    Function.Injective
      (toContinuousBilinForm : SmoothTwoForm I M →
        ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) ∞
          (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) := by
  rintro ⟨B, _⟩ ⟨C, _⟩ h
  subst h
  rfl

/-- Two smooth two-forms agreeing on every pair of tangent vectors are equal. -/
@[ext]
lemma ext (h : ∀ (x : M) (v w : TangentSpace I x), form x v w = form' x v w) :
    form = form' := by
  apply toContinuousBilinForm_injective
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
  have hform := (form.toContinuousBilinForm.contMDiff.of_le ENat.LEInfty.out).comp hb
  have htotal := ContMDiff.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M ℝ) (b := b) hform hV hW
  intro y
  have hy := htotal y
  rw [← contMDiffWithinAt_univ] at hy ⊢
  simp only [contMDiffWithinAt_totalSpace] at hy
  exact hy.2

end Evaluation

/-- The zero smooth two-form. -/
protected def zero : SmoothTwoForm I M where
  toContinuousBilinForm := 0
  alternating x v := by simp

instance : Zero (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.zero⟩

@[simp]
lemma zero_toContinuousBilinForm :
    (0 : SmoothTwoForm I M).toContinuousBilinForm = 0 := (rfl)

lemma zero_apply (x : M) (v w : TangentSpace I x) :
    (0 : SmoothTwoForm I M) x v w = 0 := (rfl)

/-- The sum of two smooth two-forms. -/
protected def add (form form' : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContinuousBilinForm := form.toContinuousBilinForm + form'.toContinuousBilinForm
  alternating x v := by simp

instance : Add (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.add⟩

@[simp]
lemma add_toContinuousBilinForm (form form' : SmoothTwoForm I M) :
    (form + form').toContinuousBilinForm =
      form.toContinuousBilinForm + form'.toContinuousBilinForm := (rfl)

lemma add_apply (form form' : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (form + form') x v w = form x v w + form' x v w := by
  rfl

/-- The negative of a smooth two-form. -/
protected def neg (form : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContinuousBilinForm := -form.toContinuousBilinForm
  alternating x v := by simp

instance : Neg (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.neg⟩

@[simp]
lemma neg_toContinuousBilinForm (form : SmoothTwoForm I M) :
    (-form).toContinuousBilinForm = -form.toContinuousBilinForm := (rfl)

lemma neg_apply (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (-form) x v w = -form x v w := by
  rfl

/-- The difference of two smooth two-forms. -/
protected def sub (form form' : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContinuousBilinForm := form.toContinuousBilinForm - form'.toContinuousBilinForm
  alternating x v := by simp

instance : Sub (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.sub⟩

@[simp]
lemma sub_toContinuousBilinForm (form form' : SmoothTwoForm I M) :
    (form - form').toContinuousBilinForm =
      form.toContinuousBilinForm - form'.toContinuousBilinForm := (rfl)

lemma sub_apply (form form' : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (form - form') x v w = form x v w - form' x v w := by
  rfl

/-- The real scalar multiple of a smooth two-form. -/
protected def smul (c : ℝ) (form : SmoothTwoForm I M) : SmoothTwoForm I M where
  toContinuousBilinForm := c • form.toContinuousBilinForm
  alternating x v := by simp

instance : SMul ℝ (SmoothTwoForm I M) :=
  ⟨SmoothTwoForm.smul⟩

@[simp]
lemma smul_toContinuousBilinForm (c : ℝ) (form : SmoothTwoForm I M) :
    (c • form).toContinuousBilinForm = c • form.toContinuousBilinForm := (rfl)

lemma smul_apply (c : ℝ) (form : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    (c • form) x v w = c * form x v w := by
  rfl

/-- Smooth two-forms form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (SmoothTwoForm I M) :=
  letI : SMul ℕ (SmoothTwoForm I M) := ⟨fun n form ↦ (n : ℝ) • form⟩
  letI : SMul ℤ (SmoothTwoForm I M) := ⟨fun n form ↦ (n : ℝ) • form⟩
  Function.Injective.addCommGroup toContinuousBilinForm toContinuousBilinForm_injective
    zero_toContinuousBilinForm add_toContinuousBilinForm neg_toContinuousBilinForm
    sub_toContinuousBilinForm
    (fun form n ↦ by
      apply ContMDiffSection.ext
      intro x
      ext v w
      change ((((n : ℝ) • form).toContinuousBilinForm x) v) w = _
      rw [smul_toContinuousBilinForm]
      exact congrArg (fun s ↦ s x v w)
        (Nat.cast_smul_eq_nsmul ℝ n form.toContinuousBilinForm))
    (fun form n ↦ by
      apply ContMDiffSection.ext
      intro x
      ext v w
      change ((((n : ℝ) • form).toContinuousBilinForm x) v) w = _
      rw [smul_toContinuousBilinForm]
      exact congrArg (fun s ↦ s x v w)
        (Int.cast_smul_eq_zsmul ℝ n form.toContinuousBilinForm))

/-- Smooth two-forms form a real vector space under pointwise scalar multiplication. -/
instance : Module ℝ (SmoothTwoForm I M) :=
  Function.Injective.module ℝ
    { toFun := toContinuousBilinForm
      map_zero' := zero_toContinuousBilinForm
      map_add' := add_toContinuousBilinForm }
    toContinuousBilinForm_injective
    smul_toContinuousBilinForm

end SmoothTwoForm

end TauCeti

end
