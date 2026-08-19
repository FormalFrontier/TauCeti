/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# Smooth periodic integration by parts

This file begins the periodic Sobolev substrate on the normalized flat torus. It defines a
classical derivative in any selected coordinate of `UnitAddTorus d`, for an arbitrary finite
index type `d`, and proves smooth scalar integration by parts against Haar volume:

`∫ x, f x * ∂ᵢ g x = -∫ x, ∂ᵢ f x * g x`.

The public torus interface is independent of a choice `d = Fin n`. Internally, a selected
coordinate is split from its complement by `Equiv.funSplitAt`; the accompanying
measure-preservation theorem is the Fubini bookkeeping needed here and in later periodic
estimates. The coordinate derivative is the quotient lift of the derivative of the one-periodic
real slice; `TauCeti.Function.Periodic.deriv` verifies that it descends to the circle. In
particular, the half-open representative used to prove the integral identity does not occur in
the derivative's definition or the main theorem's statement.

This is the smooth endpoint of the construction. The companion `Periodic.WeakDeriv` module uses
the integration-by-parts identity as the defining relation for periodic weak derivatives.

## Main declarations

* `UnitAddTorus.coordinateSplit`: split off any coordinate of a finite unit torus.
* `UnitAddTorus.coordinateSplit_volumePreserving`: the split preserves Haar volume.
* `UnitAddTorus.coordinateDerivative`: the classical derivative in one torus coordinate.
* `UnitAddTorus.coordinateDerivative_mul`: the intrinsic coordinate Leibniz rule.
* `UnitAddTorus.integral_mul_coordinateDerivative_eq_neg`: smooth periodic integration
  by parts on `UnitAddTorus d`.
-/

public section

noncomputable section

open _root_.Function MeasureTheory Set
open scoped Interval

namespace AddCircle

/-- The integral of a derivative over one period vanishes. -/
theorem intervalIntegral_deriv_eq_zero_of_periodic
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContDiff ℝ 1 f)
    (hper : Periodic f T) :
    ∫ x in (0 : ℝ)..T, deriv f x = 0 := by
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hf.contDiffOn hT]
  have hend : f T = f 0 := by simpa using hper 0
  rw [hend, sub_self]

/-- Integration by parts over one period, with the endpoint term cancelled by periodicity. -/
theorem intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    ∫ x in (0 : ℝ)..T, f x * deriv g x =
      -∫ x in (0 : ℝ)..T, deriv f x * g x := by
  have hfac : AbsolutelyContinuousOnInterval f 0 T :=
    hf.contDiffOn.absolutelyContinuousOnInterval
  have hgac : AbsolutelyContinuousOnInterval g 0 T :=
    hg.contDiffOn.absolutelyContinuousOnInterval
  rw [hfac.integral_mul_deriv_eq_deriv_mul hgac]
  have hfend : f T = f 0 := by simpa using hfper 0
  have hgend : g T = g 0 := by simpa using hgper 0
  rw [hfend, hgend, sub_self, zero_sub]

/-- Smooth integration by parts on a measured circle of arbitrary positive period. -/
theorem integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} [Fact (0 < T)] {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    (∫ x : _root_.AddCircle T,
        _root_.AddCircle.liftIoc T 0 (fun r => f r * deriv g r) x) =
      -(∫ x : _root_.AddCircle T,
        _root_.AddCircle.liftIoc T 0 (fun r => deriv f r * g r) x) := by
  rw [_root_.AddCircle.integral_liftIoc_eq_intervalIntegral,
    _root_.AddCircle.integral_liftIoc_eq_intervalIntegral]
  simpa using intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic hf hg hfper hgper

end AddCircle

namespace UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The unit torus on all coordinates other than `i`. -/
abbrev CoordinateComplement (d : Type*) (i : d) :=
  _root_.UnitAddTorus {j : d // j ≠ i}

/-- Split a selected coordinate from an arbitrary finite unit torus. -/
def coordinateSplit (i : d) :
    _root_.UnitAddTorus d ≃ᵐ _root_.UnitAddCircle × CoordinateComplement d i where
  toEquiv := Equiv.funSplitAt i _root_.UnitAddCircle
  measurable_toFun := (measurable_pi_apply i).prodMk <|
    measurable_pi_iff.2 fun j => by
      change Measurable (fun x : _root_.UnitAddTorus d => x j)
      fun_prop
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro j
    simp only [Equiv.funSplitAt_symm_apply]
    split_ifs <;> fun_prop

omit [Fintype d] in
@[simp]
theorem coordinateSplit_apply (i : d) (x : _root_.UnitAddTorus d) :
    coordinateSplit i x = (x i, fun j : {j : d // j ≠ i} => x j) := by
  change Equiv.funSplitAt i _root_.UnitAddCircle x = _
  rw [Equiv.funSplitAt_apply]

omit [Fintype d] in
@[simp]
theorem coordinateSplit_symm_apply_same (i : d)
    (z : _root_.UnitAddCircle × CoordinateComplement d i) :
    (coordinateSplit i).symm z i = z.1 := by
  rcases z with ⟨a, y⟩
  change (Equiv.funSplitAt i _root_.UnitAddCircle).symm (a, y) i = a
  rw [Equiv.funSplitAt_symm_apply]
  simp

omit [Fintype d] in
@[simp]
theorem coordinateSplit_symm_apply_ne (i : d)
    (z : _root_.UnitAddCircle × CoordinateComplement d i) (j : {j : d // j ≠ i}) :
    (coordinateSplit i).symm z j = z.2 j := by
  rcases z with ⟨a, y⟩
  change (Equiv.funSplitAt i _root_.UnitAddCircle).symm (a, y) j = y j
  rw [Equiv.funSplitAt_symm_apply]
  simp [j.property]

/-- Splitting off a coordinate preserves Haar volume on a finite unit torus. -/
theorem coordinateSplit_volumePreserving (i : d) :
    MeasurePreserving (coordinateSplit i) := by
  set e := (coordinateSplit i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  have hpre : e ⁻¹' (univ.pi s) =
      s i ×ˢ univ.pi (fun j : {j : d // j ≠ i} => s j) := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod, e]
    constructor
    · intro h
      exact ⟨by simpa using h i, fun j => by simpa [j.property] using h j⟩
    · rintro ⟨hi, hrest⟩ j
      by_cases hj : j = i
      · simpa [hj] using hi
      · rw [show (coordinateSplit i).symm z j = z.2 ⟨j, hj⟩ by
          exact coordinateSplit_symm_apply_ne i z ⟨j, hj⟩]
        exact hrest ⟨j, hj⟩
  rw [e.map_apply, hpre, Measure.volume_eq_prod, Measure.prod_prod]
  rw [volume_pi_pi]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun j => volume (s j)) i).symm

/-- Restrict a scalar field on a finite unit torus to a selected coordinate circle. -/
def coordinateSlice (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (y : CoordinateComplement d i) (a : _root_.UnitAddCircle) : ℝ :=
  f ((coordinateSplit i).symm (a, y))

/-- Lift a torus coordinate slice to its one-periodic real parametrization. -/
def coordinateSliceLift (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (y : CoordinateComplement d i) (r : ℝ) : ℝ :=
  coordinateSlice f i y (r : _root_.UnitAddCircle)

omit [Fintype d] in
theorem coordinateSliceLift_periodic (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (y : CoordinateComplement d i) : Periodic (coordinateSliceLift f i y) 1 := by
  intro r
  apply congrArg f
  apply congrArg (coordinateSplit i).symm
  simp

/-- A scalar field is `C¹` along the selected coordinate if every real lift of a coordinate
slice is `C¹`. -/
def ContDiffAlongCoordinate (f : _root_.UnitAddTorus d → ℝ) (i : d) : Prop :=
  ∀ y : CoordinateComplement d i, ContDiff ℝ 1 (coordinateSliceLift f i y)

omit [Fintype d] in
/-- Establish coordinatewise `C¹` regularity from the explicit real lifts through
`coordinateSplit`. -/
theorem contDiffAlongCoordinate_of_coordinateSplit
    (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (h : ∀ y : CoordinateComplement d i,
      ContDiff ℝ 1 (fun r : ℝ ↦
        f ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y)))) :
    ContDiffAlongCoordinate f i := by
  intro y
  exact h y

omit [Fintype d] in
/-- Constant scalar fields are continuously differentiable along every torus coordinate. -/
theorem contDiffAlongCoordinate_const (c : ℝ) (i : d) :
    ContDiffAlongCoordinate (fun _ : _root_.UnitAddTorus d ↦ c) i := by
  intro y
  exact contDiff_const

omit [Fintype d] in
/-- Coordinatewise continuous differentiability is preserved by pointwise addition. -/
theorem ContDiffAlongCoordinate.add {f g : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i) :
    ContDiffAlongCoordinate (fun x ↦ f x + g x) i := by
  intro y
  exact (hf y).add (hg y)

omit [Fintype d] in
/-- Coordinatewise continuous differentiability is preserved by pointwise negation. -/
theorem ContDiffAlongCoordinate.neg {f : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : ContDiffAlongCoordinate f i) :
    ContDiffAlongCoordinate (fun x ↦ -f x) i := by
  intro y
  exact (hf y).neg

omit [Fintype d] in
/-- Coordinatewise continuous differentiability is preserved by pointwise subtraction. -/
theorem ContDiffAlongCoordinate.sub {f g : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i) :
    ContDiffAlongCoordinate (fun x ↦ f x - g x) i := by
  intro y
  exact (hf y).sub (hg y)

omit [Fintype d] in
/-- Coordinatewise continuous differentiability is preserved by real scalar multiplication. -/
theorem ContDiffAlongCoordinate.const_smul {f : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : ContDiffAlongCoordinate f i) (c : ℝ) :
    ContDiffAlongCoordinate (fun x ↦ c * f x) i := by
  intro y
  change ContDiff ℝ 1 (fun r ↦ c * coordinateSliceLift f i y r)
  simpa only [smul_eq_mul] using (hf y).const_smul c

omit [Fintype d] in
/-- A finite sum of coordinatewise `C¹` scalar fields is coordinatewise `C¹`. -/
theorem ContDiffAlongCoordinate.finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ∀ a ∈ s, ContDiffAlongCoordinate (f a) i) :
    ContDiffAlongCoordinate (fun x ↦ ∑ a ∈ s, f a x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contDiffAlongCoordinate_const (d := d) 0 i
  | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha] using
        (hf a (Finset.mem_insert_self a s)).add
          (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

omit [Fintype d] in
/-- Coordinatewise continuous differentiability is preserved by pointwise multiplication. -/
theorem ContDiffAlongCoordinate.mul {f g : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i) :
    ContDiffAlongCoordinate (fun x ↦ f x * g x) i := by
  intro y
  exact (hf y).mul (hg y)

/-- A periodic lift agrees with evaluation through the half-open fundamental domain. -/
private theorem periodicLift_eq_liftIoc {f : ℝ → ℝ} (hf : Periodic f 1)
    (a : _root_.UnitAddCircle) :
    hf.lift a = _root_.AddCircle.liftIoc 1 0 f a := by
  let r := _root_.AddCircle.equivIoc 1 0 a
  have hr : (r : _root_.UnitAddCircle) = a := _root_.AddCircle.coe_equivIoc
  rw [← hr, Periodic.lift_coe, _root_.AddCircle.liftIoc_coe_apply r.property]

/-- The derivative of a scalar field in a selected unit-torus coordinate. -/
def coordinateDerivative (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (x : _root_.UnitAddTorus d) : ℝ :=
  let z := coordinateSplit i x
  (TauCeti.Function.Periodic.deriv (coordinateSliceLift_periodic f i z.2)).lift z.1

omit [Fintype d] in
/-- At a real representative of the selected circle coordinate, the intrinsic coordinate
derivative is the ordinary derivative of the lifted coordinate slice. -/
theorem coordinateDerivative_coordinateSplit_symm_coe
    (f : _root_.UnitAddTorus d → ℝ) (i : d) (y : CoordinateComplement d i) (r : ℝ) :
    coordinateDerivative f i ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y)) =
      deriv (coordinateSliceLift f i y) r := by
  unfold coordinateDerivative
  simp only [MeasurableEquiv.apply_symm_apply, Function.Periodic.lift_coe]

omit [Fintype d] in
/-- Identify an intrinsic coordinate derivative from ordinary derivatives of all explicit lifted
coordinate slices. -/
theorem coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
    (f f' : _root_.UnitAddTorus d → ℝ) (i : d)
    (h : ∀ (y : CoordinateComplement d i) (r : ℝ),
      HasDerivAt
        (fun s : ℝ ↦ f ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
        (f' ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))) r) :
    coordinateDerivative f i = f' := by
  funext x
  rw [← (coordinateSplit i).symm_apply_apply x]
  generalize coordinateSplit i x = z
  rcases z with ⟨a, y⟩
  induction a using QuotientAddGroup.induction_on with
  | H r =>
      rw [coordinateDerivative_coordinateSplit_symm_coe]
      exact (h y r).deriv

omit [Fintype d] in
@[simp]
theorem coordinateDerivative_const (c : ℝ) (i : d) (x : _root_.UnitAddTorus d) :
    coordinateDerivative (fun _ => c) i x = 0 := by
  unfold coordinateDerivative
  have hfun :
      coordinateSliceLift (fun _ : _root_.UnitAddTorus d => c) i ((coordinateSplit i x).2) =
        fun _ : ℝ => c := by
    rfl
  change (TauCeti.Function.Periodic.deriv
      (coordinateSliceLift_periodic (fun _ : _root_.UnitAddTorus d => c) i
        ((coordinateSplit i x).2))).lift ((coordinateSplit i x).1) = 0
  rw [periodicLift_eq_liftIoc]
  rw [hfun, deriv_const']
  rfl

omit [Fintype d] in
/-- Linearity of the intrinsic coordinate derivative under pointwise addition. -/
theorem coordinateDerivative_add (f g : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i) :
    coordinateDerivative (fun z ↦ f z + g z) i =
      fun x ↦ coordinateDerivative f i x + coordinateDerivative g i x := by
  apply coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
  intro y r
  have hf' : HasDerivAt
      (fun s : ℝ ↦ f ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative f i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hf y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hg' : HasDerivAt
      (fun s : ℝ ↦ g ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative g i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hg y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  exact hf'.add hg'

omit [Fintype d] in
/-- Linearity of the intrinsic coordinate derivative under pointwise negation. -/
theorem coordinateDerivative_neg (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) :
    coordinateDerivative (fun z ↦ -f z) i = fun x ↦ -coordinateDerivative f i x := by
  apply coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
  intro y r
  have hf' : HasDerivAt
      (fun s : ℝ ↦ f ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative f i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hf y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  exact hf'.neg

omit [Fintype d] in
/-- Linearity of the intrinsic coordinate derivative under pointwise subtraction. -/
theorem coordinateDerivative_sub (f g : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i) :
    coordinateDerivative (fun z ↦ f z - g z) i =
      fun x ↦ coordinateDerivative f i x - coordinateDerivative g i x := by
  apply coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
  intro y r
  have hf' : HasDerivAt
      (fun s : ℝ ↦ f ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative f i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hf y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hg' : HasDerivAt
      (fun s : ℝ ↦ g ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative g i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hg y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  exact hf'.sub hg'

omit [Fintype d] in
/-- Linearity of the intrinsic coordinate derivative under real scalar multiplication. -/
theorem coordinateDerivative_const_smul (f : _root_.UnitAddTorus d → ℝ) (c : ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) :
    coordinateDerivative (fun z ↦ c * f z) i = fun x ↦ c * coordinateDerivative f i x := by
  apply coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
  intro y r
  have hf' : HasDerivAt
      (fun s : ℝ ↦ f ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (coordinateDerivative f i ((coordinateSplit i).symm
        ((r : _root_.UnitAddCircle), y))) r := by
    rw [coordinateDerivative_coordinateSplit_symm_coe]
    exact ((hf y).differentiable one_ne_zero).differentiableAt.hasDerivAt
  exact hf'.const_mul c

omit [Fintype d] in
/-- The intrinsic coordinate derivative commutes with finite sums of coordinatewise `C¹`
scalar fields. -/
theorem coordinateDerivative_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ∀ a ∈ s, ContDiffAlongCoordinate (f a) i) :
    coordinateDerivative (fun x ↦ ∑ a ∈ s, f a x) i =
      fun x ↦ ∑ a ∈ s, coordinateDerivative (f a) i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext x
      simp only [Finset.sum_empty]
      exact coordinateDerivative_const 0 i x
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [coordinateDerivative_add (f a) (fun x ↦ ∑ b ∈ s, f b x) i
        (hf a (Finset.mem_insert_self a s))
        ((ContDiffAlongCoordinate.finsetSum s f i) fun b hb ↦
          hf b (Finset.mem_insert_of_mem hb)),
        ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)]

omit [Fintype d] in
/-- Leibniz rule for the intrinsic classical coordinate derivative on a finite unit torus. -/
theorem coordinateDerivative_mul (f g : _root_.UnitAddTorus d → ℝ) (i : d)
    (x : _root_.UnitAddTorus d) (hf : ContDiffAlongCoordinate f i)
    (hg : ContDiffAlongCoordinate g i) :
    coordinateDerivative (fun z ↦ f z * g z) i x =
      coordinateDerivative f i x * g x + f x * coordinateDerivative g i x := by
  unfold coordinateDerivative
  let z := coordinateSplit i x
  change
    (TauCeti.Function.Periodic.deriv
      (coordinateSliceLift_periodic (fun y ↦ f y * g y) i z.2)).lift z.1 =
        (TauCeti.Function.Periodic.deriv
          (coordinateSliceLift_periodic f i z.2)).lift z.1 * g x +
        f x * (TauCeti.Function.Periodic.deriv
          (coordinateSliceLift_periodic g i z.2)).lift z.1
  rw [periodicLift_eq_liftIoc, periodicLift_eq_liftIoc, periodicLift_eq_liftIoc]
  have hslice : coordinateSliceLift (fun y ↦ f y * g y) i z.2 =
      fun r ↦ coordinateSliceLift f i z.2 r * coordinateSliceLift g i z.2 r := rfl
  rw [hslice]
  have hderiv : deriv (fun r ↦
      coordinateSliceLift f i z.2 r * coordinateSliceLift g i z.2 r) =
      fun r ↦ deriv (coordinateSliceLift f i z.2) r * coordinateSliceLift g i z.2 r +
        coordinateSliceLift f i z.2 r * deriv (coordinateSliceLift g i z.2) r := by
    funext r
    exact ((((hf z.2).differentiable one_ne_zero).differentiableAt.hasDerivAt).mul
      (((hg z.2).differentiable one_ne_zero).differentiableAt.hasDerivAt)).deriv
  rw [hderiv]
  change
    _root_.AddCircle.liftIoc 1 0
      (fun r ↦ deriv (coordinateSliceLift f i z.2) r * coordinateSliceLift g i z.2 r +
        coordinateSliceLift f i z.2 r * deriv (coordinateSliceLift g i z.2) r) z.1 = _
  simp only [_root_.AddCircle.liftIoc]
  simp only [Function.comp_apply, domRestrict_apply, coordinateSliceLift,
    coordinateSlice, _root_.AddCircle.coe_equivIoc]
  have hz : (coordinateSplit i).symm z = x := by
    exact (coordinateSplit i).symm_apply_apply x
  rw [hz]

private def coordinateSliceDerivative (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (y : CoordinateComplement d i) (a : _root_.UnitAddCircle) : ℝ :=
  (TauCeti.Function.Periodic.deriv (coordinateSliceLift_periodic f i y)).lift a

omit [Fintype d] in
private theorem liftIoc_coordinateSliceLift (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (y : CoordinateComplement d i) (a : _root_.UnitAddCircle) :
    _root_.AddCircle.liftIoc 1 0 (coordinateSliceLift f i y) a =
      coordinateSlice f i y a := by
  change f ((coordinateSplit i).symm
      (((_root_.AddCircle.equivIoc 1 0 a).1 : _root_.UnitAddCircle), y)) =
    f ((coordinateSplit i).symm (a, y))
  rw [_root_.AddCircle.coe_equivIoc]

private theorem liftIoc_mul (f g : ℝ → ℝ) (a : _root_.UnitAddCircle) :
    _root_.AddCircle.liftIoc 1 0 (fun r => f r * g r) a =
      _root_.AddCircle.liftIoc 1 0 f a * _root_.AddCircle.liftIoc 1 0 g a := by
  rfl

omit [Fintype d] in
private theorem coordinateSlice_integration_by_parts
    (f g : _root_.UnitAddTorus d → ℝ) (i : d) (y : CoordinateComplement d i)
    (hf : ContDiff ℝ 1 (coordinateSliceLift f i y))
    (hg : ContDiff ℝ 1 (coordinateSliceLift g i y)) :
    (∫ a : _root_.UnitAddCircle,
        coordinateSlice f i y a * coordinateSliceDerivative g i y a) =
      -(∫ a : _root_.UnitAddCircle,
        coordinateSliceDerivative f i y a * coordinateSlice g i y a) := by
  have h := AddCircle.integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    hf hg (coordinateSliceLift_periodic f i y) (coordinateSliceLift_periodic g i y)
  simpa only [liftIoc_mul, liftIoc_coordinateSliceLift, coordinateSliceDerivative,
    periodicLift_eq_liftIoc] using h

omit [Fintype d] in
private theorem coordinateDerivative_coordinateSplit_symm (f : _root_.UnitAddTorus d → ℝ)
    (i : d) (z : _root_.UnitAddCircle × CoordinateComplement d i) :
    coordinateDerivative f i ((coordinateSplit i).symm z) =
      coordinateSliceDerivative f i z.2 z.1 := by
  simp [coordinateDerivative, coordinateSliceDerivative]

/-- Smooth scalar integration by parts in any selected coordinate of a normalized finite unit
torus. The hypotheses only ask for `C¹` regularity along that coordinate and integrability of the
two products that occur in the conclusion. -/
theorem integral_mul_coordinateDerivative_eq_neg
    (f g : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i) (hg : ContDiffAlongCoordinate g i)
    (hfg : Integrable (fun x => f x * coordinateDerivative g i x))
    (hgf : Integrable (fun x => coordinateDerivative f i x * g x)) :
    (∫ x, f x * coordinateDerivative g i x) =
      -(∫ x, coordinateDerivative f i x * g x) := by
  let e := coordinateSplit i
  have he : MeasurePreserving e := coordinateSplit_volumePreserving i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hfg' : Integrable ((fun x => f x * coordinateDerivative g i x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hfg
  have hgf' : Integrable ((fun x => coordinateDerivative f i x * g x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hgf
  calc
    (∫ x, f x * coordinateDerivative g i x) =
        ∫ z : _root_.UnitAddCircle × CoordinateComplement d i,
          ((fun x => f x * coordinateDerivative g i x) ∘ e.symm) z := by
      symm
      exact hesymm.integral_comp' (fun x => f x * coordinateDerivative g i x)
    _ = ∫ y : CoordinateComplement d i,
        ∫ a : _root_.UnitAddCircle,
          coordinateSlice f i y a * coordinateSliceDerivative g i y a := by
      rw [Measure.volume_eq_prod, integral_prod_symm _ hfg']
      simp [e, coordinateSlice, coordinateDerivative_coordinateSplit_symm]
    _ = -(∫ y : CoordinateComplement d i,
        ∫ a : _root_.UnitAddCircle,
          coordinateSliceDerivative f i y a * coordinateSlice g i y a) := by
      simp_rw [coordinateSlice_integration_by_parts f g i _ (hf _) (hg _)]
      exact integral_neg _
    _ = -(∫ z : _root_.UnitAddCircle × CoordinateComplement d i,
        ((fun x => coordinateDerivative f i x * g x) ∘ e.symm) z) := by
      rw [Measure.volume_eq_prod, integral_prod_symm _ hgf']
      simp [e, coordinateSlice, coordinateDerivative_coordinateSplit_symm]
    _ = -(∫ x, coordinateDerivative f i x * g x) := by
      exact congrArg Neg.neg
        (hesymm.integral_comp' (fun x => coordinateDerivative f i x * g x))

section Normalization

/-- The sine lift of the first nonzero unit-circle Fourier frequency. -/
def firstSineLift (r : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * r)

/-- The cosine lift of the first nonzero unit-circle Fourier frequency. -/
def firstCosineLift (r : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * r)

theorem firstSineLift_periodic : Periodic firstSineLift 1 := by
  intro r
  change Real.sin (2 * Real.pi * (r + 1)) = Real.sin (2 * Real.pi * r)
  simpa only [mul_add, mul_one] using Real.sin_periodic (2 * Real.pi * r)

theorem firstCosineLift_periodic : Periodic firstCosineLift 1 := by
  intro r
  change Real.cos (2 * Real.pi * (r + 1)) = Real.cos (2 * Real.pi * r)
  simpa only [mul_add, mul_one] using Real.cos_periodic (2 * Real.pi * r)

/-- The unit-period normalization contributes `2π` to the first sine-mode derivative. -/
theorem deriv_firstSineLift (r : ℝ) :
    deriv firstSineLift r = 2 * Real.pi * firstCosineLift r := by
  have hinner : HasDerivAt (fun s : ℝ => (2 * Real.pi) * s) (2 * Real.pi) r :=
    hasDerivAt_const_mul (2 * Real.pi)
  have h := ((Real.hasDerivAt_sin (2 * Real.pi * r)).comp r hinner).deriv
  change deriv (Real.sin ∘ fun s : ℝ => (2 * Real.pi) * s) r =
    2 * Real.pi * Real.cos (2 * Real.pi * r)
  rw [h]
  ring

/-- The first cosine mode pins both the `2π` normalization and the derivative sign. -/
theorem deriv_firstCosineLift (r : ℝ) :
    deriv firstCosineLift r = -(2 * Real.pi * firstSineLift r) := by
  have hinner : HasDerivAt (fun s : ℝ => (2 * Real.pi) * s) (2 * Real.pi) r :=
    hasDerivAt_const_mul (2 * Real.pi)
  have h := ((Real.hasDerivAt_cos (2 * Real.pi * r)).comp r hinner).deriv
  change deriv (Real.cos ∘ fun s : ℝ => (2 * Real.pi) * s) r =
    -(2 * Real.pi * Real.sin (2 * Real.pi * r))
  rw [h]
  ring

end Normalization

end UnitAddTorus
