/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The cut norm of a symmetric kernel

This file defines the cut norm of a bounded symmetric kernel on a finite measure space by

`‖K‖□ = sup |∫_(S × T) K|`,

where the supremum ranges over measurable sets `S` and `T`.  It develops the interface needed by
the cut-distance and counting-lemma layers: rectangle integrals, the bound of every rectangle by
the cut norm, the seminorm laws, and the comparison with the `L¹` norm.

The definition uses strict representatives, consistently with `SymmKernel`.  Consequently all
pointwise algebra happens before integration; a later layer proves invariance under a.e. equality.

## Main definitions

* `TauCeti.DenseGraphLimits.SymmKernel.rectIntegral` is the integral of a kernel over a rectangle.
* `TauCeti.DenseGraphLimits.cutNorm` is the supremum of the absolute rectangle integrals.
* `TauCeti.DenseGraphLimits.cutNormSet` is the textbook set-form name for the same quantity.

## Main results

* `abs_rectIntegral_le_cutNorm` and `cutNorm_le` are the introduction and elimination rules for the
  supremum.
* `cutNorm_zero`, `cutNorm_neg`, `cutNorm_add_le`, and `cutNorm_smul` are the seminorm laws.
* `cutNorm_le_integral_abs` bounds the cut norm by the `L¹` norm.

## References

* L. Lovász, *Large Networks and Graph Limits*, §8.2.1.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, §4.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the cut norm and its set form;
  the signatures follow `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.
* The definition and rectangle-integral interface follow `Graphon/CutNorm.lean` in
  `cameronfreer/graphon` (Apache 2.0) at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`; the strict-kernel integrability and full seminorm
  API are developed here.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

namespace SymmKernel

/-- A bounded symmetric kernel is integrable on the product of two finite copies of its measure. -/
theorem integrable_prod [IsFiniteMeasure μ] (K : SymmKernel Ω μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ) := by
  obtain ⟨C, hC⟩ := K.exists_bound
  refine Integrable.of_bound K.measurable.aestronglyMeasurable C (ae_of_all _ fun p => ?_)
  simpa [Function.uncurry_apply_pair, Real.norm_eq_abs] using hC p.1 p.2

/-- The integral of a symmetric kernel over the rectangle `S × T`. -/
noncomputable def rectIntegral (K : SymmKernel Ω μ) (S T : Set Ω) : ℝ :=
  ∫ p in S ×ˢ T, K p.1 p.2 ∂(μ.prod μ)

/-- A rectangle integral is the product-measure integral restricted to the rectangle. -/
theorem rectIntegral_def (K : SymmKernel Ω μ) (S T : Set Ω) :
    K.rectIntegral μ S T = ∫ p in S ×ˢ T, K p.1 p.2 ∂(μ.prod μ) := (rfl)

/-- A rectangle integral can be evaluated as an iterated set integral. -/
theorem rectIntegral_eq_setIntegral_setIntegral [IsFiniteMeasure μ]
    (K : SymmKernel Ω μ) (S T : Set Ω) :
    K.rectIntegral μ S T = ∫ x in S, ∫ y in T, K x y ∂μ ∂μ := by
  rw [rectIntegral_def]
  exact setIntegral_prod _ K.integrable_prod.integrableOn

@[simp]
theorem rectIntegral_empty_left (K : SymmKernel Ω μ) (T : Set Ω) :
    K.rectIntegral μ ∅ T = 0 := by
  simp [rectIntegral_def]

@[simp]
theorem rectIntegral_empty_right (K : SymmKernel Ω μ) (S : Set Ω) :
    K.rectIntegral μ S ∅ = 0 := by
  simp [rectIntegral_def]

@[simp]
theorem rectIntegral_univ_univ (K : SymmKernel Ω μ) :
    K.rectIntegral μ univ univ = ∫ p, K p.1 p.2 ∂(μ.prod μ) := by
  simp [rectIntegral_def]

/-- Transposing a rectangle does not change the integral of a symmetric kernel. -/
theorem rectIntegral_comm [SFinite μ] (K : SymmKernel Ω μ) (S T : Set Ω) :
    K.rectIntegral μ S T = K.rectIntegral μ T S := by
  rw [rectIntegral, rectIntegral, ← setIntegral_prod_swap S T (fun p => K p.1 p.2)]
  exact integral_congr_ae (ae_of_all _ fun p => K.symm p.2 p.1)

@[simp]
theorem rectIntegral_zero (S T : Set Ω) :
    (0 : SymmKernel Ω μ).rectIntegral μ S T = 0 := by
  simp [rectIntegral]

@[simp]
theorem rectIntegral_add [IsFiniteMeasure μ] (K L : SymmKernel Ω μ) (S T : Set Ω) :
    (K + L).rectIntegral μ S T = K.rectIntegral μ S T + L.rectIntegral μ S T := by
  rw [rectIntegral, rectIntegral, rectIntegral]
  exact integral_add K.integrable_prod.integrableOn L.integrable_prod.integrableOn

@[simp]
theorem rectIntegral_neg (K : SymmKernel Ω μ) (S T : Set Ω) :
    (-K).rectIntegral μ S T = -K.rectIntegral μ S T := by
  unfold rectIntegral
  simpa only [SymmKernel.coe_neg, Pi.neg_apply] using
    (integral_neg (μ := (μ.prod μ).restrict (S ×ˢ T)) (fun p : Ω × Ω => K p.1 p.2))

@[simp]
theorem rectIntegral_sub [IsFiniteMeasure μ] (K L : SymmKernel Ω μ) (S T : Set Ω) :
    (K - L).rectIntegral μ S T = K.rectIntegral μ S T - L.rectIntegral μ S T := by
  rw [sub_eq_add_neg, rectIntegral_add, rectIntegral_neg, sub_eq_add_neg]

@[simp]
theorem rectIntegral_smul (c : ℝ) (K : SymmKernel Ω μ) (S T : Set Ω) :
    (c • K).rectIntegral μ S T = c * K.rectIntegral μ S T := by
  unfold rectIntegral
  simpa only [SymmKernel.coe_smul, Pi.smul_apply, smul_eq_mul] using
    (integral_smul (μ := (μ.prod μ).restrict (S ×ˢ T)) c (fun p : Ω × Ω => K p.1 p.2))

/-- The absolute value of any rectangle integral is bounded by the integral of `|K|` over the
whole product space. -/
theorem abs_rectIntegral_le_integral_abs [IsFiniteMeasure μ]
    (K : SymmKernel Ω μ) (S T : Set Ω) :
    |K.rectIntegral μ S T| ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) := by
  calc
    |K.rectIntegral μ S T|
        ≤ ∫ p in S ×ˢ T, |K p.1 p.2| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
      setIntegral_le_integral K.integrable_prod.abs (ae_of_all _ fun _ => abs_nonneg _)

end SymmKernel

/-- The set form of the cut norm on a finite measure space: the supremum of the absolute kernel
integrals over measurable rectangles. -/
noncomputable def cutNormSet [IsFiniteMeasure μ] (K : SymmKernel Ω μ) : ℝ :=
  ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
    |K.rectIntegral μ S T|

/-- The cut norm of a symmetric kernel on a finite measure space: the supremum over measurable
sets `S` and `T` of the absolute value of the integral of the kernel over `S × T`. -/
noncomputable def cutNorm [IsFiniteMeasure μ] (K : SymmKernel Ω μ) : ℝ := cutNormSet μ K

variable [IsFiniteMeasure μ]

/-- The cut norm is definitionally its measurable-set form.  This is not a `simp` lemma: `cutNorm`
is the normal form that the rest of the API, and hence the `simp` set, is stated in. -/
theorem cutNorm_eq_cutNormSet (K : SymmKernel Ω μ) : cutNorm μ K = cutNormSet μ K := (rfl)

/-- The set-form cut norm is the iterated supremum over measurable rectangles. -/
theorem cutNormSet_def (K : SymmKernel Ω μ) :
    cutNormSet μ K =
      ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
        |K.rectIntegral μ S T| := (rfl)

omit [IsFiniteMeasure μ] in
private theorem integral_abs_nonneg (K : SymmKernel Ω μ) :
    0 ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  integral_nonneg fun _ => abs_nonneg _

/-- To prove an upper bound on the cut norm, it suffices to prove it for every measurable
rectangle. -/
theorem cutNorm_le {K : SymmKernel Ω μ} {C : ℝ}
    (h : ∀ S, MeasurableSet S → ∀ T, MeasurableSet T → |K.rectIntegral μ S T| ≤ C) :
    cutNorm μ K ≤ C := by
  have hC : 0 ≤ C := by simpa using h ∅ MeasurableSet.empty ∅ MeasurableSet.empty
  unfold cutNorm cutNormSet
  apply Real.iSup_le _ hC
  intro S
  apply Real.iSup_le _ hC
  intro hS
  apply Real.iSup_le _ hC
  intro T
  apply Real.iSup_le _ hC
  exact h S hS T

private theorem iSup_measurableSet_right_le_integral_abs
    (K : SymmKernel Ω μ) (S T : Set Ω) :
    (⨆ (_ : MeasurableSet T), |K.rectIntegral μ S T|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun _ => K.abs_rectIntegral_le_integral_abs μ S T) (integral_abs_nonneg μ K)

private theorem iSup_right_le_integral_abs (K : SymmKernel Ω μ) (S : Set Ω) :
    (⨆ (T : Set Ω) (_ : MeasurableSet T), |K.rectIntegral μ S T|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun T => iSup_measurableSet_right_le_integral_abs μ K S T)
    (integral_abs_nonneg μ K)

private theorem iSup_measurableSet_left_le_integral_abs
    (K : SymmKernel Ω μ) (S : Set Ω) :
    (⨆ (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
      |K.rectIntegral μ S T|) ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun _ => iSup_right_le_integral_abs μ K S) (integral_abs_nonneg μ K)

private theorem iSup_left_le_integral_abs (K : SymmKernel Ω μ) :
    (⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
      |K.rectIntegral μ S T|) ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun S => iSup_measurableSet_left_le_integral_abs μ K S)
    (integral_abs_nonneg μ K)

private theorem bddAbove_range_abs_rectIntegral_measurableSet_right
    (K : SymmKernel Ω μ) (S T : Set Ω) :
    BddAbove (range fun _ : MeasurableSet T => |K.rectIntegral μ S T|) := by
  refine ⟨∫ p, |K p.1 p.2| ∂(μ.prod μ), ?_⟩
  rintro _ ⟨_, rfl⟩
  exact K.abs_rectIntegral_le_integral_abs μ S T

private theorem bddAbove_range_iSup_abs_rectIntegral_right
    (K : SymmKernel Ω μ) (S : Set Ω) :
    BddAbove (range fun T : Set Ω =>
      ⨆ (_ : MeasurableSet T), |K.rectIntegral μ S T|) := by
  refine ⟨∫ p, |K p.1 p.2| ∂(μ.prod μ), ?_⟩
  rintro _ ⟨T, rfl⟩
  exact iSup_measurableSet_right_le_integral_abs μ K S T

private theorem bddAbove_range_iSup_abs_rectIntegral_measurableSet_left
    (K : SymmKernel Ω μ) (S : Set Ω) :
    BddAbove (range fun _ : MeasurableSet S =>
      ⨆ (T : Set Ω) (_ : MeasurableSet T), |K.rectIntegral μ S T|) := by
  refine ⟨∫ p, |K p.1 p.2| ∂(μ.prod μ), ?_⟩
  rintro _ ⟨_, rfl⟩
  exact iSup_right_le_integral_abs μ K S

private theorem bddAbove_range_iSup_abs_rectIntegral_left (K : SymmKernel Ω μ) :
    BddAbove (range fun S : Set Ω =>
      ⨆ (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
        |K.rectIntegral μ S T|) := by
  refine ⟨∫ p, |K p.1 p.2| ∂(μ.prod μ), ?_⟩
  rintro _ ⟨S, rfl⟩
  exact iSup_measurableSet_left_le_integral_abs μ K S

/-- Every measurable rectangle integral is bounded by the cut norm. -/
theorem abs_rectIntegral_le_cutNorm (K : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |K.rectIntegral μ S T| ≤ cutNorm μ K := by
  unfold cutNorm cutNormSet
  apply le_ciSup_of_le (bddAbove_range_iSup_abs_rectIntegral_left μ K) S
  apply le_ciSup_of_le (bddAbove_range_iSup_abs_rectIntegral_measurableSet_left μ K S) hS
  apply le_ciSup_of_le (bddAbove_range_iSup_abs_rectIntegral_right μ K S) T
  exact le_ciSup (bddAbove_range_abs_rectIntegral_measurableSet_right μ K S T) hT

/-- The cut norm is nonnegative. -/
theorem cutNorm_nonneg (K : SymmKernel Ω μ) : 0 ≤ cutNorm μ K := by
  simpa using abs_rectIntegral_le_cutNorm μ K MeasurableSet.empty MeasurableSet.empty

/-- The cut norm is bounded by the integral of the absolute value of the kernel. -/
theorem cutNorm_le_integral_abs (K : SymmKernel Ω μ) :
    cutNorm μ K ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) := by
  unfold cutNorm cutNormSet
  exact iSup_left_le_integral_abs μ K

/-- The zero kernel has cut norm zero. -/
@[simp]
theorem cutNorm_zero : cutNorm μ (0 : SymmKernel Ω μ) = 0 := by
  apply le_antisymm
  · apply cutNorm_le μ
    simp
  · exact cutNorm_nonneg μ 0

/-- Negating a kernel does not change its cut norm. -/
@[simp]
theorem cutNorm_neg (K : SymmKernel Ω μ) : cutNorm μ (-K) = cutNorm μ K := by
  unfold cutNorm cutNormSet
  simp

/-- The cut norm satisfies the triangle inequality. -/
theorem cutNorm_add_le (K L : SymmKernel Ω μ) :
    cutNorm μ (K + L) ≤ cutNorm μ K + cutNorm μ L := by
  apply cutNorm_le μ
  intro S hS T hT
  rw [SymmKernel.rectIntegral_add]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_rectIntegral_le_cutNorm μ K hS hT) (abs_rectIntegral_le_cutNorm μ L hS hT))

/-- The cut norm of a difference is at most the sum of the two cut norms. -/
theorem cutNorm_sub_le (K L : SymmKernel Ω μ) :
    cutNorm μ (K - L) ≤ cutNorm μ K + cutNorm μ L := by
  simpa [sub_eq_add_neg] using cutNorm_add_le μ K (-L)

/-- The cut norm is absolutely homogeneous. -/
theorem cutNorm_smul (c : ℝ) (K : SymmKernel Ω μ) :
    cutNorm μ (c • K) = |c| * cutNorm μ K := by
  unfold cutNorm cutNormSet
  simp only [SymmKernel.rectIntegral_smul, abs_mul,
    Real.mul_iSup_of_nonneg (abs_nonneg c)]

end DenseGraphLimits

end TauCeti
