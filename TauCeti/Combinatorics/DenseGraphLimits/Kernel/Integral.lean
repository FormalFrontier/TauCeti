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
# Integrating a symmetric kernel

The integrals of a bounded symmetric kernel that the cut norm and its consumers are built from:
over a measurable rectangle, against a pair of test functions, and against one test function with
the other variable left free.

```text
rectIntegral K S T = ∫ (S × T) K            testIntegral K u v = ∫∫ u(x) v(y) K(x,y)
partialIntegral K v x = ∫ v(y) K(x,y)
```

This file is deliberately independent of the cut norm.  Several consumers — the block averages of a
step graphon, and the `L²` theory — need rectangle integrals and nothing else, and previously
reached the supremum and signed-cut-norm layer to obtain them.

The definitions use strict representatives, consistently with `SymmKernel`, so all pointwise algebra
happens before integration.

## Main definitions

* `TauCeti.DenseGraphLimits.SymmKernel.rectIntegral` — the integral over a rectangle;
* `TauCeti.DenseGraphLimits.SymmKernel.testIntegral` — the pairing with two test functions, of which
  a rectangle integral is the indicator case;
* `TauCeti.DenseGraphLimits.SymmKernel.partialIntegral` — the pairing with one.

## Main results

* the additive and scaling laws for `rectIntegral`, and its `L¹` bound;
* `testIntegral_indicator_one` — testing against indicators recovers a rectangle integral;
* `testIntegral_eq_integral_partialIntegral` — the iterated form.

## References

* L. Lovász, *Large Networks and Graph Limits*, §8.2.1.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, §4.
* The rectangle-integral interface follows `Graphon/CutNorm.lean` in `cameronfreer/graphon`
  (Apache 2.0) at commit `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`; the strict-kernel
  integrability is developed here.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

namespace SymmKernel

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
  exact setIntegral_prod _ K.integrable_uncurry.integrableOn

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
  rw [rectIntegral_def, rectIntegral_def, ← setIntegral_prod_swap S T (fun p => K p.1 p.2)]
  exact integral_congr_ae (ae_of_all _ fun p => K.symm p.2 p.1)

@[simp]
theorem rectIntegral_zero (S T : Set Ω) :
    (0 : SymmKernel Ω μ).rectIntegral μ S T = 0 := by
  simp [rectIntegral_def]

@[simp]
theorem rectIntegral_add [IsFiniteMeasure μ] (K L : SymmKernel Ω μ) (S T : Set Ω) :
    (K + L).rectIntegral μ S T = K.rectIntegral μ S T + L.rectIntegral μ S T := by
  rw [rectIntegral_def, rectIntegral_def, rectIntegral_def]
  exact integral_add K.integrable_uncurry.integrableOn L.integrable_uncurry.integrableOn

@[simp]
theorem rectIntegral_neg (K : SymmKernel Ω μ) (S T : Set Ω) :
    (-K).rectIntegral μ S T = -K.rectIntegral μ S T := by
  rw [rectIntegral_def, rectIntegral_def]
  simpa only [SymmKernel.coe_neg, Pi.neg_apply] using
    (integral_neg (μ := (μ.prod μ).restrict (S ×ˢ T)) (fun p : Ω × Ω => K p.1 p.2))

@[simp]
theorem rectIntegral_sub [IsFiniteMeasure μ] (K L : SymmKernel Ω μ) (S T : Set Ω) :
    (K - L).rectIntegral μ S T = K.rectIntegral μ S T - L.rectIntegral μ S T := by
  rw [sub_eq_add_neg, rectIntegral_add, rectIntegral_neg, sub_eq_add_neg]

@[simp]
theorem rectIntegral_smul (c : ℝ) (K : SymmKernel Ω μ) (S T : Set Ω) :
    (c • K).rectIntegral μ S T = c * K.rectIntegral μ S T := by
  rw [rectIntegral_def, rectIntegral_def]
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
      setIntegral_le_integral K.integrable_uncurry.abs (ae_of_all _ fun _ => abs_nonneg _)

/-- **Change of variables for a rectangle integral.** If `f` pushes `ν` forward to `μ`, then the
rectangle integral of `K` over `S × T` equals the rectangle integral of the pullback kernel over
the preimage rectangle `f ⁻¹' S × f ⁻¹' T`.

The two rectangles carry the two measures of the type ascriptions, so this is the statement that
lets a cut-norm estimate move between a carrier and a pushforward of it. -/
theorem rectIntegral_comap_preimage {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    {f : α → Ω} (hf : MeasurePreserving f ν μ) (K : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (K.comap f hf.measurable ν).rectIntegral ν (f ⁻¹' S) (f ⁻¹' T) = K.rectIntegral μ S T := by
  have hmap : (ν.prod ν).map (Prod.map f f) = μ.prod μ := (hf.prod hf).map_eq
  have key : ∫ p in S ×ˢ T, K p.1 p.2 ∂((ν.prod ν).map (Prod.map f f)) =
      ∫ p in Prod.map f f ⁻¹' (S ×ˢ T), K (f p.1) (f p.2) ∂(ν.prod ν) :=
    setIntegral_map (hS.prod hT) K.measurable.aestronglyMeasurable
      (hf.measurable.prodMap hf.measurable).aemeasurable
  rw [rectIntegral_def, rectIntegral_def, ← hmap, key]
  simp only [comap_apply]
  rfl

/-- The integral of a symmetric kernel against a pair of test functions:
`∫∫ u(x) v(y) K(x,y)`.

This generalises `rectIntegral`, which is the case of two indicator functions
(`testIntegral_indicator_one`), and is the quantity the signed cut norm takes a supremum of. -/
noncomputable def testIntegral (K : SymmKernel Ω μ) (u v : Ω → ℝ) : ℝ :=
  ∫ p, u p.1 * v p.2 * K p.1 p.2 ∂(μ.prod μ)

/-- A test integral is the product-measure integral of `u ⊗ v · K`. -/
theorem testIntegral_def (K : SymmKernel Ω μ) (u v : Ω → ℝ) :
    K.testIntegral μ u v = ∫ p, u p.1 * v p.2 * K p.1 p.2 ∂(μ.prod μ) := (rfl)

/-- The integrand of a test integral is integrable when the test functions are measurable and
`[-1,1]`-valued: it is then dominated pointwise by `|K|`, which is integrable. -/
theorem integrable_testIntegrand [IsFiniteMeasure μ] (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun p : Ω × Ω => u p.1 * v p.2 * K p.1 p.2) (μ.prod μ) := by
  refine Integrable.mono' K.integrable_uncurry.abs
    (((hu.comp measurable_fst).mul (hv.comp measurable_snd)).mul
      K.measurable).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |u p.1| * |v p.2| * |K p.1 p.2|
      ≤ 1 * 1 * |K p.1 p.2| := by
        gcongr
        · exact abs_le.2 (hu1 p.1)
        · exact abs_le.2 (hv1 p.2)
    _ = |K p.1 p.2| := by ring

/-- Every `[-1,1]`-test integral is bounded by the `L¹` norm of the kernel.  This is the bound that
makes the signed cut norm's supremum a supremum of a bounded set. -/
theorem abs_testIntegral_le_integral_abs [IsFiniteMeasure μ] (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    |K.testIntegral μ u v| ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) := by
  rw [testIntegral_def]
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono (K.integrable_testIntegrand μ hu hv hu1 hv1).abs
    K.integrable_uncurry.abs fun p => ?_
  rw [abs_mul, abs_mul]
  calc |u p.1| * |v p.2| * |K p.1 p.2|
      ≤ 1 * 1 * |K p.1 p.2| := by
        gcongr
        · exact abs_le.2 (hu1 p.1)
        · exact abs_le.2 (hv1 p.2)
    _ = |K p.1 p.2| := by ring

/-- Testing against two indicator functions recovers the rectangle integral.  This is what makes
the set form of the cut norm a special case of the signed form. -/
@[simp]
theorem testIntegral_indicator_one (K : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    K.testIntegral μ (S.indicator 1) (T.indicator 1) = K.rectIntegral μ S T := by
  rw [testIntegral_def, rectIntegral_def, ← integral_indicator (hS.prod hT)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp1 : p.1 ∈ S <;> by_cases hp2 : p.2 ∈ T <;> simp [hp1, hp2, Set.mem_prod]

/-- Swapping the two test functions of a symmetric kernel leaves the pairing unchanged. -/
theorem testIntegral_comm [SFinite μ] (K : SymmKernel Ω μ) (u v : Ω → ℝ) :
    K.testIntegral μ u v = K.testIntegral μ v u := by
  rw [testIntegral_def, testIntegral_def,
    ← integral_prod_swap (fun p : Ω × Ω => v p.1 * u p.2 * K p.1 p.2)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [K.symm p.2 p.1]
  ring

/-- The inner integral of a kernel against a single test function, `x ↦ ∫ v(y) K(x,y)`.

This is the partial pairing that the extremal step of the factor sandwich optimises over.  When `μ`
is finite and `v` is measurable and `[-1,1]`-valued, the partial pairing is measurable and
integrable. The definition itself asks nothing of `v`. -/
noncomputable def partialIntegral (K : SymmKernel Ω μ) (v : Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, v y * K x y ∂μ

/-- The defining integral of `partialIntegral`. -/
theorem partialIntegral_def (K : SymmKernel Ω μ) (v : Ω → ℝ) (x : Ω) :
    K.partialIntegral μ v x = ∫ y, v y * K x y ∂μ := (rfl)

/-- The partial pairing is measurable in the remaining variable. -/
theorem measurable_partialIntegral [SFinite μ] (K : SymmKernel Ω μ) {v : Ω → ℝ}
    (hv : Measurable v) :
    Measurable (K.partialIntegral μ v) := by
  have h : Measurable fun p : Ω × Ω => v p.2 * K p.1 p.2 :=
    (hv.comp measurable_snd).mul K.measurable
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The partial pairing against a `[-1,1]`-valued test function is integrable. -/
theorem integrable_partialIntegral [IsFiniteMeasure μ] (K : SymmKernel Ω μ) {v : Ω → ℝ}
    (hv : Measurable v) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    Integrable (K.partialIntegral μ v) μ := by
  have h1 : ∀ x : Ω, (fun _ : Ω => (1 : ℝ)) x ∈ Icc (-1 : ℝ) 1 := fun _ => by norm_num
  have h := (K.integrable_testIntegrand μ measurable_const hv h1 hv1).integral_prod_left
  simp only [one_mul] at h
  exact h

/-- A test integral is the integral of the left test function against the partial pairing.

Only integrability of the product integrand is needed — that is all Fubini asks.  A caller with
bounded measurable test functions gets it from `integrable_testIntegrand`. -/
theorem testIntegral_eq_integral_partialIntegral [SFinite μ] (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (h : Integrable (fun p : Ω × Ω => u p.1 * v p.2 * K p.1 p.2) (μ.prod μ)) :
    K.testIntegral μ u v = ∫ x, u x * K.partialIntegral μ v x ∂μ := by
  have key : ∀ x, ∫ y, u x * v y * K x y ∂μ = u x * K.partialIntegral μ v x := by
    intro x
    rw [partialIntegral_def, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [testIntegral_def, integral_prod _ h]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- The pairing is subtractive in the left test function, given integrability of both pieces. -/
theorem testIntegral_sub_left (K : SymmKernel Ω μ) {u₁ u₂ v : Ω → ℝ}
    (h₁ : Integrable (fun p : Ω × Ω => u₁ p.1 * v p.2 * K p.1 p.2) (μ.prod μ))
    (h₂ : Integrable (fun p : Ω × Ω => u₂ p.1 * v p.2 * K p.1 p.2) (μ.prod μ)) :
    K.testIntegral μ (u₁ - u₂) v = K.testIntegral μ u₁ v - K.testIntegral μ u₂ v := by
  rw [testIntegral_def, testIntegral_def, testIntegral_def, ← integral_sub h₁ h₂]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply]
  ring

/-- The pairing is subtractive in the right test function, given integrability of both pieces. -/
theorem testIntegral_sub_right (K : SymmKernel Ω μ) {u v₁ v₂ : Ω → ℝ}
    (h₁ : Integrable (fun p : Ω × Ω => u p.1 * v₁ p.2 * K p.1 p.2) (μ.prod μ))
    (h₂ : Integrable (fun p : Ω × Ω => u p.1 * v₂ p.2 * K p.1 p.2) (μ.prod μ)) :
    K.testIntegral μ u (v₁ - v₂) = K.testIntegral μ u v₁ - K.testIntegral μ u v₂ := by
  rw [testIntegral_def, testIntegral_def, testIntegral_def, ← integral_sub h₁ h₂]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply]
  ring

end SymmKernel

end DenseGraphLimits

end TauCeti
