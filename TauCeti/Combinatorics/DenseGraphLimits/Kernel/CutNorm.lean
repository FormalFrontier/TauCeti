/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# The cut norm of a symmetric kernel

This file defines the cut norm of a bounded symmetric kernel on a finite measure space by

`‖K‖□ = sup |∫_(S × T) K|`,

where the supremum ranges over measurable sets `S` and `T`.  The file develops the interface needed
by the cut-distance and counting-lemma layers: rectangle integrals, the bound of every rectangle by
the cut norm, the seminorm laws, and the comparison with the `L¹` norm.

The definition uses strict representatives, consistently with `SymmKernel`.  Consequently all
pointwise algebra happens before integration; a later layer proves invariance under a.e. equality.

## Main definitions

* `TauCeti.DenseGraphLimits.SymmKernel.rectIntegral` is the integral of a kernel over a rectangle.
* `TauCeti.DenseGraphLimits.cutNorm` is the supremum of the absolute rectangle integrals.
* `TauCeti.DenseGraphLimits.cutNormSet` is the separately roadmap-pinned textbook set-form name for
  the same quantity.
* `TauCeti.DenseGraphLimits.SymmKernel.testIntegral` is the integral of a kernel against a pair of
  test functions, of which a rectangle integral is the indicator case.
* `TauCeti.DenseGraphLimits.SymmKernel.partialIntegral` is the pairing against one test function
  only, the object the extremal step of the factor sandwich optimises over.
* `TauCeti.DenseGraphLimits.cutNormSigned` is the signed cut norm: the same supremum taken over
  measurable `[-1,1]`-valued test functions rather than over indicators.

## Main results

* `abs_rectIntegral_le_cutNorm` and `cutNorm_le` are the introduction and elimination rules for the
  supremum.
* `cutNorm_zero`, `cutNorm_neg`, `cutNorm_add_le`, and `cutNorm_smul` are the seminorm laws.
* `cutNorm_le_integral_abs` bounds the cut norm by the `L¹` norm.
* `rectIntegral_comap_preimage` and `cutNorm_le_cutNorm_comap` are the change of variables along a
  pushforward: a rectangle downstairs pulls back to one upstairs with the same integral, so the cut
  norm does not increase when a carrier is replaced by one it is a pushforward of.
* `abs_testIntegral_le_cutNormSigned` and `cutNormSigned_le` are the corresponding introduction and
  elimination rules for the signed cut norm.
* `cutNorm_le_cutNormSigned` and `cutNormSigned_le_four_mul_cutNorm` are the two sides of the
  factor sandwich relating the two forms.

## References

* L. Lovász, *Large Networks and Graph Limits*, §8.2.1.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, §4.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the cut norm, its set form, and
  the signed form; the signatures follow `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.
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
theorem integrable_uncurry [IsFiniteMeasure μ] (K : SymmKernel Ω μ) :
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
is finite and `v` is measurable and `[-1,1]`-valued — the hypotheses `exists_pm_one_left` carries —
the supremum over the remaining test function is attained at the sign of this function.  The
definition itself asks nothing of `v`. -/
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

/-- The set form of the cut norm: the supremum of the absolute kernel integrals over measurable
rectangles. -/
noncomputable def cutNormSet [IsFiniteMeasure μ] (K : SymmKernel Ω μ) : ℝ :=
  let ν : FiniteMeasure Ω := ⟨μ, inferInstance⟩
  ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
    |K.rectIntegral (ν : Measure Ω) S T|

/-- The cut norm of a symmetric kernel: the supremum over measurable sets `S` and `T` of the
absolute integral over `S × T`. -/
noncomputable def cutNorm [IsFiniteMeasure μ] (K : SymmKernel Ω μ) : ℝ := cutNormSet μ K

/-- The **signed cut norm**: the supremum, over measurable `[-1,1]`-valued test functions `u` and
`v`, of `|∫∫ u(x) v(y) K(x,y)|`.

Relaxing the indicators of `cutNorm` to `[-1,1]`-valued functions can only increase the supremum
(`cutNorm_le_cutNormSigned`), and increases it by at most a factor of `4`
(`cutNormSigned_le_four_mul_cutNorm`), so the two forms define the same topology.

`[IsFiniteMeasure μ]` is required, as for `cutNorm`, and is not decoration: on an infinite measure
the test integrals are unbounded — take `μ` Lebesgue, `K` the constant kernel `1`, and `u = v` the
indicator of `[0, n]`, giving `n²` — so the conditionally complete supremum on `ℝ` would collapse to
its junk value `0` for a kernel that is nowhere near zero.  Finiteness is what makes
`abs_testIntegral_le_integral_abs` bound the range, and hence what makes this a faithful
supremum. -/
noncomputable def cutNormSigned [IsFiniteMeasure μ] (K : SymmKernel Ω μ) : ℝ :=
  let ν : FiniteMeasure Ω := ⟨μ, inferInstance⟩
  ⨆ (u : Ω → ℝ) (_ : Measurable u) (_ : ∀ x, u x ∈ Icc (-1 : ℝ) 1)
    (v : Ω → ℝ) (_ : Measurable v) (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1),
    |K.testIntegral (ν : Measure Ω) u v|

variable [IsFiniteMeasure μ]

/-- The cut norm is definitionally its separately roadmap-pinned measurable-set form.  This is not
a `simp` lemma: `cutNorm` is the normal form that the rest of the API, and hence the `simp` set, is
stated in. -/
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
  rw [cutNorm_eq_cutNormSet, cutNormSet_def]
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

private theorem bddAbove_range_of_forall_le {I : Sort*} {f : I → ℝ} {C : ℝ}
    (h : ∀ i, f i ≤ C) : BddAbove (range f) :=
  ⟨C, Set.forall_mem_range.2 h⟩

/-- Every measurable rectangle integral is bounded by the cut norm. -/
theorem abs_rectIntegral_le_cutNorm (K : SymmKernel Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |K.rectIntegral μ S T| ≤ cutNorm μ K := by
  rw [cutNorm_eq_cutNormSet, cutNormSet_def]
  apply le_ciSup_of_le (bddAbove_range_of_forall_le fun S =>
    iSup_measurableSet_left_le_integral_abs μ K S) S
  apply le_ciSup_of_le (bddAbove_range_of_forall_le fun _ =>
    iSup_right_le_integral_abs μ K S) hS
  apply le_ciSup_of_le (bddAbove_range_of_forall_le fun T =>
    iSup_measurableSet_right_le_integral_abs μ K S T) T
  exact le_ciSup (bddAbove_range_of_forall_le fun _ =>
    K.abs_rectIntegral_le_integral_abs μ S T) hT

/-- The cut norm is at most `C` exactly when every measurable rectangle integral is. -/
theorem cutNorm_le_iff {K : SymmKernel Ω μ} {C : ℝ} :
    cutNorm μ K ≤ C ↔
      ∀ S, MeasurableSet S → ∀ T, MeasurableSet T → |K.rectIntegral μ S T| ≤ C := by
  constructor
  · intro h S hS T hT
    exact (abs_rectIntegral_le_cutNorm μ K hS hT).trans h
  · exact cutNorm_le μ

/-- Any strict lower bound on the cut norm is exceeded by some measurable rectangle integral. -/
theorem exists_lt_abs_rectIntegral (K : SymmKernel Ω μ) {c : ℝ} (h : c < cutNorm μ K) :
    ∃ S T, MeasurableSet S ∧ MeasurableSet T ∧ c < |K.rectIntegral μ S T| := by
  by_contra h'
  apply (not_le_of_gt h)
  apply cutNorm_le μ
  intro S hS T hT
  exact le_of_not_gt fun hST => h' ⟨S, T, hS, hT, hST⟩

/-- The cut norm is nonnegative. -/
theorem cutNorm_nonneg (K : SymmKernel Ω μ) : 0 ≤ cutNorm μ K := by
  rw [cutNorm_eq_cutNormSet, cutNormSet_def]
  exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The cut norm is bounded by the integral of the absolute value of the kernel. -/
theorem cutNorm_le_integral_abs (K : SymmKernel Ω μ) :
    cutNorm μ K ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  cutNorm_le μ fun S _ T _ => K.abs_rectIntegral_le_integral_abs μ S T

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
  rw [cutNorm_eq_cutNormSet, cutNormSet_def, cutNorm_eq_cutNormSet, cutNormSet_def]
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
@[simp]
theorem cutNorm_smul (c : ℝ) (K : SymmKernel Ω μ) :
    cutNorm μ (c • K) = |c| * cutNorm μ K := by
  rw [cutNorm_eq_cutNormSet, cutNormSet_def, cutNorm_eq_cutNormSet, cutNormSet_def]
  simp only [SymmKernel.rectIntegral_smul, abs_mul,
    Real.mul_iSup_of_nonneg (abs_nonneg c)]

/-- **The cut norm does not increase along a pushforward.** If `f` pushes `ν` forward to `μ`, then
the cut norm of `K` over `μ` is at most the cut norm of its pullback over `ν`.

Every measurable rectangle downstairs pulls back to a measurable rectangle upstairs with the same
integral (`rectIntegral_comap_preimage`), so the upstairs supremum ranges over at least as much.
The swap application obtains equality by applying this bound in both directions. The common-carrier
application only needs the stated inequality and identifies the pulled-back kernel outright. -/
theorem cutNorm_le_cutNorm_comap {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → Ω} (hf : MeasurePreserving f ν μ) (K : SymmKernel Ω μ) :
    cutNorm μ K ≤ cutNorm ν (K.comap f hf.measurable ν) :=
  cutNorm_le μ fun S hS T hT => by
    rw [← SymmKernel.rectIntegral_comap_preimage μ hf K hS hT]
    exact abs_rectIntegral_le_cutNorm ν _ (hf.measurable hS) (hf.measurable hT)

/-- The signed cut norm is the iterated supremum over measurable `[-1,1]`-valued test functions. -/
theorem cutNormSigned_def (K : SymmKernel Ω μ) :
    cutNormSigned μ K =
      ⨆ (u : Ω → ℝ) (_ : Measurable u) (_ : ∀ x, u x ∈ Icc (-1 : ℝ) 1)
        (v : Ω → ℝ) (_ : Measurable v) (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1),
        |K.testIntegral μ u v| := (rfl)

/-  The supremum defining `cutNormSigned` has six binders, so bounding it from below at a chosen
pair of test functions needs the range at each level to be bounded above.  The five private lemmas
below strip one binder each, all with the same `L¹` bound; they play the role that
`iSup_right_le_integral_abs` and its siblings play for `cutNorm`. -/
private theorem iSup_mem_right_le_integral_abs (K : SymmKernel Ω μ) (u v : Ω → ℝ)
    (hu : Measurable u) (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (hv : Measurable v) :
    (⨆ (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1), |K.testIntegral μ u v|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun hv1 => K.abs_testIntegral_le_integral_abs μ hu hv hu1 hv1)
    (integral_abs_nonneg μ K)

private theorem iSup_measurable_right_le_integral_abs (K : SymmKernel Ω μ) (u v : Ω → ℝ)
    (hu : Measurable u) (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) :
    (⨆ (_ : Measurable v) (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1), |K.testIntegral μ u v|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun hv => iSup_mem_right_le_integral_abs μ K u v hu hu1 hv)
    (integral_abs_nonneg μ K)

private theorem iSup_fun_right_le_integral_abs (K : SymmKernel Ω μ) (u : Ω → ℝ)
    (hu : Measurable u) (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) :
    (⨆ (v : Ω → ℝ) (_ : Measurable v) (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1),
      |K.testIntegral μ u v|) ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun v => iSup_measurable_right_le_integral_abs μ K u v hu hu1)
    (integral_abs_nonneg μ K)

private theorem iSup_mem_left_le_integral_abs (K : SymmKernel Ω μ) (u : Ω → ℝ)
    (hu : Measurable u) :
    (⨆ (_ : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (v : Ω → ℝ) (_ : Measurable v)
      (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1), |K.testIntegral μ u v|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun hu1 => iSup_fun_right_le_integral_abs μ K u hu hu1) (integral_abs_nonneg μ K)

private theorem iSup_measurable_left_le_integral_abs (K : SymmKernel Ω μ) (u : Ω → ℝ) :
    (⨆ (_ : Measurable u) (_ : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (v : Ω → ℝ) (_ : Measurable v)
      (_ : ∀ y, v y ∈ Icc (-1 : ℝ) 1), |K.testIntegral μ u v|) ≤
      ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  Real.iSup_le (fun hu => iSup_mem_left_le_integral_abs μ K u hu) (integral_abs_nonneg μ K)

/-- Every `[-1,1]`-test integral is bounded by the signed cut norm.  This is the introduction rule
for the supremum, mirroring `abs_rectIntegral_le_cutNorm`. -/
theorem abs_testIntegral_le_cutNormSigned (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    |K.testIntegral μ u v| ≤ cutNormSigned μ K := by
  rw [cutNormSigned_def]
  refine le_ciSup_of_le (bddAbove_range_of_forall_le fun u' =>
    iSup_measurable_left_le_integral_abs μ K u') u ?_
  refine le_ciSup_of_le (bddAbove_range_of_forall_le fun _ =>
    iSup_mem_left_le_integral_abs μ K u hu) hu ?_
  refine le_ciSup_of_le (bddAbove_range_of_forall_le fun _ =>
    iSup_fun_right_le_integral_abs μ K u hu hu1) hu1 ?_
  refine le_ciSup_of_le (bddAbove_range_of_forall_le fun v' =>
    iSup_measurable_right_le_integral_abs μ K u v' hu hu1) v ?_
  refine le_ciSup_of_le (bddAbove_range_of_forall_le fun _ =>
    iSup_mem_right_le_integral_abs μ K u v hu hu1 hv) hv ?_
  exact le_ciSup (bddAbove_range_of_forall_le fun _ =>
    K.abs_testIntegral_le_integral_abs μ hu hv hu1 hv1) hv1

/-- To prove an upper bound on the signed cut norm, it suffices to prove it for every pair of
measurable `[-1,1]`-valued test functions.  Nonnegativity of the bound is not a hypothesis: it
follows by testing against the zero function. -/
theorem cutNormSigned_le {K : SymmKernel Ω μ} {C : ℝ}
    (h : ∀ u v : Ω → ℝ, Measurable u → Measurable v → (∀ x, u x ∈ Icc (-1 : ℝ) 1) →
      (∀ y, v y ∈ Icc (-1 : ℝ) 1) → |K.testIntegral μ u v| ≤ C) :
    cutNormSigned μ K ≤ C := by
  have hzero : ∀ x : Ω, (0 : Ω → ℝ) x ∈ Icc (-1 : ℝ) 1 := fun _ => by norm_num
  have hC : 0 ≤ C := by
    simpa [SymmKernel.testIntegral_def] using
      h 0 0 measurable_const measurable_const hzero hzero
  rw [cutNormSigned_def]
  exact Real.iSup_le (fun u => Real.iSup_le (fun hu => Real.iSup_le (fun hu1 =>
    Real.iSup_le (fun v => Real.iSup_le (fun hv => Real.iSup_le (fun hv1 =>
      h u v hu hv hu1 hv1) hC) hC) hC) hC) hC) hC

/-- The signed cut norm is nonnegative. -/
theorem cutNormSigned_nonneg (K : SymmKernel Ω μ) : 0 ≤ cutNormSigned μ K := by
  rw [cutNormSigned_def]
  exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The signed cut norm is bounded by the `L¹` norm of the kernel, as the cut norm is. -/
theorem cutNormSigned_le_integral_abs (K : SymmKernel Ω μ) :
    cutNormSigned μ K ≤ ∫ p, |K p.1 p.2| ∂(μ.prod μ) :=
  cutNormSigned_le μ fun _ _ hu hv hu1 hv1 => K.abs_testIntegral_le_integral_abs μ hu hv hu1 hv1

/-- **Lower side of the factor sandwich.** The cut norm is at most the signed cut norm: indicators
are `[-1,1]`-valued test functions, so the signed supremum ranges over more pairs. -/
theorem cutNorm_le_cutNormSigned (K : SymmKernel Ω μ) : cutNorm μ K ≤ cutNormSigned μ K := by
  refine cutNorm_le μ fun S hS T hT => ?_
  rw [← K.testIntegral_indicator_one μ hS hT]
  refine abs_testIntegral_le_cutNormSigned μ K (measurable_one.indicator hS)
    (measurable_one.indicator hT) (fun x => ?_) fun y => ?_
  · by_cases hx : x ∈ S <;> simp [hx]
  · by_cases hy : y ∈ T <;> simp [hy]

/-- The extremal step: replacing the left test function by the sign of the inner integral can only
increase the pairing, and the replacement is `±1`-valued. -/
private theorem exists_pm_one_left (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (-1 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    ∃ w : Ω → ℝ, Measurable w ∧ (∀ x, w x = 1 ∨ w x = -1) ∧
      |K.testIntegral μ u v| ≤ K.testIntegral μ w v := by
  set g := K.partialIntegral μ v with hg_def
  have hg : Measurable g := K.measurable_partialIntegral μ hv
  have hgint : Integrable g μ := K.integrable_partialIntegral μ hv hv1
  refine ⟨fun x => if 0 ≤ g x then 1 else -1, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const
  · intro x; by_cases hx : 0 ≤ g x <;> simp [hx]
  · have hw1 : ∀ x, (if 0 ≤ g x then (1 : ℝ) else -1) ∈ Icc (-1 : ℝ) 1 := by
      intro x; by_cases hx : 0 ≤ g x <;> simp [hx]
    have hwm : Measurable fun x => if 0 ≤ g x then (1 : ℝ) else -1 :=
      Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const
    rw [K.testIntegral_eq_integral_partialIntegral μ
        (K.integrable_testIntegrand μ hu hv hu1 hv1),
      K.testIntegral_eq_integral_partialIntegral μ
        (K.integrable_testIntegrand μ hwm hv hw1 hv1), ← hg_def]
    have hint : Integrable (fun x => u x * g x) μ :=
      Integrable.mono' hgint.abs (hu.mul hg).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          calc |u x| * |g x| ≤ 1 * |g x| := by gcongr; exact abs_le.2 (hu1 x)
            _ = |g x| := one_mul _)
    calc |∫ x, u x * g x ∂μ|
        ≤ ∫ x, |u x * g x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |g x| ∂μ := by
          refine integral_mono hint.abs hgint.abs fun x => ?_
          rw [abs_mul]
          calc |u x| * |g x| ≤ 1 * |g x| := by gcongr; exact abs_le.2 (hu1 x)
            _ = |g x| := one_mul _
      _ = ∫ x, (if 0 ≤ g x then (1 : ℝ) else -1) * g x ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          by_cases hx : 0 ≤ g x
          · simp [hx, abs_of_nonneg hx]
          · simp [hx, abs_of_neg (lt_of_not_ge hx)]

omit [MeasurableSpace Ω] in
private theorem mem_Icc_of_pm {w : Ω → ℝ} (hw : ∀ x, w x = 1 ∨ w x = -1) (x : Ω) :
    w x ∈ Icc (-1 : ℝ) 1 := by
  rcases hw x with h | h <;> rw [h] <;> constructor <;> norm_num

/-- A `±1`-valued measurable function is the indicator of a measurable set minus the indicator of
its complement. -/
private theorem exists_indicator_sub_of_pm {u : Ω → ℝ} (hu : Measurable u)
    (hu' : ∀ x, u x = 1 ∨ u x = -1) :
    ∃ S : Set Ω, MeasurableSet S ∧ u = S.indicator 1 - Sᶜ.indicator 1 := by
  refine ⟨u ⁻¹' {1}, hu (measurableSet_singleton 1), ?_⟩
  funext x
  by_cases hx : u x = 1
  · simp [Set.mem_preimage, hx]
  · have hxS : x ∉ u ⁻¹' {1} := by simpa using hx
    have hx' : u x = -1 := (hu' x).resolve_left hx
    simp [hxS, hx']

/-- The four-rectangle bound: a pairing of `±1`-valued test functions splits into the four
rectangles cut out by the two sets, each bounded by the cut norm. -/
private theorem abs_testIntegral_le_four_mul_cutNorm_of_pm (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu' : ∀ x, u x = 1 ∨ u x = -1) (hv' : ∀ y, v y = 1 ∨ v y = -1) :
    |K.testIntegral μ u v| ≤ 4 * cutNorm μ K := by
  obtain ⟨S, hS, hu_eq⟩ := exists_indicator_sub_of_pm hu hu'
  obtain ⟨T, hT, hv_eq⟩ := exists_indicator_sub_of_pm hv hv'
  have hind : ∀ A : Set Ω, MeasurableSet A → Measurable (A.indicator (1 : Ω → ℝ)) :=
    fun _ hA => measurable_one.indicator hA
  have hmem : ∀ (A : Set Ω) (x : Ω), A.indicator (1 : Ω → ℝ) x ∈ Icc (-1 : ℝ) 1 := by
    intro A x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hv_eq, K.testIntegral_sub_right μ
      (K.integrable_testIntegrand μ hu (hind T hT) (mem_Icc_of_pm hu') (hmem T))
      (K.integrable_testIntegrand μ hu (hind Tᶜ hT.compl) (mem_Icc_of_pm hu') (hmem Tᶜ)),
    hu_eq,
    K.testIntegral_sub_left μ
      (K.integrable_testIntegrand μ (hind S hS) (hind T hT) (hmem S) (hmem T))
      (K.integrable_testIntegrand μ (hind Sᶜ hS.compl) (hind T hT) (hmem Sᶜ) (hmem T)),
    K.testIntegral_sub_left μ
      (K.integrable_testIntegrand μ (hind S hS) (hind Tᶜ hT.compl) (hmem S) (hmem Tᶜ))
      (K.integrable_testIntegrand μ (hind Sᶜ hS.compl) (hind Tᶜ hT.compl) (hmem Sᶜ) (hmem Tᶜ)),
    K.testIntegral_indicator_one μ hS hT, K.testIntegral_indicator_one μ hS.compl hT,
    K.testIntegral_indicator_one μ hS hT.compl,
    K.testIntegral_indicator_one μ hS.compl hT.compl]
  obtain ⟨l1, r1⟩ := abs_le.1 (abs_rectIntegral_le_cutNorm μ K hS hT)
  obtain ⟨l2, r2⟩ := abs_le.1 (abs_rectIntegral_le_cutNorm μ K hS.compl hT)
  obtain ⟨l3, r3⟩ := abs_le.1 (abs_rectIntegral_le_cutNorm μ K hS hT.compl)
  obtain ⟨l4, r4⟩ := abs_le.1 (abs_rectIntegral_le_cutNorm μ K hS.compl hT.compl)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Upper side of the factor sandwich.** Relaxing indicators to `[-1,1]`-valued test functions
increases the cut norm by at most a factor of `4`. -/
theorem cutNormSigned_le_four_mul_cutNorm (K : SymmKernel Ω μ) :
    cutNormSigned μ K ≤ 4 * cutNorm μ K := by
  refine cutNormSigned_le μ fun u v hu hv hu1 hv1 => ?_
  obtain ⟨w, hw, hw', hle⟩ := exists_pm_one_left μ K hu hv hu1 hv1
  obtain ⟨z, hz, hz', hle2⟩ :=
    exists_pm_one_left μ K hv hw hv1 (mem_Icc_of_pm hw')
  have e1 : K.testIntegral μ w v = K.testIntegral μ v w := K.testIntegral_comm μ w v
  have e2 : K.testIntegral μ z w = K.testIntegral μ w z := K.testIntegral_comm μ z w
  have h4 : |K.testIntegral μ w z| ≤ 4 * cutNorm μ K :=
    abs_testIntegral_le_four_mul_cutNorm_of_pm μ K hw hz hw' hz'
  calc |K.testIntegral μ u v|
      ≤ K.testIntegral μ w v := hle
    _ = K.testIntegral μ v w := e1
    _ ≤ |K.testIntegral μ v w| := le_abs_self _
    _ ≤ K.testIntegral μ z w := hle2
    _ = K.testIntegral μ w z := e2
    _ ≤ |K.testIntegral μ w z| := le_abs_self _
    _ ≤ 4 * cutNorm μ K := h4

end DenseGraphLimits

end TauCeti
