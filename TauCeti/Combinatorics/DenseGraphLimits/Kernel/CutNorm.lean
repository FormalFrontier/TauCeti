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
* `abs_testIntegral_le_cutNorm` bounds every `[0,1]`-test integral by the cut norm itself, with no
  loss of constant — the form the counting lemma consumes, where the weights read off the other
  edges of a graph are `[0,1]`-valued.
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

/-- Multiplying a partial pairing by a measurable `[-1,1]`-valued function preserves
integrability. -/
private theorem integrable_mul_partialIntegral [IsFiniteMeasure μ] (K : SymmKernel Ω μ)
    {v w : Ω → ℝ} (hv : Measurable v) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1)
    (hw : Measurable w) (hw1 : ∀ x, w x ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun x => w x * K.partialIntegral μ v x) μ :=
  (K.integrable_partialIntegral μ hv hv1).bdd_mul hw.aestronglyMeasurable
    (ae_of_all _ fun x => abs_le.2 (hw1 x))

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

omit [MeasurableSpace Ω] in
/-- An indicator of the constant-one function takes values in `[-1,1]`. -/
private theorem indicator_one_mem_Icc_neg_one_one (A : Set Ω) (x : Ω) :
    A.indicator (1 : Ω → ℝ) x ∈ Icc (-1 : ℝ) 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

/-- The extremal step for `[0,1]`-valued test functions.  The pairing is affine in the left test
function, so it lies between the pairings against the indicator of the set where the partial
pairing is nonnegative and the indicator of the complement; one of those two indicators therefore
does at least as well in absolute value. -/
private theorem exists_indicator_left_of_mem_Icc (K : SymmKernel Ω μ)
    {u v : Ω → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (0 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (-1 : ℝ) 1) :
    ∃ S : Set Ω, MeasurableSet S ∧
      |K.testIntegral μ u v| ≤ |K.testIntegral μ (S.indicator 1) v| := by
  classical
  have hu1' : ∀ x, u x ∈ Icc (-1 : ℝ) 1 := fun x => ⟨by linarith [(hu1 x).1], (hu1 x).2⟩
  set g := K.partialIntegral μ v with hgdef
  have hgm : Measurable g := K.measurable_partialIntegral μ hv
  set S : Set Ω := {x | 0 ≤ g x} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_const hgm
  have hind : ∀ A : Set Ω, MeasurableSet A → Measurable (A.indicator (1 : Ω → ℝ)) :=
    fun _ hA => measurable_one.indicator hA
  have hrepr : ∀ w : Ω → ℝ, Measurable w → (∀ x, w x ∈ Icc (-1 : ℝ) 1) →
      K.testIntegral μ w v = ∫ x, w x * g x ∂μ := fun w hw hw1 =>
    K.testIntegral_eq_integral_partialIntegral μ (K.integrable_testIntegrand μ hw hv hw1 hv1)
  have hgnonpos : ∀ x ∉ S, g x ≤ 0 := fun x hx =>
    le_of_lt (lt_of_not_ge (by simpa [hSdef] using hx))
  have hlow : ∀ x, Sᶜ.indicator (1 : Ω → ℝ) x * g x ≤ u x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_notMem (by simpa using hx), zero_mul]
      exact mul_nonneg (hu1 x).1 hx
    · have hgx := hgnonpos x hx
      rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply]
      exact mul_le_mul_of_nonpos_right (hu1 x).2 hgx
  have hhigh : ∀ x, u x * g x ≤ S.indicator (1 : Ω → ℝ) x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      exact mul_le_mul_of_nonneg_right (hu1 x).2 hx
    · have hgx := hgnonpos x hx
      rw [Set.indicator_of_notMem hx, zero_mul]
      nlinarith [(hu1 x).1, hgx]
  set IA := ∫ x, S.indicator (1 : Ω → ℝ) x * g x ∂μ with hIA
  set IB := ∫ x, Sᶜ.indicator (1 : Ω → ℝ) x * g x ∂μ with hIB
  set IC := ∫ x, u x * g x ∂μ with hIC
  have hBC : IB ≤ IC :=
    integral_mono
      (K.integrable_mul_partialIntegral μ hv hv1 (hind _ hS.compl)
        (indicator_one_mem_Icc_neg_one_one _))
      (K.integrable_mul_partialIntegral μ hv hv1 hu hu1') hlow
  have hCA : IC ≤ IA :=
    integral_mono (K.integrable_mul_partialIntegral μ hv hv1 hu hu1')
      (K.integrable_mul_partialIntegral μ hv hv1 (hind _ hS)
        (indicator_one_mem_Icc_neg_one_one _)) hhigh
  have hA0 : 0 ≤ IA := by
    refine integral_nonneg fun x => ?_
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]; exact hx
    · rw [Set.indicator_of_notMem hx, zero_mul]
  have hB0 : IB ≤ 0 := by
    refine integral_nonpos fun x => ?_
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_notMem (by simpa using hx), zero_mul]
    · have hgx := hgnonpos x hx
      rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply, one_mul]
      exact hgx
  rcases le_total (-IB) IA with h | h
  · refine ⟨S, hS, ?_⟩
    rw [hrepr u hu hu1', hrepr _ (hind _ hS) (indicator_one_mem_Icc_neg_one_one _),
      ← hIC, ← hIA, abs_of_nonneg hA0]
    exact abs_le.2 ⟨by linarith, hCA⟩
  · refine ⟨Sᶜ, hS.compl, ?_⟩
    rw [hrepr u hu hu1',
      hrepr _ (hind _ hS.compl) (indicator_one_mem_Icc_neg_one_one _), ← hIC, ← hIB,
      abs_of_nonpos hB0]
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Every `[0,1]`-test integral is bounded by the cut norm.**  The pairing is affine in each test
function, so replacing a `[0,1]`-valued test function by a suitable indicator only increases the
absolute pairing; doing so on both sides lands on a measurable rectangle.  Unlike the
`[-1,1]`-valued case (`cutNormSigned_le_four_mul_cutNorm`) there is no factor of `4`, which is what
makes this the form the counting lemma consumes. -/
theorem abs_testIntegral_le_cutNorm (K : SymmKernel Ω μ) {u v : Ω → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ x, u x ∈ Icc (0 : ℝ) 1) (hv1 : ∀ y, v y ∈ Icc (0 : ℝ) 1) :
    |K.testIntegral μ u v| ≤ cutNorm μ K := by
  have hv1' : ∀ y, v y ∈ Icc (-1 : ℝ) 1 := fun y => ⟨by linarith [(hv1 y).1], (hv1 y).2⟩
  obtain ⟨S, hS, hSle⟩ := exists_indicator_left_of_mem_Icc μ K hu hv hu1 hv1'
  rw [K.testIntegral_comm μ (S.indicator 1) v] at hSle
  obtain ⟨T, hT, hTle⟩ :=
    exists_indicator_left_of_mem_Icc μ K hv (measurable_one.indicator hS) hv1
      (indicator_one_mem_Icc_neg_one_one _)
  calc |K.testIntegral μ u v|
      ≤ |K.testIntegral μ v (S.indicator 1)| := hSle
    _ ≤ |K.testIntegral μ (T.indicator 1) (S.indicator 1)| := hTle
    _ = |K.rectIntegral μ T S| := by rw [K.testIntegral_indicator_one μ hT hS]
    _ ≤ cutNorm μ K := abs_rectIntegral_le_cutNorm μ K hT hS

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
    (measurable_one.indicator hT) (indicator_one_mem_Icc_neg_one_one _)
      (indicator_one_mem_Icc_neg_one_one _)

/-- **Upper side of the factor sandwich.** Relaxing indicators to `[-1,1]`-valued test functions
increases the cut norm by at most a factor of `4`. -/
theorem cutNormSigned_le_four_mul_cutNorm (K : SymmKernel Ω μ) :
    cutNormSigned μ K ≤ 4 * cutNorm μ K := by
  refine cutNormSigned_le μ fun u v hu hv hu1 hv1 => ?_
  let up := fun x => max (u x) 0
  let un := fun x => max (-u x) 0
  let vp := fun x => max (v x) 0
  let vn := fun x => max (-v x) 0
  have hupm : Measurable up := hu.max measurable_const
  have hunm : Measurable un := hu.neg.max measurable_const
  have hvpm : Measurable vp := hv.max measurable_const
  have hvnm : Measurable vn := hv.neg.max measurable_const
  have hup1 : ∀ x, up x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_right _ _, max_le (hu1 x).2 zero_le_one⟩
  have hun1 : ∀ x, un x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_right _ _, max_le (by linarith [(hu1 x).1]) zero_le_one⟩
  have hvp1 : ∀ x, vp x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_right _ _, max_le (hv1 x).2 zero_le_one⟩
  have hvn1 : ∀ x, vn x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_right _ _, max_le (by linarith [(hv1 x).1]) zero_le_one⟩
  have hup1' : ∀ x, up x ∈ Icc (-1 : ℝ) 1 := fun x =>
    ⟨by linarith [(hup1 x).1], (hup1 x).2⟩
  have hun1' : ∀ x, un x ∈ Icc (-1 : ℝ) 1 := fun x =>
    ⟨by linarith [(hun1 x).1], (hun1 x).2⟩
  have hvp1' : ∀ x, vp x ∈ Icc (-1 : ℝ) 1 := fun x =>
    ⟨by linarith [(hvp1 x).1], (hvp1 x).2⟩
  have hvn1' : ∀ x, vn x ∈ Icc (-1 : ℝ) 1 := fun x =>
    ⟨by linarith [(hvn1 x).1], (hvn1 x).2⟩
  have hu_eq : u = up - un := by
    funext x
    exact (max_zero_sub_max_neg_zero_eq_self (u x)).symm
  have hv_eq : v = vp - vn := by
    funext x
    exact (max_zero_sub_max_neg_zero_eq_self (v x)).symm
  have hu_sub1 : ∀ x, (up - un) x ∈ Icc (-1 : ℝ) 1 := by
    rw [← hu_eq]
    exact hu1
  have hpp := abs_testIntegral_le_cutNorm μ K hupm hvpm hup1 hvp1
  have hmp := abs_testIntegral_le_cutNorm μ K hunm hvpm hun1 hvp1
  have hpm := abs_testIntegral_le_cutNorm μ K hupm hvnm hup1 hvn1
  have hmm := abs_testIntegral_le_cutNorm μ K hunm hvnm hun1 hvn1
  rw [hu_eq, hv_eq,
    K.testIntegral_sub_right μ
      (K.integrable_testIntegrand μ (hupm.sub hunm) hvpm hu_sub1 hvp1')
      (K.integrable_testIntegrand μ (hupm.sub hunm) hvnm hu_sub1 hvn1'),
    K.testIntegral_sub_left μ
      (K.integrable_testIntegrand μ hupm hvpm hup1' hvp1')
      (K.integrable_testIntegrand μ hunm hvpm hun1' hvp1'),
    K.testIntegral_sub_left μ
      (K.integrable_testIntegrand μ hupm hvnm hup1' hvn1')
      (K.integrable_testIntegrand μ hunm hvnm hun1' hvn1')]
  calc
    |K.testIntegral μ up vp - K.testIntegral μ un vp -
        (K.testIntegral μ up vn - K.testIntegral μ un vn)|
        ≤ |K.testIntegral μ up vp - K.testIntegral μ un vp| +
            |K.testIntegral μ up vn - K.testIntegral μ un vn| := abs_sub _ _
    _ ≤ (|K.testIntegral μ up vp| + |K.testIntegral μ un vp|) +
          (|K.testIntegral μ up vn| + |K.testIntegral μ un vn|) :=
      add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ (cutNorm μ K + cutNorm μ K) + (cutNorm μ K + cutNorm μ K) :=
      add_le_add (add_le_add hpp hmp) (add_le_add hpm hmm)
    _ = 4 * cutNorm μ K := by ring

end DenseGraphLimits

end TauCeti
