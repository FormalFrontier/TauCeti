module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Pointwise products of `L²` functions on a finite product measure

For a finite family of σ-finite measures `μ i` and `L²(μ i)` functions `f i`, the pointwise product
`x ↦ ∏ i, f i (x i)` belongs to `L²(Measure.pi μ)`, and the assignment factors the inner product as
a tensor. This is the `Fintype`-indexed analogue of `TauCeti.L2prodMul`, and Part B3/D of the
`OrthogonalL2Bases` roadmap.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]

/-- The pointwise product `x ↦ ∏ i, f i (x i)` of `L²` functions is `L²` for the product measure. -/
theorem memLp_pi_prod {f : ∀ i, α i → 𝕜} (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x : ∀ i, α i => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hmeas : AEStronglyMeasurable (fun x : ∀ i, α i => ∏ i, f i (x i)) (Measure.pi μ) :=
    Finset.aestronglyMeasurable_fun_prod (f := fun i (x : ∀ j, α j) => f i (x i)) _ fun i _ =>
      (hf i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (Integrable.fintype_prod_dep
    (fun i => (memLp_two_iff_integrable_sq_norm (hf i).1).1 (hf i))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_prod, Finset.prod_pow]

/-- The pointwise product `x ↦ ∏ i, F i (x i)` of a family of `L²(μ i)` vectors, as a vector of
`L²(Measure.pi μ)`. -/
noncomputable def L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : Lp 𝕜 2 (Measure.pi μ) :=
  (memLp_pi_prod (fun i => Lp.memLp (F i))).toLp _

/-- The `Lp` representative of `L2piMul F` is the pointwise product of the representatives. -/
theorem coeFn_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) :
    ⇑(L2piMul F) =ᵐ[Measure.pi μ] fun x : ∀ i, α i => ∏ i, F i (x i) :=
  MemLp.coeFn_toLp _

/-- **The tensor inner-product identity, `Fintype`-indexed.** The inner product of two pointwise
products factors as the product of the coordinatewise inner products. -/
@[simp]
theorem inner_L2piMul (F G : ∀ i, Lp 𝕜 2 (μ i)) :
    inner 𝕜 (L2piMul F) (L2piMul G) = ∏ i, inner 𝕜 (F i) (G i) := by
  rw [L2.inner_def]
  calc
    ∫ x, inner 𝕜 (L2piMul F x) (L2piMul G x) ∂(Measure.pi μ)
        = ∫ x : ∀ i, α i, ∏ i, inner 𝕜 (F i (x i)) (G i (x i)) ∂(Measure.pi μ) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2piMul F, coeFn_L2piMul G] with x hF hG
          rw [hF, hG]
          simp only [RCLike.inner_apply', map_prod, Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, inner 𝕜 (F i x) (G i x) ∂(μ i) :=
          integral_fintype_prod_eq_prod (fun i x => inner 𝕜 (F i x) (G i x))
    _ = ∏ i, inner 𝕜 (F i) (G i) :=
          Finset.prod_congr rfl fun i _ => (L2.inner_def _ _).symm

/-- **Orthonormality of the tensor family, `Fintype`-indexed.** Coordinatewise orthonormal families
multiply to an orthonormal family of `L²(Measure.pi μ)`, indexed by the dependent function type. -/
theorem orthonormal_L2piMul {κ : ι → Type*} {b : ∀ i, κ i → Lp 𝕜 2 (μ i)}
    (hb : ∀ i, Orthonormal 𝕜 (b i)) :
    Orthonormal 𝕜 (fun k : ∀ i, κ i => L2piMul (fun i => b i (k i))) := by
  classical
  simp_rw [orthonormal_iff_ite] at hb ⊢
  intro k l
  rw [inner_L2piMul]
  simp_rw [hb]
  by_cases hkl : k = l
  · subst hkl
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hkl
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), if_neg hkl]

end TauCeti
