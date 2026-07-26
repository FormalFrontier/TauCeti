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

/-- The tensor construction is norm-multiplicative. -/
@[simp]
theorem norm_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : ‖L2piMul F‖ = ∏ i, ‖F i‖ := by
  have h : ((‖L2piMul F‖ : ℝ) : 𝕜) ^ 2 = ∏ i, ((‖F i‖ : ℝ) : 𝕜) ^ 2 := by
    simpa only [inner_self_eq_norm_sq_to_K] using inner_L2piMul F F
  have h3 : ‖L2piMul F‖ ^ 2 = (∏ i, ‖F i‖) ^ 2 := by
    have hc : ((‖L2piMul F‖ ^ 2 : ℝ) : 𝕜) = (((∏ i, ‖F i‖) ^ 2 : ℝ) : 𝕜) := by
      push_cast
      rw [h, ← Finset.prod_pow]
    exact_mod_cast hc
  calc ‖L2piMul F‖ = Real.sqrt (‖L2piMul F‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((∏ i, ‖F i‖) ^ 2) := by rw [h3]
    _ = ∏ i, ‖F i‖ := Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _)

section Slot

variable [DecidableEq ι]

/-- Splitting off the `j`-th coordinate of a tensor. -/
theorem coeFn_L2piMul_update (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    ⇑(L2piMul (Function.update F j v)) =ᵐ[Measure.pi μ]
      fun x : ∀ i, α i => v (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  filter_upwards [coeFn_L2piMul (Function.update F j v)] with x hx
  rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The tensor is additive in the `j`-th coordinate. -/
theorem L2piMul_update_add (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v w : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (v + w))
      = L2piMul (Function.update F j v) + L2piMul (Function.update F j w) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (v + w), coeFn_L2piMul_update j F v,
    coeFn_L2piMul_update j F w,
    Lp.coeFn_add (L2piMul (Function.update F j v)) (L2piMul (Function.update F j w)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_add v w)]
    with x h h1 h2 hadd hv
  rw [h, hadd, Pi.add_apply, h1, h2, hv, Pi.add_apply, add_mul]

/-- The tensor is homogeneous in the `j`-th coordinate. -/
theorem L2piMul_update_smul (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (c : 𝕜) (v : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (c • v)) = c • L2piMul (Function.update F j v) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (c • v), coeFn_L2piMul_update j F v,
    Lp.coeFn_smul c (L2piMul (Function.update F j v)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_smul c v)]
    with x h h1 hsmul hv
  rw [h, hsmul, Pi.smul_apply, h1, hv, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- Tensoring with all coordinates but `j` held fixed, as a continuous linear map. -/
@[expose] noncomputable def L2piMulSlot (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) :
    Lp 𝕜 2 (μ j) →L[𝕜] Lp 𝕜 2 (Measure.pi μ) :=
  LinearMap.mkContinuous
    { toFun := fun v => L2piMul (Function.update F j v)
      map_add' := L2piMul_update_add j F
      map_smul' := fun c v => L2piMul_update_smul j F c v }
    (∏ i ∈ Finset.univ.erase j, ‖F i‖) fun v => by
      change ‖L2piMul (Function.update F j v)‖ ≤ (∏ i ∈ Finset.univ.erase j, ‖F i‖) * ‖v‖
      rw [norm_L2piMul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self,
        mul_comm]
      refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (norm_nonneg v)
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- `L2piMulSlot` applies as the tensor. -/
@[simp]
theorem L2piMulSlot_apply (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    L2piMulSlot j F v = L2piMul (Function.update F j v) := rfl

end Slot

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from
coordinatewise Hilbert bases is orthogonal to *every* elementary tensor. The coordinates are
generalized one at a time, by expanding a single slot along its basis and pushing the sum through
the continuous linear map `L2piMulSlot`. -/
theorem inner_L2piMul_eq_zero_of_forall_basis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ k : ∀ i, κ i, inner 𝕜 h (L2piMul (fun i => b i (k i))) = 0)
    (F : ∀ i, Lp 𝕜 2 (μ i)) : inner 𝕜 h (L2piMul F) = 0 := by
  classical
  have key : ∀ S : Finset ι, ∀ F : ∀ i, Lp 𝕜 2 (μ i),
      (∀ i, i ∉ S → ∃ c, F i = b i c) → inner 𝕜 h (L2piMul F) = 0 := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro F hF
        choose k hk using fun i => hF i (by simp)
        have hFk : F = fun i => b i (k i) := funext hk
        rw [hFk]
        exact hz k
    | @insert j S hj ih =>
        intro F hF
        have hsum := ((b j).hasSum_repr (F j)).mapL ((innerSL 𝕜 h).comp (L2piMulSlot j F))
        have hzero : HasSum (fun _ : κ j => (0 : 𝕜))
            ((innerSL 𝕜 h).comp (L2piMulSlot j F) (F j)) := by
          refine hsum.congr_fun fun c => ?_
          have hupd : inner 𝕜 h (L2piMul (Function.update F j (b j c))) = 0 := by
            refine ih _ fun i hi => ?_
            by_cases hij : i = j
            · subst hij
              exact ⟨c, by rw [Function.update_self]⟩
            · rw [Function.update_of_ne hij]
              exact hF i fun hmem => (Finset.mem_insert.1 hmem).elim hij hi
          simp [hupd]
        have hfin := (hasSum_zero.unique hzero).symm
        simpa [Function.update_eq_self] using hfin
  exact key Finset.univ F fun i hi => absurd (Finset.mem_univ i) hi

end TauCeti
