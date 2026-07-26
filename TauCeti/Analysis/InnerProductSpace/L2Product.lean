module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise products of `L²` functions on a product measure

For an `L²(μ)` function `f` and an `L²(ν)` function `g` on s-finite measures, the pointwise
product `(x, y) ↦ f x * g y` belongs to `L²(μ ⊗ ν)`, and the assignment factors the inner product
as a tensor:
`⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫`.
Consequently the products of two orthonormal families are an orthonormal family of `L²(μ ⊗ ν)`.

This is the Fubini orthonormality half of Part B3 of the `OrthogonalL2Bases` roadmap (the product
`L²`-basis milestone): the elementary tensors are orthonormal, and their inner products separate.
It is a genuine gap in Mathlib, which provides only `MemLp.comp_fst`/`MemLp.comp_snd`
(single-factor membership, and only for finite measures) and the finite-dimensional
`OrthonormalBasis.tensorProduct`; there is no `L²(μ.prod ν)` product API. The completeness half —
that these tensors *span* `L²(μ ⊗ ν)`, hence form a Hilbert basis — is left to a separate
construction; this file supplies the orthonormality input it consumes.

The scalars are generic over `[RCLike 𝕜]`, so a single construction serves both the real and
complex `L²` spaces.

## Main definitions

* `TauCeti.L2prodMul` — the pointwise product `(x, y) ↦ f x * g y` of `F : L²(μ)` and `G : L²(ν)`
  as a vector of `L²(μ ⊗ ν)`.

## Main statements

* `TauCeti.memLp_mul_prod` — the pointwise product of `L²` functions is `L²` for the product
  measure.
* `TauCeti.inner_L2prodMul` — the inner product of two tensors factors as a product of inner
  products.
* `TauCeti.orthonormal_L2prodMul` — products of orthonormal families are orthonormal.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 α β : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

/-- The pointwise product `(x, y) ↦ f x * g y` of an `L²(μ)` and an `L²(ν)` function is `L²` for the
product measure `μ ⊗ ν`. -/
theorem memLp_mul_prod [SFinite μ] [SFinite ν] {f : α → 𝕜} {g : β → 𝕜}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
  have hfst : AEStronglyMeasurable (fun p : α × β => f p.1) (μ.prod ν) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun p : α × β => g p.2) (μ.prod ν) :=
    hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmeas : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) := hfst.mul hsnd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg2 : Integrable (fun y => ‖g y‖ ^ 2) ν := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  refine (hf2.mul_prod hg2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul, mul_pow]

/-- The pointwise product `(x, y) ↦ F x * G y` of `F : L²(μ)` and `G : L²(ν)`, as a vector of
`L²(μ ⊗ ν)`. -/
noncomputable def L2prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    Lp 𝕜 2 (μ.prod ν) :=
  (memLp_mul_prod (Lp.memLp F) (Lp.memLp G)).toLp _

/-- The `Lp` representative of `L2prodMul F G` is the pointwise product of the representatives. -/
theorem coeFn_L2prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ⇑(L2prodMul F G) =ᵐ[μ.prod ν] fun p : α × β => F p.1 * G p.2 :=
  MemLp.coeFn_toLp _

/-- An a.e. statement on the first factor transfers to the product measure. -/
theorem ae_of_ae_fst [SFinite μ] [SFinite ν] {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.1 :=
  Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hp

/-- An a.e. statement on the second factor transfers to the product measure. -/
theorem ae_of_ae_snd [SFinite μ] [SFinite ν] {p : β → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.2 :=
  Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hp

theorem L2prodMul_add_left [SFinite μ] [SFinite ν] (F₁ F₂ : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul (F₁ + F₂) G = L2prodMul F₁ G + L2prodMul F₂ G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul (F₁ + F₂) G, coeFn_L2prodMul F₁ G, coeFn_L2prodMul F₂ G,
    Lp.coeFn_add (L2prodMul F₁ G) (L2prodMul F₂ G),
    ae_of_ae_fst (β := β) (ν := ν) (Lp.coeFn_add F₁ F₂)] with q h h1 h2 hadd hf
  rw [h, hadd, Pi.add_apply, h1, h2, hf, Pi.add_apply, add_mul]

theorem L2prodMul_add_right [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    L2prodMul F (G₁ + G₂) = L2prodMul F G₁ + L2prodMul F G₂ := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul F (G₁ + G₂), coeFn_L2prodMul F G₁, coeFn_L2prodMul F G₂,
    Lp.coeFn_add (L2prodMul F G₁) (L2prodMul F G₂),
    ae_of_ae_snd (α := α) (μ := μ) (Lp.coeFn_add G₁ G₂)] with q h h1 h2 hadd hg
  rw [h, hadd, Pi.add_apply, h1, h2, hg, Pi.add_apply, mul_add]

theorem L2prodMul_smul_left [SFinite μ] [SFinite ν] (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul (c • F) G = c • L2prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul (c • F) G, coeFn_L2prodMul F G,
    Lp.coeFn_smul c (L2prodMul F G),
    ae_of_ae_fst (β := β) (ν := ν) (Lp.coeFn_smul c F)] with q h h1 hsmul hf
  rw [h, hsmul, Pi.smul_apply, h1, hf, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem L2prodMul_smul_right [SFinite μ] [SFinite ν] (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul F (c • G) = c • L2prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul F (c • G), coeFn_L2prodMul F G,
    Lp.coeFn_smul c (L2prodMul F G),
    ae_of_ae_snd (α := α) (μ := μ) (Lp.coeFn_smul c G)] with q h h1 hsmul hg
  rw [h, hsmul, Pi.smul_apply, h1, hg, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- **The tensor inner-product identity.** The inner product of two pointwise-product vectors in
`L²(μ ⊗ ν)` factors as the product of the inner products of the factors. -/
@[simp]
theorem inner_L2prodMul [SFinite μ] [SFinite ν] (F₁ F₂ : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    inner 𝕜 (L2prodMul F₁ G₁) (L2prodMul F₂ G₂) = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by
  rw [L2.inner_def]
  calc
    ∫ p, inner 𝕜 (L2prodMul F₁ G₁ p) (L2prodMul F₂ G₂ p) ∂(μ.prod ν)
        = ∫ p : α × β, inner 𝕜 (F₁ p.1 * G₁ p.2) (F₂ p.1 * G₂ p.2) ∂(μ.prod ν) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2prodMul F₁ G₁, coeFn_L2prodMul F₂ G₂] with p hp1 hp2
          rw [hp1, hp2]
    _ = ∫ p : α × β,
          inner 𝕜 (F₁ p.1) (F₂ p.1) * inner 𝕜 (G₁ p.2) (G₂ p.2) ∂(μ.prod ν) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [RCLike.inner_apply', map_mul]
          ring
    _ = (∫ x, inner 𝕜 (F₁ x) (F₂ x) ∂μ) * ∫ y, inner 𝕜 (G₁ y) (G₂ y) ∂ν :=
          integral_prod_mul (fun x => inner 𝕜 (F₁ x) (F₂ x))
            (fun y => inner 𝕜 (G₁ y) (G₂ y))
    _ = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by rw [← L2.inner_def, ← L2.inner_def]

/-- **Orthonormality of the tensor family.** If `b` and `c` are orthonormal families of `L²(μ)` and
`L²(ν)`, their pointwise products form an orthonormal family of `L²(μ ⊗ ν)`, indexed by the product
of index types. -/
theorem orthonormal_L2prodMul [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    {b : ι₁ → Lp 𝕜 2 μ} {c : ι₂ → Lp 𝕜 2 ν}
    (hb : Orthonormal 𝕜 b) (hc : Orthonormal 𝕜 c) :
    Orthonormal 𝕜 (fun ij : ι₁ × ι₂ => L2prodMul (b ij.1) (c ij.2)) := by
  classical
  rw [orthonormal_iff_ite] at hb hc ⊢
  intro ij kl
  rw [inner_L2prodMul, hb, hc]
  by_cases h1 : ij.1 = kl.1 <;> by_cases h2 : ij.2 = kl.2 <;>
    simp [h1, h2, Prod.ext_iff]

/-- The tensor construction is norm-multiplicative. -/
@[simp]
theorem norm_L2prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ‖L2prodMul F G‖ = ‖F‖ * ‖G‖ := by
  have h : ((‖L2prodMul F G‖ : ℝ) : 𝕜) ^ 2 = ((‖F‖ : ℝ) : 𝕜) ^ 2 * ((‖G‖ : ℝ) : 𝕜) ^ 2 := by
    simpa only [inner_self_eq_norm_sq_to_K] using inner_L2prodMul (𝕜 := 𝕜) F F G G
  have h3 : ‖L2prodMul F G‖ ^ 2 = (‖F‖ * ‖G‖) ^ 2 := by
    have hc : ((‖L2prodMul F G‖ ^ 2 : ℝ) : 𝕜) = (((‖F‖ * ‖G‖) ^ 2 : ℝ) : 𝕜) := by
      push_cast
      rw [h]
      ring
    exact_mod_cast hc
  calc ‖L2prodMul F G‖ = Real.sqrt (‖L2prodMul F G‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((‖F‖ * ‖G‖) ^ 2) := by rw [h3]
    _ = ‖F‖ * ‖G‖ := Real.sqrt_sq (by positivity)

/-- Tensoring on the right with a fixed `L²(ν)` vector, as a continuous linear map. -/
@[expose] noncomputable def L2prodMulLeftL [SFinite μ] [SFinite ν] (G : Lp 𝕜 2 ν) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun F => L2prodMul F G
      map_add' := fun F₁ F₂ => L2prodMul_add_left F₁ F₂ G
      map_smul' := fun c F => L2prodMul_smul_left c F G }
    ‖G‖ fun F => by simp [mul_comm]

/-- Tensoring on the left with a fixed `L²(μ)` vector, as a continuous linear map. -/
@[expose] noncomputable def L2prodMulRightL [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) :
    Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun G => L2prodMul F G
      map_add' := fun G₁ G₂ => L2prodMul_add_right F G₁ G₂
      map_smul' := fun c G => L2prodMul_smul_right c F G }
    ‖F‖ fun G => le_of_eq (norm_L2prodMul F G)

@[simp]
theorem L2prodMulLeftL_apply [SFinite μ] [SFinite ν] (G : Lp 𝕜 2 ν) (F : Lp 𝕜 2 μ) :
    L2prodMulLeftL G F = L2prodMul F G := rfl

@[simp]
theorem L2prodMulRightL_apply [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMulRightL F G = L2prodMul F G := rfl

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from two Hilbert
bases is orthogonal to *every* elementary tensor. This is the countability-free half of the
completeness argument: it is pure Hilbert-space geometry, with no null-set bookkeeping. -/
theorem inner_L2prodMul_eq_zero_of_forall_basis [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν))
    {h : Lp 𝕜 2 (μ.prod ν)} (hz : ∀ i j, inner 𝕜 h (L2prodMul (b₁ i) (b₂ j)) = 0)
    (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) : inner 𝕜 h (L2prodMul F G) = 0 := by
  have step : ∀ i : ι₁, ∀ G' : Lp 𝕜 2 ν, inner 𝕜 h (L2prodMul (b₁ i) G') = 0 := by
    intro i G'
    have hsum := ((b₂.hasSum_repr G').mapL ((innerSL 𝕜 h).comp (L2prodMulRightL (b₁ i))))
    have hzero : HasSum (fun _ : ι₂ => (0 : 𝕜))
        ((innerSL 𝕜 h).comp (L2prodMulRightL (b₁ i)) G') := by
      refine hsum.congr_fun fun j => ?_
      simp [hz i j]
    simpa using (hasSum_zero.unique hzero).symm
  have hsum := ((b₁.hasSum_repr F).mapL ((innerSL 𝕜 h).comp (L2prodMulLeftL G)))
  have hzero : HasSum (fun _ : ι₁ => (0 : 𝕜))
      ((innerSL 𝕜 h).comp (L2prodMulLeftL G) F) := by
    refine hsum.congr_fun fun i => ?_
    simp [step i G]
  simpa using (hasSum_zero.unique hzero).symm

/-- **Completeness of the tensor family.** The elementary tensors built from two Hilbert bases have
trivial orthogonal complement in `L²(μ ⊗ ν)`. -/
theorem orthogonal_span_range_L2prodMul_eq_bot [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) :
    (Submodule.span 𝕜
      (Set.range (fun ij : ι₁ × ι₂ => L2prodMul (b₁ ij.1) (b₂ ij.2))))ᗮ = ⊥ := by
  sorry

/-- **The product Hilbert basis.** Pointwise products of two Hilbert bases form a Hilbert basis of
`L²(μ ⊗ ν)`, indexed by the product of the index types. -/
noncomputable def prodHilbertBasis [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) :
    HilbertBasis (ι₁ × ι₂) 𝕜 (Lp 𝕜 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (orthonormal_L2prodMul b₁.orthonormal b₂.orthonormal)
    (orthogonal_span_range_L2prodMul_eq_bot b₁ b₂)

/-- The `(i, j)` vector of `prodHilbertBasis` is a.e. the pointwise product `b₁ i ⊗ b₂ j`. -/
theorem coeFn_prodHilbertBasis [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) (i : ι₁) (j : ι₂) :
    ⇑(prodHilbertBasis b₁ b₂ (i, j)) =ᵐ[μ.prod ν] fun q : α × β => b₁ i q.1 * b₂ j q.2 := by
  rw [prodHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact coeFn_L2prodMul _ _

end TauCeti
