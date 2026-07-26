module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Integral.Prod

/-!
# Pointwise products of `L²` functions on a product measure

For an `L²(μ)` function `f` and an `L²(ν)` function `g` on s-finite measures, the pointwise
product `(x, y) ↦ f x * g y` belongs to `L²(μ ⊗ ν)`, and the assignment factors the inner product
as a tensor:
`⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫`.
Consequently the products of two orthonormal families are an orthonormal family of `L²(μ ⊗ ν)`.

This is Part B3 of the `OrthogonalL2Bases` roadmap (the product `L²`-basis milestone), in both
halves: the elementary tensors are orthonormal *and* they span, so for σ-finite factors the
products of two Hilbert bases form a Hilbert basis `TauCeti.prodHilbertBasis` of `L²(μ ⊗ ν)`.
It is a genuine gap in Mathlib, which provides only `MemLp.comp_fst`/`MemLp.comp_snd`
(single-factor membership, and only for finite measures) and the finite-dimensional
`OrthonormalBasis.tensorProduct`; there is no `L²(μ.prod ν)` product API.

The completeness half avoids any slicing argument, and with it any countability assumption on the
index types. It runs in three moves:

1. `TauCeti.inner_L2prodMul_eq_zero_of_forall_basis` — orthogonality to the *basis* tensors upgrades
   to orthogonality to *every* elementary tensor. This is pure Hilbert-space geometry: expand a
   vector along a basis and push the sum through the continuous linear map
   `TauCeti.L2prodMulL`.
2. `TauCeti.setIntegral_prod_eq_zero_of_forall_inner` — testing against indicators, since
   `1ₐ ⊗ 1_b` is the indicator of the rectangle `a ×ˢ b`.
3. `TauCeti.setIntegral_eq_zero_of_forall_prod` — the Dynkin (π-λ) step, upgrading rectangles to
   arbitrary measurable sets. It is applied inside a finite box; the monotone exhaustion of the
   space by the boxes `spanningSets μ n ×ˢ spanningSets ν n` is then done in
   `TauCeti.setIntegral_eq_zero_of_forall_inner`.

The scalars are generic over `[RCLike 𝕜]`, so a single construction serves both the real and
complex `L²` spaces.

## Main definitions

* `TauCeti.L2prodMul` — the pointwise product `(x, y) ↦ f x * g y` of `F : L²(μ)` and `G : L²(ν)`
  as a vector of `L²(μ ⊗ ν)`.
* `TauCeti.prodHilbertBasis` — the Hilbert basis of `L²(μ ⊗ ν)` built from Hilbert bases of the
  factors.

## Main statements

* `TauCeti.memLp_mul_prod` — the pointwise product of `L²` functions is `L²` for the product
  measure.
* `TauCeti.inner_L2prodMul` — the inner product of two tensors factors as a product of inner
  products.
* `TauCeti.orthonormal_L2prodMul` — products of orthonormal families are orthonormal.
* `TauCeti.orthogonal_span_range_L2prodMul_eq_bot` — the completeness half: the basis tensors have
  trivial orthogonal complement.
* `TauCeti.prodHilbertBasis_apply` — the `(i, j)` basis vector is the tensor `b₁ i ⊗ b₂ j`;
  `TauCeti.coeFn_prodHilbertBasis` gives its a.e. representative.
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

/-- The tensor is additive in its first argument. -/
@[simp]
theorem L2prodMul_add_left [SFinite μ] [SFinite ν] (F₁ F₂ : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul (F₁ + F₂) G = L2prodMul F₁ G + L2prodMul F₂ G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul (F₁ + F₂) G, coeFn_L2prodMul F₁ G, coeFn_L2prodMul F₂ G,
    Lp.coeFn_add (L2prodMul F₁ G) (L2prodMul F₂ G),
    ae_of_ae_fst (β := β) (ν := ν) (Lp.coeFn_add F₁ F₂)] with q h h1 h2 hadd hf
  rw [h, hadd, Pi.add_apply, h1, h2, hf, Pi.add_apply, add_mul]

/-- The tensor is additive in its second argument. -/
@[simp]
theorem L2prodMul_add_right [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    L2prodMul F (G₁ + G₂) = L2prodMul F G₁ + L2prodMul F G₂ := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul F (G₁ + G₂), coeFn_L2prodMul F G₁, coeFn_L2prodMul F G₂,
    Lp.coeFn_add (L2prodMul F G₁) (L2prodMul F G₂),
    ae_of_ae_snd (α := α) (μ := μ) (Lp.coeFn_add G₁ G₂)] with q h h1 h2 hadd hg
  rw [h, hadd, Pi.add_apply, h1, h2, hg, Pi.add_apply, mul_add]

/-- The tensor is homogeneous in its first argument. -/
@[simp]
theorem L2prodMul_smul_left [SFinite μ] [SFinite ν] (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul (c • F) G = c • L2prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul (c • F) G, coeFn_L2prodMul F G,
    Lp.coeFn_smul c (L2prodMul F G),
    ae_of_ae_fst (β := β) (ν := ν) (Lp.coeFn_smul c F)] with q h h1 hsmul hf
  rw [h, hsmul, Pi.smul_apply, h1, hf, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The tensor is homogeneous in its second argument. -/
@[simp]
theorem L2prodMul_smul_right [SFinite μ] [SFinite ν] (c : 𝕜) (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMul F (c • G) = c • L2prodMul F G := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul F (c • G), coeFn_L2prodMul F G,
    Lp.coeFn_smul c (L2prodMul F G),
    ae_of_ae_snd (α := α) (μ := μ) (Lp.coeFn_smul c G)] with q h h1 hsmul hg
  rw [h, hsmul, Pi.smul_apply, h1, hg, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- The tensor vanishes when its first argument does. -/
@[simp]
theorem L2prodMul_zero_left [SFinite μ] [SFinite ν] (G : Lp 𝕜 2 ν) :
    L2prodMul (0 : Lp 𝕜 2 μ) G = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul (0 : Lp 𝕜 2 μ) G, Lp.coeFn_zero 𝕜 2 (μ.prod ν),
    ae_of_ae_fst (β := β) (ν := ν) (Lp.coeFn_zero 𝕜 2 μ)] with q h hz hf
  rw [h, hz, hf, Pi.zero_apply, Pi.zero_apply, zero_mul]

/-- The tensor vanishes when its second argument does. -/
@[simp]
theorem L2prodMul_zero_right [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) :
    L2prodMul F (0 : Lp 𝕜 2 ν) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2prodMul F (0 : Lp 𝕜 2 ν), Lp.coeFn_zero 𝕜 2 (μ.prod ν),
    ae_of_ae_snd (α := α) (μ := μ) (Lp.coeFn_zero 𝕜 2 ν)] with q h hz hg
  rw [h, hz, hg, Pi.zero_apply, Pi.zero_apply, mul_zero]

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

/-- **The tensor as a bounded bilinear map.** `L2prodMulL F G = L2prodMul F G`, packaged so that
either operand can be fixed: `L2prodMulL F` fixes the left factor, `L2prodMulL.flip G` the right.
The operator norm bound is `1`, since `norm_L2prodMul` is an equality. -/
noncomputable def L2prodMulL [SFinite μ] [SFinite ν] :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 L2prodMul
      (fun F₁ F₂ G => L2prodMul_add_left F₁ F₂ G)
      (fun c F G => L2prodMul_smul_left c F G)
      (fun F G₁ G₂ => L2prodMul_add_right F G₁ G₂)
      (fun c F G => L2prodMul_smul_right c F G))
    1 fun F G => by simp [norm_L2prodMul]

@[simp]
theorem L2prodMulL_apply [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    L2prodMulL F G = L2prodMul F G :=
  LinearMap.mkContinuous₂_apply _ _ _ _

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from two Hilbert
bases is orthogonal to *every* elementary tensor. This is the countability-free half of the
completeness argument: it is pure Hilbert-space geometry, with no null-set bookkeeping. -/
theorem inner_L2prodMul_eq_zero_of_forall_basis [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν))
    {h : Lp 𝕜 2 (μ.prod ν)} (hz : ∀ i j, inner 𝕜 h (L2prodMul (b₁ i) (b₂ j)) = 0)
    (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) : inner 𝕜 h (L2prodMul F G) = 0 := by
  have step : ∀ i : ι₁, ∀ G' : Lp 𝕜 2 ν, inner 𝕜 h (L2prodMul (b₁ i) G') = 0 := by
    intro i G'
    have hsum := ((b₂.hasSum_repr G').mapL ((innerSL 𝕜 h).comp (L2prodMulL (b₁ i))))
    have hzero : HasSum (fun _ : ι₂ => (0 : 𝕜))
        ((innerSL 𝕜 h).comp (L2prodMulL (b₁ i)) G') := by
      refine hsum.congr_fun fun j => ?_
      simp [hz i j]
    simpa using (hasSum_zero.unique hzero).symm
  have hsum := ((b₁.hasSum_repr F).mapL ((innerSL 𝕜 h).comp (L2prodMulL.flip G)))
  have hzero : HasSum (fun _ : ι₁ => (0 : 𝕜))
      ((innerSL 𝕜 h).comp (L2prodMulL.flip G) F) := by
    refine hsum.congr_fun fun i => ?_
    simp [step i G]
  simpa using (hasSum_zero.unique hzero).symm

/-- The tensor of two indicators is the indicator of the rectangle, so orthogonality to every
elementary tensor makes the integral over every finite-measure rectangle vanish. -/
theorem setIntegral_prod_eq_zero_of_forall_inner [SFinite μ] [SFinite ν]
    {h : Lp 𝕜 2 (μ.prod ν)}
    (hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (L2prodMul F G) h = 0)
    {A : Set α} (hA : MeasurableSet A) (hμA : μ A ≠ ⊤)
    {B : Set β} (hB : MeasurableSet B) (hνB : ν B ≠ ⊤) :
    ∫ p in A ×ˢ B, h p ∂(μ.prod ν) = 0 := by
  set F : Lp 𝕜 2 μ := indicatorConstLp 2 hA hμA (1 : 𝕜) with hFdef
  set G : Lp 𝕜 2 ν := indicatorConstLp 2 hB hνB (1 : 𝕜) with hGdef
  have hFc : ⇑F =ᵐ[μ] A.indicator fun _ => (1 : 𝕜) := indicatorConstLp_coeFn
  have hGc : ⇑G =ᵐ[ν] B.indicator fun _ => (1 : 𝕜) := indicatorConstLp_coeFn
  calc ∫ p in A ×ˢ B, h p ∂(μ.prod ν)
      = ∫ p, (A ×ˢ B).indicator (fun q => h q) p ∂(μ.prod ν) :=
        (integral_indicator (hA.prod hB)).symm
    _ = ∫ p, inner 𝕜 ((L2prodMul F G) p) (h p) ∂(μ.prod ν) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_L2prodMul F G, ae_of_ae_fst (β := β) (ν := ν) hFc,
          ae_of_ae_snd (α := α) (μ := μ) hGc] with p hp hpF hpG
        rw [hp, hpF, hpG]
        by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
          simp [Set.mem_prod, h1, h2]
    _ = inner 𝕜 (L2prodMul F G) h := (L2.inner_def _ _).symm
    _ = 0 := hz F G

/-- **Orthogonality kills every finite-measure set integral.** Exhaust the product space by finite
boxes `spanningSets μ n ×ˢ spanningSets ν n`, run the Dynkin step inside each box, and pass to the
monotone limit. -/
theorem setIntegral_eq_zero_of_forall_inner [SigmaFinite μ] [SigmaFinite ν]
    {h : Lp 𝕜 2 (μ.prod ν)}
    (hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (L2prodMul F G) h = 0)
    (u : Set (α × β)) (hu : MeasurableSet u) (hfin : (μ.prod ν) u < ⊤) :
    ∫ p in u, h p ∂(μ.prod ν) = 0 := by
  have hAm : ∀ n, MeasurableSet (spanningSets μ n) := measurableSet_spanningSets μ
  have hBm : ∀ n, MeasurableSet (spanningSets ν n) := measurableSet_spanningSets ν
  have hboxfin : ∀ n, (μ.prod ν) (spanningSets μ n ×ˢ spanningSets ν n) < ⊤ := by
    intro n
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν n)
  have hbox : ∀ n, ∫ p in u ∩ (spanningSets μ n ×ˢ spanningSets ν n), h p ∂(μ.prod ν) = 0 := by
    intro n
    have hrect : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t →
        ∫ p in s ×ˢ t, h p ∂((μ.prod ν).restrict
          (spanningSets μ n ×ˢ spanningSets ν n)) = 0 := by
      intro s hs t ht
      rw [Measure.restrict_restrict (hs.prod ht), Set.prod_inter_prod]
      exact setIntegral_prod_eq_zero_of_forall_inner hz (hs.inter (hAm n))
        (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_spanningSets_lt_top μ n)).ne
        (ht.inter (hBm n))
        (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_spanningSets_lt_top ν n)).ne
    have hdyn := setIntegral_eq_zero_of_forall_prod
      (integrableOn_Lp_of_measure_ne_top h one_le_two (hboxfin n).ne) hrect u hu
    rwa [Measure.restrict_restrict hu] at hdyn
  have hmono : Monotone fun n => u ∩ (spanningSets μ n ×ˢ spanningSets ν n) := fun m n hmn =>
    Set.inter_subset_inter_right _
      (Set.prod_mono (monotone_spanningSets μ hmn) (monotone_spanningSets ν hmn))
  have hcover : ⋃ n, u ∩ (spanningSets μ n ×ˢ spanningSets ν n) = u := by
    rw [← Set.inter_iUnion]
    have huniv : ⋃ n, (spanningSets μ n ×ˢ spanningSets ν n) = Set.univ := by
      refine Set.eq_univ_of_forall fun p => ?_
      have h1 : p.1 ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
      have h2 : p.2 ∈ ⋃ n, spanningSets ν n := by rw [iUnion_spanningSets]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h2
      exact Set.mem_iUnion.2 ⟨max i j, monotone_spanningSets μ (le_max_left i j) hi,
        monotone_spanningSets ν (le_max_right i j) hj⟩
    rw [huniv, Set.inter_univ]
  have htend := tendsto_setIntegral_of_monotone
    (fun n => hu.inter ((hAm n).prod (hBm n))) hmono
    (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
  rw [hcover] at htend
  simp only [hbox] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- **Completeness of the tensor family.** The elementary tensors built from two Hilbert bases have
trivial orthogonal complement in `L²(μ ⊗ ν)`: a vector orthogonal to all of them is orthogonal to
every elementary tensor, hence integrates to zero on every rectangle, hence on every finite-measure
set, hence vanishes. -/
theorem orthogonal_span_range_L2prodMul_eq_bot [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) :
    (Submodule.span 𝕜
      (Set.range (fun ij : ι₁ × ι₂ => L2prodMul (b₁ ij.1) (b₂ ij.2))))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh => ?_
  rw [Submodule.mem_orthogonal] at hh
  have hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (L2prodMul F G) h = 0 := by
    intro F G
    rw [inner_eq_zero_symm]
    refine inner_L2prodMul_eq_zero_of_forall_basis b₁ b₂ (fun i j => ?_) F G
    rw [inner_eq_zero_symm]
    exact hh _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero h (by norm_num) (by norm_num)
    (fun s _ hs' => integrableOn_Lp_of_measure_ne_top h one_le_two hs'.ne)
    (fun s hs hs' => setIntegral_eq_zero_of_forall_inner hz s hs hs')
  rw [Lp.ext_iff]
  exact hae.trans (Lp.coeFn_zero 𝕜 2 (μ.prod ν)).symm

/-- **The product Hilbert basis.** Pointwise products of two Hilbert bases form a Hilbert basis of
`L²(μ ⊗ ν)`, indexed by the product of the index types. -/
noncomputable def prodHilbertBasis [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) :
    HilbertBasis (ι₁ × ι₂) 𝕜 (Lp 𝕜 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (orthonormal_L2prodMul b₁.orthonormal b₂.orthonormal)
    (orthogonal_span_range_L2prodMul_eq_bot b₁ b₂)

/-- The `(i, j)` vector of `prodHilbertBasis` is the tensor of the `i`-th and `j`-th basis
vectors. -/
@[simp]
theorem prodHilbertBasis_apply [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) (i : ι₁) (j : ι₂) :
    prodHilbertBasis b₁ b₂ (i, j) = L2prodMul (b₁ i) (b₂ j) := by
  rw [prodHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The `(i, j)` vector of `prodHilbertBasis` is a.e. the pointwise product `b₁ i ⊗ b₂ j`. -/
theorem coeFn_prodHilbertBasis [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) (i : ι₁) (j : ι₂) :
    ⇑(prodHilbertBasis b₁ b₂ (i, j)) =ᵐ[μ.prod ν] fun q : α × β => b₁ i q.1 * b₂ j q.2 := by
  rw [prodHilbertBasis_apply]
  exact coeFn_L2prodMul _ _

end TauCeti
