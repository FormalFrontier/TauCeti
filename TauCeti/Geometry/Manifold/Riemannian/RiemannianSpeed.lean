/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Riemannian speed and path length

This file provides the pointwise Riemannian speed of a real-parameterized
curve and connects its ordinary real integral to Mathlib's canonical
`Manifold.pathELength`. It also records continuity under local `C^1`
regularity and the chain rule for real reparametrizations.

The model with corners is an explicit argument throughout, matching the
argument order of `Manifold.pathELength`.
-/

public section

open Bundle Filter Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti.Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The pointwise Riemannian speed of a real-parameterized curve. -/
def riemannianSpeed (gamma : ℝ → M) (t : ℝ) : ℝ :=
  ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖

/-- The definition equation for Riemannian speed. -/
@[simp]
theorem riemannianSpeed_apply (gamma : ℝ → M) (t : ℝ) :
    riemannianSpeed I gamma t = ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖ :=
  by simp only [riemannianSpeed]

/-- Riemannian speed is nonnegative. -/
@[simp]
theorem riemannianSpeed_nonneg (gamma : ℝ → M) (t : ℝ) :
    0 ≤ ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖ := norm_nonneg _

/-- A curve that is not differentiable at a point has zero Riemannian speed there. -/
theorem riemannianSpeed_eq_zero_of_not_mdifferentiableAt
    (gamma : ℝ → M) (t : ℝ) (h : ¬MDiffAt gamma t) :
    riemannianSpeed I gamma t = 0 := by
  rw [riemannianSpeed_apply, mfderiv_zero_of_not_mdifferentiableAt h]
  simp

/-- Riemannian speed obeys the chain rule for a differentiable real
reparametrization. -/
theorem riemannianSpeed_comp (gamma : ℝ → M) (f : ℝ → ℝ) (t : ℝ)
    (hgamma : MDiffAt gamma (f t)) (hf : DifferentiableAt ℝ f t) :
    riemannianSpeed I (gamma ∘ f) t =
      |deriv f t| * riemannianSpeed I gamma (f t) := by
  rw [riemannianSpeed_apply, riemannianSpeed_apply,
    mfderiv_comp_apply t hgamma hf.mdifferentiableAt]
  have hmf :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f t
          (1 : TangentSpace 𝓘(ℝ, ℝ) t) =
        deriv f t • (1 : TangentSpace 𝓘(ℝ, ℝ) (f t)) := by
    -- In the one-dimensional model, both tangent spaces reduce to `ℝ`.
    apply (NormedSpace.fromTangentSpace (f t)).injective
    rw [mfderiv_eq_fderiv]
    -- `mfderiv_eq_fderiv` leaves the derivative viewed through the
    -- definitional identification of real tangent spaces with `ℝ`. No public
    -- rewriting lemma exposes that application, so normalize this scalar goal
    -- before using the ordinary derivative API.
    change (fderiv ℝ f t) (1 : ℝ) = deriv f t * 1
    rw [fderiv_apply_one_eq_deriv, mul_one]
  rw [hmf, map_smul, norm_smul, Real.norm_eq_abs]

variable [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The speed is continuous on a set where the curve is `C^1`, provided the
curve is differentiable at every point of that set and the set is uniquely
mdifferentiable. -/
theorem continuousOn_riemannianSpeed {gamma : ℝ → M} {s : Set ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma s)
    (hmdiff : ∀ t ∈ s, MDiffAt gamma t) (hunique : UniqueMDiff[s]) :
    ContinuousOn (riemannianSpeed I gamma) s := by
  let q : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ := fun t ↦
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, 1)
  have hq_proj (t : ℝ) : (q t).proj = t := by
    simp only [q, tangentBundleModelSpaceHomeomorph_coe_symm]
    rfl
  have hq : Continuous q :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hq_maps : MapsTo q s (Bundle.TotalSpace.proj ⁻¹' s) := by
    intro t ht
    simpa only [Set.mem_preimage, hq_proj] using ht
  have hwithin : ContinuousOn
      (fun t ↦ tangentMapWithin 𝓘(ℝ, ℝ) I gamma s (q t)) s :=
    (hgamma.continuousOn_tangentMapWithin (by norm_num) hunique).comp
      hq.continuousOn hq_maps
  have htangent : ContinuousOn
      (fun t ↦ tangentMap 𝓘(ℝ, ℝ) I gamma (q t)) s := by
    refine hwithin.congr fun t ht ↦ ?_
    have hunique_t : UniqueMDiffAt[s] (q t).proj := by
      rw [hq_proj]
      exact hunique t ht
    have hmdiff_t : MDiffAt gamma (q t).proj := by
      rw [hq_proj]
      exact hmdiff t ht
    exact (tangentMapWithin_eq_tangentMap hunique_t hmdiff_t).symm
  have hinner : ContinuousOn (fun t : ℝ ↦
      @inner ℝ (TangentSpace I (gamma t)) _
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)) s := by
    exact htangent.inner_bundle htangent
  refine hinner.sqrt.congr fun t _ ↦ ?_
  rw [riemannianSpeed_apply, norm_eq_sqrt_real_inner]

/-- Riemannian speed is continuous at every point where the curve is `C^1`. -/
theorem continuousAt_riemannianSpeed {gamma : ℝ → M} {t : ℝ}
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma t) :
    ContinuousAt (riemannianSpeed I gamma) t := by
  have hevent : ∀ᶠ s in 𝓝 t, ContMDiffAt 𝓘(ℝ, ℝ) I 1 gamma s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := (1 : ℕ∞)) (by simp)).mp hgamma
  obtain ⟨s, hsub, hs_open, hts⟩ := mem_nhds_iff.mp hevent
  have hcont : ContinuousOn (riemannianSpeed I gamma) s :=
    continuousOn_riemannianSpeed I
      (fun u hu ↦ (hsub hu).contMDiffWithinAt)
      (fun u hu ↦ (hsub hu).mdifferentiableAt (by norm_num))
      hs_open.uniqueMDiffOn
  exact hcont.continuousAt (hs_open.mem_nhds hts)

/-- The Riemannian speed of a globally `C^1` curve is continuous. -/
theorem continuous_riemannianSpeed {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma) :
    Continuous (riemannianSpeed I gamma) :=
  continuous_iff_continuousAt.mpr fun _ ↦
    continuousAt_riemannianSpeed I hgamma.contMDiffAt

omit [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- On an ordered interval, Mathlib's `pathELength` is the extended-real
image of the integral of Riemannian speed. -/
theorem pathELength_eq_ofReal_integral_riemannianSpeed
    {gamma : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hint : MeasureTheory.IntegrableOn (riemannianSpeed I gamma) (Icc a b)) :
    pathELength I gamma a b =
      ENNReal.ofReal (∫ t in a..b, riemannianSpeed I gamma t) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have heq : (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖ₑ) =
      fun t ↦ ENNReal.ofReal (riemannianSpeed I gamma t) := by
    funext t
    simp [riemannianSpeed, ← ofReal_norm]
  rw [heq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  · exact Filter.Eventually.of_forall fun t ↦ riemannianSpeed_nonneg I gamma t

end

end TauCeti.Manifold
