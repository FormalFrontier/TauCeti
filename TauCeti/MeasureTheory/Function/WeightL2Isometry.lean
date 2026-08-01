/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The weight ↔ measure isometry `L²(w·μ) ≃ₗᵢ L²(μ)`

For an almost-everywhere-positive real weight `w` on an arbitrary measurable space, multiplication
by `√w` is a linear isometric equivalence from the weighted `L²` space `L²(w·μ)` onto `L²(μ)`, where
`w·μ := μ.withDensity (ENNReal.ofReal ∘ w)`. It is an *equivalence* precisely because `w > 0`
almost everywhere: the inverse is multiplication by `(√w)⁻¹`.

This is the Part 0 primitive `weightL2Isometry` from the `OrthogonalL2Bases` roadmap, the single
map converting a weight-in-the-measure normalization to a weight-in-the-function normalization. Once
combined with `HilbertBasis.mapₗᵢ` (transport of a Hilbert basis across a `≃ₗᵢ`, already in
`TauCeti.Analysis.InnerProductSpace.HilbertBasisMap`), it moves an orthogonal-polynomial basis of a
weighted measure to the `√w`-envelope basis of the reference measure and back.

The construction is purely measure-theoretic, so it is stated over an arbitrary `MeasurableSpace`;
only the later polynomial-facing layers specialize to `Measure ℝ`.

## Main definitions

* `TauCeti.weightL2Isometry` — the isometric equivalence `L²(w·μ) ≃ₗᵢ[𝕜] L²(μ)`.

## Main statements

* `TauCeti.weightL2Isometry_apply` — the forward map is multiplication by `√w`.
* `TauCeti.weightL2Isometry_symm_apply` — the inverse map is multiplication by `(√w)⁻¹`.

The file also provides the underlying `L²` seminorm identity: the `L²(μ)` seminorm of `√w · g`
equals the `L²(w·μ)` seminorm of `g`.
-/

public section

namespace TauCeti

open MeasureTheory

open scoped ENNReal NNReal

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] (μ : Measure α) (w : α → ℝ)

/-- **Core seminorm identity.** The `L²(μ)` seminorm of `√w · g` equals the `L²(w·μ)` seminorm of
`g`, where `w·μ = μ.withDensity (ENNReal.ofReal ∘ w)`. Only nonnegativity of `w` almost everywhere
is needed. -/
private theorem eLpNorm_sqrt_smul_withDensity (hwm : AEMeasurable w μ)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x) (g : α → 𝕜) :
    eLpNorm (fun x => Real.sqrt (w x) • g x) 2 μ
      = eLpNorm g 2 (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
  have h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2z h2t, ht]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ μ hwm.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [hw_nonneg] with x hx
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (w x) := Real.sqrt_nonneg _
  simp only [Pi.mul_apply]
  rw [enorm_smul, Real.enorm_of_nonneg hsqnn,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg hsqnn (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two, Real.sq_sqrt hx]

/-- `w · μ` is absolutely continuous with respect to `μ` (always holds). -/
private theorem withDensity_ac :
    (μ.withDensity fun x => ENNReal.ofReal (w x)) ≪ μ := withDensity_absolutelyContinuous _ _

/-- `μ` is absolutely continuous with respect to `w · μ` (uses `w > 0` a.e.). -/
private theorem ac_withDensity (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) :
    μ ≪ μ.withDensity fun x => ENNReal.ofReal (w x) :=
  withDensity_absolutelyContinuous' hwm.ennreal_ofReal (by
    filter_upwards [hwpos] with x hx
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hx)

/-- The forward direction `√w · f` of a class in `L²(w·μ)` is in `L²(μ)`. -/
private theorem memLp_sqrt_smul (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (f : Lp 𝕜 2 (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    MemLp (fun x => Real.sqrt (w x) • (f : α → 𝕜) x) 2 μ := by
  refine ⟨(hwm.sqrt.aestronglyMeasurable).smul
    ((Lp.aestronglyMeasurable f).mono_ac (ac_withDensity μ w hwpos hwm)), ?_⟩
  rw [eLpNorm_sqrt_smul_withDensity μ w hwm (hwpos.mono fun _ h => h.le)]
  exact Lp.eLpNorm_lt_top f

/-- The inverse direction `(√w)⁻¹ · g` of a class in `L²(μ)` is in `L²(w·μ)`. -/
private theorem memLp_inv_sqrt_smul (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (g : Lp 𝕜 2 μ) :
    MemLp (fun x => (Real.sqrt (w x))⁻¹ • (g : α → 𝕜) x) 2
      (μ.withDensity fun x => ENNReal.ofReal (w x)) := by
  have hasm : AEStronglyMeasurable (fun x => (Real.sqrt (w x))⁻¹ • (g : α → 𝕜) x) μ :=
    (hwm.sqrt.inv.aestronglyMeasurable).smul (Lp.aestronglyMeasurable g)
  refine ⟨hasm.mono_ac (withDensity_ac μ w), ?_⟩
  rw [← eLpNorm_sqrt_smul_withDensity μ w hwm (hwpos.mono fun _ h => h.le)]
  refine (eLpNorm_congr_ae ?_).trans_lt (Lp.eLpNorm_lt_top g)
  filter_upwards [hwpos] with x hx
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul]

/-- **The weight ↔ measure isometry.** For an almost-everywhere-positive weight `w`, multiplication
by `√w` is a linear isometric equivalence `L²(w·μ) ≃ₗᵢ[𝕜] L²(μ)`. -/
noncomputable def weightL2Isometry (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ) :
    Lp 𝕜 2 (μ.withDensity fun x => ENNReal.ofReal (w x)) ≃ₗᵢ[𝕜] Lp 𝕜 2 μ where
  toLinearEquiv :=
    { toFun := fun f => (memLp_sqrt_smul μ w hwpos hwm f).toLp _
      invFun := fun g => (memLp_inv_sqrt_smul μ w hwpos hwm g).toLp _
      map_add' := fun f₁ f₂ => by
        rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
        filter_upwards [(Lp.coeFn_add f₁ f₂).filter_mono (ac_withDensity μ w hwpos hwm).ae_le]
          with x hx
        simp only [Pi.add_apply, hx, smul_add]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
        filter_upwards [(Lp.coeFn_smul c f).filter_mono (ac_withDensity μ w hwpos hwm).ae_le]
          with x hx
        simp only [Pi.smul_apply, hx]
        rw [smul_comm]
      left_inv := fun f => by
        refine Lp.ext ?_
        have e2 : (⇑((memLp_sqrt_smul μ w hwpos hwm f).toLp _) : α → 𝕜)
            =ᵐ[μ.withDensity fun x => ENNReal.ofReal (w x)]
              fun x => Real.sqrt (w x) • (f : α → 𝕜) x :=
          (MemLp.coeFn_toLp _).filter_mono (withDensity_ac μ w).ae_le
        filter_upwards [MemLp.coeFn_toLp
          (memLp_inv_sqrt_smul μ w hwpos hwm ((memLp_sqrt_smul μ w hwpos hwm f).toLp _)),
          e2, hwpos.filter_mono (withDensity_ac μ w).ae_le] with x h1 h2 hx
        rw [h1, h2, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul]
      right_inv := fun g => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp
          (memLp_sqrt_smul μ w hwpos hwm ((memLp_inv_sqrt_smul μ w hwpos hwm g).toLp _)),
          (MemLp.coeFn_toLp (memLp_inv_sqrt_smul μ w hwpos hwm g)).filter_mono
            (ac_withDensity μ w hwpos hwm).ae_le,
          hwpos] with x h1 h2 hx
        rw [h1, h2, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hx).ne', one_smul] }
  norm_map' := fun f => by
    -- The forward map is definitionally `MemLp.toLp (√w • f)`; expose that representative so that
    -- `Lp.norm_toLp` fires, then discharge the norm through the core seminorm identity.
    change ‖MemLp.toLp (fun x => Real.sqrt (w x) • (f : α → 𝕜) x)
      (memLp_sqrt_smul μ w hwpos hwm f)‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def,
      eLpNorm_sqrt_smul_withDensity μ w hwm (hwpos.mono fun _ h => h.le)]

/-- The forward isometry is multiplication by `√w`. -/
theorem weightL2Isometry_apply (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (f : Lp 𝕜 2 (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    weightL2Isometry μ w hwpos hwm f =ᵐ[μ] fun x => Real.sqrt (w x) • (f : α → 𝕜) x :=
  MemLp.coeFn_toLp (memLp_sqrt_smul μ w hwpos hwm f)

/-- The inverse isometry is multiplication by `(√w)⁻¹`. -/
theorem weightL2Isometry_symm_apply (hwpos : ∀ᵐ x ∂μ, 0 < w x) (hwm : AEMeasurable w μ)
    (g : Lp 𝕜 2 μ) : (weightL2Isometry μ w hwpos hwm).symm g
      =ᵐ[μ] fun x => (Real.sqrt (w x))⁻¹ • (g : α → 𝕜) x :=
  (MemLp.coeFn_toLp (memLp_inv_sqrt_smul μ w hwpos hwm g)).filter_mono
    (ac_withDensity μ w hwpos hwm).ae_le

end TauCeti
