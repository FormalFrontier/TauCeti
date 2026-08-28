/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Translation
public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rellich--Kondrachov for zero-boundary first-order Sobolev spaces

This file proves the compact embedding

`W^{1,p}_0(Ω) → Lᵖ(Ω)`

for a bounded open subset `Ω` of a finite-dimensional real inner-product space and
`1 ≤ p < ∞`.  No regularity of the boundary is needed: a zero-boundary Sobolev function extends
by zero to a whole-space Sobolev function, and the extension is supported in `Ω`.

The proof applies the Fréchet--Kolmogorov criterion to the zero-extended values of the open unit
ball.  Their `Lᵖ` norms are uniformly bounded by their Sobolev norms, their supports lie in the
fixed bounded set `Ω`, and the whole-space Sobolev translation estimate bounds every translation
increment by `‖h‖ ‖∇u‖ₚ`.  Restriction back to `Ω` then gives compactness of the canonical value
map `TauCeti.W1p0.valueL`.

The corresponding compact embedding for all of `W^{1,p}(Ω)` requires a boundary-regular
extension operator and is not claimed here.

## Main declaration

* `TauCeti.W1p0.isCompactOperator_valueL`: Rellich--Kondrachov for `W^{1,p}_0(Ω)`.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Corollary 9.16; L. C. Evans, *Partial Differential Equations*,
Section 5.7.  The compactness criterion used here is the Kolmogorov--Riesz form proved in
`TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Shortcut instance for the norm inherited through the two nested Sobolev subspaces. -/
noncomputable local instance instSeminormedAddCommGroupW1p0 :
    SeminormedAddCommGroup (W1p0 mu Omega p) := inferInstance

/-- Shortcut instance for the scalar action inherited through the two nested Sobolev subspaces. -/
noncomputable local instance instNormedSpaceW1p0 :
    NormedSpace ℝ (W1p0 mu Omega p) := inferInstance

/-- Regard an `Lᵖ` class for the restriction to `univ` as an `Lᵖ` class for the original
measure. -/
private def univLpL : Lp ℝ p (mu.restrict (Set.univ : Set E)) →L[ℝ] Lp ℝ p mu :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (by simp)

/-- The value of a zero-boundary Sobolev function, extended by zero to the whole space. -/
private def W1p0.valueExtendByZeroL : W1p0 mu Omega p →L[ℝ] Lp ℝ p mu :=
  univLpL.comp <| (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
    (subset_univ (Omega : Set E))).toContinuousLinearMap.comp W1p0.valueL

private theorem W1p0.norm_valueExtendByZeroL_le (u : W1p0 mu Omega p) :
    ‖W1p0.valueExtendByZeroL u‖ ≤ ‖u‖ := by
  calc
    ‖W1p0.valueExtendByZeroL u‖ ≤ ‖univLpL (E := E) (mu := mu) (p := p)‖ *
        ‖(extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ (Omega : Set E)))
          (W1p0.valueL u)‖ := by
      exact (univLpL (E := E) (mu := mu) (p := p)).le_opNorm _
    _ ≤ 1 * ‖(extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
        (subset_univ (Omega : Set E))) (W1p0.valueL u)‖ := by
      gcongr
      exact (Lp.norm_LpToLpOfMeasureLeSMul_le ENNReal.one_ne_top (by simp)).trans_eq <| by simp
    _ = ‖W1p0.valueL u‖ := by rw [one_mul, LinearIsometry.norm_map]
    _ ≤ ‖u‖ := W1p0.norm_value_le u

private theorem W1p0.coeFn_valueExtendByZeroL (u : W1p0 mu Omega p) :
    (W1p0.valueExtendByZeroL u : E → ℝ) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (by simp)
    ((extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ (Omega : Set E)))
      (W1p0.valueL u))).trans <| by
        simpa only [W1p0.valueL_apply, Measure.restrict_univ] using
          coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
            (subset_univ (Omega : Set E)) (W1p0.valueL u)

private theorem W1p0.translation_valueExtendByZeroL (hp : p ≠ ∞) (u : W1p0 mu Omega p)
    (h : E) :
    eLpNorm (fun x => W1p0.valueExtendByZeroL u (x + h) - W1p0.valueExtendByZeroL u x) p mu
      ≤ ‖h‖ₑ * ‖u‖ₑ := by
  let u0 : W1p0 mu (⊤ : Opens E) p := W1p0.extendByZeroL le_top u
  have hvalue : (W1p0.valueExtendByZeroL u : E → ℝ) =ᵐ[mu]
      (W1p.value (u0 : W1p mu (⊤ : Opens E) p) : E → ℝ) := by
    have hu0 : W1p.value (u0 : W1p mu (⊤ : Opens E) p) =
        extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ (Omega : Set E))
          (W1p0.valueL u) := by
      dsimp only [u0]
      rw [W1p0.value_extendByZeroL, W1p0.valueL_apply]
    have hu0ae : (W1p.value (u0 : W1p mu (⊤ : Opens E) p) : E → ℝ) =ᵐ[mu]
        (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
      rw [hu0]
      simpa only [W1p0.valueL_apply, Measure.restrict_univ] using
        coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
          (subset_univ (Omega : Set E)) (W1p0.valueL u)
    exact (W1p0.coeFn_valueExtendByZeroL u).trans hu0ae.symm
  have hvalue_add := hvalue.comp_tendsto
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
  calc
    eLpNorm (fun x => W1p0.valueExtendByZeroL u (x + h) - W1p0.valueExtendByZeroL u x) p mu
        = eLpNorm (fun x => W1p.value (u0 : W1p mu (⊤ : Opens E) p) (x + h) -
            W1p.value (u0 : W1p mu (⊤ : Opens E) p) x) p mu := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [hvalue, hvalue_add] with x hx hxadd
          simp only [Function.comp_apply] at hxadd
          rw [hx, hxadd]
    _ ≤ ‖h‖ₑ * ‖W1p.gradient (u0 : W1p mu (⊤ : Opens E) p)‖ₑ :=
      W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient hp h u0.2
    _ ≤ ‖h‖ₑ * ‖u0‖ₑ := by
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_mono (W1p.norm_gradient_le _)
    _ = ‖h‖ₑ * ‖u‖ₑ := by
      congr 1
      dsimp only [u0]
      rw [← ofReal_norm, ← ofReal_norm]
      exact congrArg ENNReal.ofReal (W1p0.norm_extendByZeroL le_top u)

private theorem W1p0.isCompactOperator_valueExtendByZeroL (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator
      (W1p0.valueExtendByZeroL (mu := mu) (Omega := Omega) (p := p)).toLinearMap := by
  let T : W1p0 mu Omega p →L[ℝ] Lp ℝ p mu :=
    W1p0.valueExtendByZeroL (mu := mu) (Omega := Omega) (p := p)
  let S : Set (Lp ℝ p mu) := T '' ball (0 : W1p0 mu Omega p) 1
  -- Zero extension gives the fixed support and norm bounds in Fréchet--Kolmogorov.
  have hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ (Omega : Set E) → f x = 0 := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := hf
    filter_upwards [W1p0.coeFn_valueExtendByZeroL (mu := mu) (Omega := Omega) (p := p) u]
      with x hx
    intro hxOmega
    rw [hx, indicator_of_notMem hxOmega]
  have hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ 1 := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := hf
    rw [mem_ball, dist_zero_right] at hu
    rw [← Lp.enorm_def]
    calc
      ‖W1p0.valueExtendByZeroL u‖ₑ ≤ ‖(1 : ℝ)‖ₑ := enorm_le_iff_norm_le.mpr
        ((W1p0.norm_valueExtendByZeroL_le (mu := mu) (Omega := Omega) (p := p) u).trans
          (by simpa using hu.le))
      _ = 1 := by simp
  -- The Sobolev translation estimate is uniform on the open unit ball.
  have htrans : ∀ epsilon : ENNReal, 0 < epsilon → ∃ delta > 0, ∀ f ∈ S, ∀ h : E,
      ‖h‖ < delta → eLpNorm (fun x => f (x + h) - f x) p mu ≤ epsilon := by
    intro epsilon hepsilon
    let eta : ENNReal := min epsilon 1
    have heta_pos : 0 < eta := lt_min hepsilon zero_lt_one
    have heta_top : eta ≠ ∞ := (min_le_right epsilon 1).trans_lt ENNReal.one_lt_top |>.ne
    refine ⟨eta.toReal, ENNReal.toReal_pos heta_pos.ne' heta_top, fun f hf h hh => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hf
    rw [mem_ball, dist_zero_right] at hu
    have hh' : ‖h‖ₑ ≤ eta := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_le_iff_le_toReal heta_top).2 hh.le
    have hu' : ‖u‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_mono hu.le
    calc
      eLpNorm (fun x => W1p0.valueExtendByZeroL u (x + h) -
          W1p0.valueExtendByZeroL u x) p mu
          ≤ ‖h‖ₑ * ‖u‖ₑ := W1p0.translation_valueExtendByZeroL
            (mu := mu) (Omega := Omega) hp u h
      _ ≤ eta * 1 := mul_le_mul' hh' hu'
      _ = eta := mul_one eta
      _ ≤ epsilon := min_le_left _ _
  -- The criterion makes the extended image relatively compact.
  have hcompact : IsCompact (closure S) :=
    isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl
      (E := E) (F := ℝ) (mu := mu) (p := p) (S := S) (s := (Omega : Set E)) (M := 1)
      hp hOmega hsupp ENNReal.one_ne_top hbdd htrans
  apply (isCompactOperator_iff_isCompact_closure_image_ball T.toLinearMap one_pos).2
  rw [ContinuousLinearMap.coe_coe T]
  simpa only [S] using hcompact

/-- **Rellich--Kondrachov for zero-boundary Sobolev spaces.**  If `Ω` is bounded and
`1 ≤ p < ∞`, the canonical value map `W^{1,p}_0(Ω) → Lᵖ(Ω)` is a compact operator.

No boundary regularity is assumed.  The zero-boundary condition is what permits extension by zero
without creating a distributional boundary term. -/
theorem W1p0.isCompactOperator_valueL (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator (W1p0.valueL (mu := mu) (Omega := Omega) (p := p)) := by
  let T : W1p0 mu Omega p →L[ℝ] Lp ℝ p mu :=
    W1p0.valueExtendByZeroL (mu := mu) (Omega := Omega) (p := p)
  have hT : IsCompactOperator T.toLinearMap :=
    W1p0.isCompactOperator_valueExtendByZeroL hp hOmega
  have hrestrict :
      (LpToLpRestrictCLM E ℝ ℝ mu p (Omega : Set E)).comp T = W1p0.valueL := by
    dsimp only [T]
    ext u
    have hvalue : (W1p.value (u : W1p mu Omega p) : E → ℝ) =ᵐ[mu.restrict Omega]
        (W1p0.valueL u : E → ℝ) := by
      rw [← Lp.ext_iff]
      exact (W1p0.valueL_apply u).symm
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Omega : Set E) (T u),
      (W1p0.coeFn_valueExtendByZeroL (mu := mu) (Omega := Omega) (p := p) u).filter_mono
        (ae_mono Measure.restrict_le_self), ae_restrict_mem Omega.isOpen.measurableSet, hvalue]
        with x hx hTux hxOmega hvaluex
    rw [ContinuousLinearMap.comp_apply, hx, hTux, indicator_of_mem hxOmega, hvaluex]
  rw [← hrestrict]
  exact hT.clm_comp (LpToLpRestrictCLM E ℝ ℝ mu p (Omega : Set E))

end TauCeti
