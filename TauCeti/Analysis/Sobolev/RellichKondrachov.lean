/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Translation
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rellich--Kondrachov for zero-boundary first-order Sobolev spaces

This file proves that the canonical value map

`W^{1,p}_0(Ω) → Lᵖ(Ω)`

is a compact operator, for `1 ≤ p < ∞` and a bounded open subset `Ω` of a finite-dimensional real
inner-product space.  No regularity of the boundary is needed: a zero-boundary Sobolev function
extends by zero to a whole-space Sobolev function, and the extension is supported in `Ω`.

The proof applies the Fréchet--Kolmogorov criterion to the zero-extended values of the open unit
ball.  Their `Lᵖ` norms are uniformly bounded by their Sobolev norms, their supports lie in the
fixed bounded set `Ω`, and the whole-space Sobolev translation estimate bounds every translation
increment by `‖h‖ ‖∇u‖ₚ`.  Restriction back to `Ω` then gives compactness of the canonical value
map `TauCeti.W1p0.valueL`.

The corresponding statement for all of `W^{1,p}(Ω)` requires a boundary-regular extension
operator and is not claimed here.

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Restricting to `⊤` leaves a measure unchanged; this identifies the whole-space `Lᵖ` space in
which the zero extension takes its values with `Lᵖ(mu)`. -/
private theorem restrict_coe_top (nu : Measure E) :
    nu.restrict ((⊤ : Opens E) : Set E) = nu := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- The value of a zero-boundary Sobolev function, extended by zero to the whole space. -/
private def W1p0.valueExtendByZeroL : W1p0 mu Omega p →L[ℝ] Lp ℝ p mu :=
  (castLpₗᵢ (𝕜 := ℝ) (restrict_coe_top mu)).toLinearIsometry.toContinuousLinearMap.comp <|
    (W1p0.valueL (Omega := ⊤)).comp (W1p0.extendByZeroL le_top)

private theorem W1p0.valueExtendByZeroL_apply (u : W1p0 mu Omega p) :
    W1p0.valueExtendByZeroL u =
      castLpₗᵢ (𝕜 := ℝ) (restrict_coe_top mu)
        (W1p0.valueL (W1p0.extendByZeroL le_top u)) :=
  rfl

private theorem W1p0.norm_valueExtendByZeroL_le (u : W1p0 mu Omega p) :
    ‖W1p0.valueExtendByZeroL u‖ ≤ ‖u‖ := by
  calc
    ‖W1p0.valueExtendByZeroL u‖
        = ‖W1p.value (W1p0.extendByZeroL le_top u : W1p mu (⊤ : Opens E) p)‖ := by
      rw [W1p0.valueExtendByZeroL_apply, LinearIsometryEquiv.norm_map, W1p0.valueL_apply]
    _ ≤ ‖W1p0.extendByZeroL le_top u‖ := W1p.norm_value_le _
    _ = ‖u‖ := W1p0.norm_extendByZeroL le_top u

/-- The isometric cast does not move representatives, so the zero-extended value is represented
by the value of the whole-space Sobolev extension. -/
private theorem W1p0.coeFn_valueExtendByZeroL_eq_value (u : W1p0 mu Omega p) :
    (W1p0.valueExtendByZeroL u : E → ℝ) =
      (W1p.value (W1p0.extendByZeroL le_top u : W1p mu (⊤ : Opens E) p) : E → ℝ) :=
  funext fun _ => by rw [W1p0.valueExtendByZeroL_apply, coeFn_castLpₗᵢ, W1p0.valueL_apply]

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
    rw [W1p0.coeFn_valueExtendByZeroL_eq_value]
    exact W1p0.value_extendByZeroL_ae_eq_zero_compl u
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
    obtain ⟨delta, hdelta, hbound⟩ :=
      W1p0.exists_pos_forall_eLpNorm_value_extendByZeroL_comp_add_sub_le_of_norm_le
        (S := ball (0 : W1p0 mu Omega p) 1) (C := 1) hp
        (fun u hu => (mem_ball_zero_iff.1 hu).le) hepsilon
    refine ⟨delta, hdelta, fun f hf h hh => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hf
    rw [W1p0.coeFn_valueExtendByZeroL_eq_value]
    exact hbound u hu h hh
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
    -- On `Ω` the zero extension restricts back to the original value.
    have hvalue : (W1p0.valueExtendByZeroL u : E → ℝ) =ᵐ[mu.restrict (Omega : Set E)]
        (W1p0.valueL u : E → ℝ) := by
      rw [W1p0.coeFn_valueExtendByZeroL_eq_value, W1p0.value_extendByZeroL, W1p0.valueL_apply]
      exact coeFn_extendByZeroLpₗᵢ_restrict ℝ Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value (u : W1p mu Omega p))
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Omega : Set E) (T u), hvalue] with x hx hvaluex
    rw [ContinuousLinearMap.comp_apply, hx]
    exact hvaluex
  rw [← hrestrict]
  exact hT.clm_comp (LpToLpRestrictCLM E ℝ ℝ mu p (Omega : Set E))

end TauCeti
