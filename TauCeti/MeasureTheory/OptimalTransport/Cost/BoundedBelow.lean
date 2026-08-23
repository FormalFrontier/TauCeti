/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Transport costs bounded below by integrable marginal terms

An extended-real transport cost may take negative values, so it cannot be integrated directly by
`lintegral`. If `c : X × Y → EReal` is bounded below by a split function `a x + b y`, with `a`
and `b` integrable against the two marginals, subtracting that lower bound leaves a nonnegative
residual. Its `lintegral` is well-defined, and adding back the two fixed marginal integrals gives
the signed extended cost of a coupling.

This file packages the lower-bound hypothesis as `TauCeti.IntegrableSplitLowerBound`, defines the
cost `TauCeti.planCostBddBelow` of an individual feasible plan, and defines its infimum
`TauCeti.transportCostBddBelow`. The main theorem
`TauCeti.transportCostBddBelow_congr_lowerBound` proves that the value is independent of the
chosen split lower bound. The specialization
`TauCeti.transportCostBddBelow_coe_eq_transportCost` recovers the nonnegative
`TauCeti.transportCost` interface exactly.

The normalization avoids every indeterminate subtraction: the only extended integral is the
`lintegral` of a nonnegative residual, and the quantities added afterwards are finite real
numbers. In particular, a cost identically `∞` still has value `∞`, while an empty feasible set
also has value `∞`.

## References

* C. Villani, *Optimal Transport: Old and New*, Chapter 5, especially the convention of allowing
  costs bounded below by a sum of integrable marginal functions.
* `TauCetiRoadmap/OptimalTransport/README.md`, Layer 1, item 1 (the bounded-below signed cost
  interface).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → EReal} {μ : Measure X} {ν : Measure Y}

/-- An integrable split lower bound for an extended-real cost `c` with marginals `μ` and `ν`.

The functions `fst` and `snd` provide the normalization
`fst x + snd y ≤ c (x, y)`. Their integrability makes their two marginal integrals finite, which
is precisely what prevents an `∞ - ∞` ambiguity when the normalization is added back. -/
structure IntegrableSplitLowerBound (c : X × Y → EReal) (μ : Measure X) (ν : Measure Y) where
  /-- The part of the lower bound depending on the source variable. -/
  fst : X → ℝ
  /-- The part of the lower bound depending on the target variable. -/
  snd : Y → ℝ
  /-- The source part is integrable against the source marginal. -/
  integrable_fst : Integrable fst μ
  /-- The target part is integrable against the target marginal. -/
  integrable_snd : Integrable snd ν
  /-- The two marginal terms together bound the cost from below. -/
  le_cost : ∀ x y, ((fst x + snd y : ℝ) : EReal) ≤ c (x, y)

namespace IntegrableSplitLowerBound

/-- Two integrable split lower bounds are equal when their source and target parts agree
pointwise. -/
@[ext]
theorem ext {h k : IntegrableSplitLowerBound c μ ν}
    (hfst : ∀ x, h.fst x = k.fst x) (hsnd : ∀ y, h.snd y = k.snd y) : h = k := by
  have hfst_eq : h.fst = k.fst := funext hfst
  have hsnd_eq : h.snd = k.snd := funext hsnd
  cases h
  cases k
  simp_all

variable (h : IntegrableSplitLowerBound c μ ν)

/-- The nonnegative residual left after subtracting an integrable split lower bound from a cost. -/
def residual (z : X × Y) : ℝ≥0∞ :=
  (c z - (h.fst z.1 + h.snd z.2 : ℝ)).toENNReal

/-- The characteristic formula for the residual of an integrable split lower bound. -/
theorem residual_def (z : X × Y) :
    h.residual z = (c z - (h.fst z.1 + h.snd z.2 : ℝ)).toENNReal :=
  (rfl)

/-- The residual is the exact nonnegative part of the normalized cost: adding the split lower
bound back in `EReal` recovers the original cost, including when that cost is `∞`. -/
@[simp]
theorem coe_residual_add (z : X × Y) :
    (h.residual z : EReal) + ((h.fst z.1 : EReal) + (h.snd z.2 : EReal)) = c z := by
  rw [← EReal.coe_add, residual, EReal.coe_toENNReal]
  · exact EReal.sub_add_cancel
  · exact (EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _))
      (Or.inr (EReal.coe_ne_bot _))).2 (h.le_cost z.1 z.2)

/-- Every nonnegative extended-real cost has the zero split lower bound. -/
def ofNonneg (hc : ∀ z, 0 ≤ c z) (μ : Measure X) (ν : Measure Y) :
    IntegrableSplitLowerBound c μ ν where
  fst := 0
  snd := 0
  integrable_fst := integrable_zero X ℝ μ
  integrable_snd := integrable_zero Y ℝ ν
  le_cost x y := by simpa using hc (x, y)

end IntegrableSplitLowerBound

/-- The signed cost of a coupling, normalized using an integrable split lower bound.

The coupling witness is part of the domain because the fixed marginal correction terms reconstruct
the plan's cost only when `π` has marginals `μ` and `ν`; for an arbitrary measure, this expression
can depend on the chosen lower bound. -/
def planCostBddBelow (π : Measure (X × Y)) (_hπ : IsCoupling π μ ν)
    (h : IntegrableSplitLowerBound c μ ν) : EReal :=
  ((∫⁻ z, h.residual z ∂π : ℝ≥0∞) : EReal) +
    ((∫ x, h.fst x ∂μ : ℝ) : EReal) + ((∫ y, h.snd y ∂ν : ℝ) : EReal)

/-- The characteristic formula for the normalized signed cost of a coupling. -/
theorem planCostBddBelow_def (π : Measure (X × Y)) (hπ : IsCoupling π μ ν)
    (h : IntegrableSplitLowerBound c μ ν) :
    planCostBddBelow π hπ h =
      ((∫⁻ z, h.residual z ∂π : ℝ≥0∞) : EReal) +
        ((∫ x, h.fst x ∂μ : ℝ) : EReal) + ((∫ y, h.snd y ∂ν : ℝ) : EReal) :=
  (rfl)

/-- The transport cost of `μ` and `ν` for an extended-real cost bounded below by integrable
marginal terms.

For a lower bound `h` with components `a` and `b`, this is the infimum over couplings `π` of
`↑(∫⁻ (c - a ⊕ b) dπ) + ∫ a dμ + ∫ b dν`. The residual is nonnegative by `h.le_cost`, and the
last two summands are finite real numbers. The value does not depend on `h`; see
`transportCostBddBelow_congr_lowerBound`. -/
def transportCostBddBelow (c : X × Y → EReal) (μ : Measure X) (ν : Measure Y)
    (h : IntegrableSplitLowerBound c μ ν) : EReal :=
  ⨅ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν), planCostBddBelow π hπ h

/-- The characteristic formula for the bounded-below signed transport cost. -/
theorem transportCostBddBelow_def :
    transportCostBddBelow c μ ν h =
      ⨅ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν),
        planCostBddBelow π hπ h :=
  (rfl)

/-- The signed transport cost is bounded above by the normalized cost of every feasible plan. -/
theorem transportCostBddBelow_le (hπ : IsCoupling π μ ν)
    (h : IntegrableSplitLowerBound c μ ν) :
    transportCostBddBelow c μ ν h ≤ planCostBddBelow π hπ h :=
  iInf₂_le π hπ

/-- A lower bound valid for the normalized cost of every coupling bounds the signed transport
cost from below. -/
theorem le_transportCostBddBelow {d : EReal} (h : IntegrableSplitLowerBound c μ ν)
    (hd : ∀ π hπ, d ≤ planCostBddBelow π hπ h) :
    d ≤ transportCostBddBelow c μ ν h :=
  le_iInf₂ hd

private theorem residual_add_lowerBoundParts
    (h k : IntegrableSplitLowerBound c μ ν) (z : X × Y) :
    h.residual z + ENNReal.ofReal (h.fst z.1 - k.fst z.1) +
        ENNReal.ofReal (h.snd z.2 - k.snd z.2) =
      k.residual z + ENNReal.ofReal (k.fst z.1 - h.fst z.1) +
        ENNReal.ofReal (k.snd z.2 - h.snd z.2) := by
  by_cases htop : c z = ⊤
  · have hres_top (a b : ℝ) :
        ((⊤ : EReal) - ((a + b : ℝ) : EReal)).toENNReal = ⊤ := by
      rw [EReal.top_sub_coe, EReal.toENNReal_eq_top_iff.2 rfl]
    simp only [IntegrableSplitLowerBound.residual, htop, hres_top]
    simp
  have hbot : c z ≠ ⊥ := by
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h.le_cost z.1 z.2)
  lift c z to ℝ using ⟨htop, hbot⟩ with q hq
  have hh : h.fst z.1 + h.snd z.2 ≤ q := by
    exact EReal.coe_le_coe_iff.1 (hq ▸ h.le_cost z.1 z.2)
  have hk : k.fst z.1 + k.snd z.2 ≤ q := by
    exact EReal.coe_le_coe_iff.1 (hq ▸ k.le_cost z.1 z.2)
  have hresidual_h : h.residual z = ENNReal.ofReal (q - (h.fst z.1 + h.snd z.2)) := by
    simp only [IntegrableSplitLowerBound.residual, ← hq, ← EReal.coe_sub,
      EReal.real_coe_toENNReal]
  have hresidual_k : k.residual z = ENNReal.ofReal (q - (k.fst z.1 + k.snd z.2)) := by
    simp only [IntegrableSplitLowerBound.residual, ← hq, ← EReal.coe_sub,
      EReal.real_coe_toENNReal]
  have hl : h.residual z + ENNReal.ofReal (h.fst z.1 - k.fst z.1) +
      ENNReal.ofReal (h.snd z.2 - k.snd z.2) ≠ ⊤ := by
    simp [hresidual_h]
  have hr : k.residual z + ENNReal.ofReal (k.fst z.1 - h.fst z.1) +
      ENNReal.ofReal (k.snd z.2 - h.snd z.2) ≠ ⊤ := by
    simp [hresidual_k]
  rw [← ENNReal.toReal_eq_toReal_iff' hl hr]
  rw [hresidual_h, hresidual_k,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal']
  rw [max_eq_left (sub_nonneg.2 hh), max_eq_left (sub_nonneg.2 hk)]
  grind [max_zero_sub_max_neg_zero_eq_self]

/-- On a coupling, the signed plan cost is independent of the chosen split lower bound. -/
theorem planCostBddBelow_congr_lowerBound
    (h k : IntegrableSplitLowerBound c μ ν) (hπ : IsCoupling π μ ν) :
    planCostBddBelow π hπ h = planCostBddBelow π hπ k := by
  simp only [planCostBddBelow]
  -- Split the change of normalization into its positive and negative marginal parts.
  let fx : X → ℝ := fun x ↦ h.fst x - k.fst x
  let fy : Y → ℝ := fun y ↦ h.snd y - k.snd y
  let px : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (fx x) ∂μ
  let nx : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-fx x) ∂μ
  let py : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (fy y) ∂ν
  let ny : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (-fy y) ∂ν
  have hfx : Integrable fx μ := h.integrable_fst.sub k.integrable_fst
  have hfy : Integrable fy ν := h.integrable_snd.sub k.integrable_snd
  have hpx : px ≠ ⊤ := hfx.lintegral_lt_top.ne
  have hnx : nx ≠ ⊤ := hfx.neg.lintegral_lt_top.ne
  have hpy : py ≠ ⊤ := hfy.lintegral_lt_top.ne
  have hny : ny ≠ ⊤ := hfy.neg.lintegral_lt_top.ne
  have hfxm : AEMeasurable (fun x ↦ ENNReal.ofReal (fx x)) μ :=
    hfx.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfym : AEMeasurable (fun y ↦ ENNReal.ofReal (fy y)) ν :=
    hfy.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hnfxm : AEMeasurable (fun x ↦ ENNReal.ofReal (-fx x)) μ :=
    hfx.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hnfym : AEMeasurable (fun y ↦ ENNReal.ofReal (-fy y)) ν :=
    hfy.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  -- Pull all four parts back to the coupling through its two fixed marginals.
  have hpxmap : ∫⁻ z, ENNReal.ofReal (fx z.1) ∂π = px := by
    have hm : AEMeasurable (fun x ↦ ENNReal.ofReal (fx x)) π.fst := by
      rwa [hπ.fst_eq]
    dsimp only [px]
    rw [← hπ.fst_eq]
    exact (lintegral_map' hm measurable_fst.aemeasurable).symm
  have hpymap : ∫⁻ z, ENNReal.ofReal (fy z.2) ∂π = py := by
    have hm : AEMeasurable (fun y ↦ ENNReal.ofReal (fy y)) π.snd := by
      rwa [hπ.snd_eq]
    dsimp only [py]
    rw [← hπ.snd_eq]
    exact (lintegral_map' hm measurable_snd.aemeasurable).symm
  have hnxmap : ∫⁻ z, ENNReal.ofReal (-fx z.1) ∂π = nx := by
    have hm : AEMeasurable (fun x ↦ ENNReal.ofReal (-fx x)) π.fst := by
      rwa [hπ.fst_eq]
    dsimp only [nx]
    rw [← hπ.fst_eq]
    exact (lintegral_map' hm measurable_fst.aemeasurable).symm
  have hnymap : ∫⁻ z, ENNReal.ofReal (-fy z.2) ∂π = ny := by
    have hm : AEMeasurable (fun y ↦ ENNReal.ofReal (-fy y)) π.snd := by
      rwa [hπ.snd_eq]
    dsimp only [ny]
    rw [← hπ.snd_eq]
    exact (lintegral_map' hm measurable_snd.aemeasurable).symm
  let mpfst : MeasurePreserving Prod.fst π μ := ⟨measurable_fst, hπ.fst_eq⟩
  let mpsnd : MeasurePreserving Prod.snd π ν := ⟨measurable_snd, hπ.snd_eq⟩
  have hfxmp : AEMeasurable (fun z : X × Y ↦ ENNReal.ofReal (fx z.1)) π :=
    hfxm.comp_quasiMeasurePreserving mpfst.quasiMeasurePreserving
  have hfymp : AEMeasurable (fun z : X × Y ↦ ENNReal.ofReal (fy z.2)) π :=
    hfym.comp_quasiMeasurePreserving mpsnd.quasiMeasurePreserving
  have hnfxmp : AEMeasurable (fun z : X × Y ↦ ENNReal.ofReal (-fx z.1)) π :=
    hnfxm.comp_quasiMeasurePreserving mpfst.quasiMeasurePreserving
  have hnfymp : AEMeasurable (fun z : X × Y ↦ ENNReal.ofReal (-fy z.2)) π :=
    hnfym.comp_quasiMeasurePreserving mpsnd.quasiMeasurePreserving
  -- Integrate the pointwise residual balance after adjoining those four parts.
  have hres : (∫⁻ z, h.residual z ∂π) + px + py =
      (∫⁻ z, k.residual z ∂π) + nx + ny := by
    rw [← hpxmap, ← hpymap, ← hnxmap, ← hnymap,
      ← lintegral_add_right' _ hfxmp, ← lintegral_add_right' _ hfymp,
      ← lintegral_add_right' _ hnfxmp, ← lintegral_add_right' _ hnfymp]
    apply lintegral_congr
    intro z
    simpa [fx, fy, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      residual_add_lowerBoundParts h k z
  have hdiff : px.toReal - nx.toReal + (py.toReal - ny.toReal) =
      (∫ x, h.fst x ∂μ) + (∫ y, h.snd y ∂ν) -
        ((∫ x, k.fst x ∂μ) + (∫ y, k.snd y ∂ν)) := by
    rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfx,
      ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfy]
    simp only [fx, fy, integral_sub h.integrable_fst k.integrable_fst,
      integral_sub h.integrable_snd k.integrable_snd]
    ring
  have hres' :
      ((∫⁻ z, h.residual z ∂π : ℝ≥0∞) : EReal) +
          ((px.toReal + py.toReal : ℝ) : EReal) =
        ((∫⁻ z, k.residual z ∂π : ℝ≥0∞) : EReal) +
          ((nx.toReal + ny.toReal : ℝ) : EReal) := by
    simpa [EReal.coe_ennreal_add, EReal.coe_add, EReal.coe_ennreal_toReal, hpx, hnx, hpy, hny,
      add_assoc] using congrArg (fun t : ℝ≥0∞ ↦ (t : EReal)) hres
  -- Recombine the positive/negative parts with the finite marginal integrals.
  calc
    ((∫⁻ z, h.residual z ∂π : ℝ≥0∞) : EReal) +
          ((∫ x, h.fst x ∂μ : ℝ) : EReal) + ((∫ y, h.snd y ∂ν : ℝ) : EReal) =
        (((∫⁻ z, h.residual z ∂π : ℝ≥0∞) : EReal) +
          ((px.toReal + py.toReal : ℝ) : EReal)) +
          (((∫ x, h.fst x ∂μ) + (∫ y, h.snd y ∂ν) -
            (px.toReal + py.toReal) : ℝ) : EReal) := by
            simp only [← EReal.coe_add, add_assoc]
            ring_nf
    _ = (((∫⁻ z, k.residual z ∂π : ℝ≥0∞) : EReal) +
          ((nx.toReal + ny.toReal : ℝ) : EReal)) +
          (((∫ x, h.fst x ∂μ) + (∫ y, h.snd y ∂ν) -
            (px.toReal + py.toReal) : ℝ) : EReal) := by
            rw [hres']
    _ = ((∫⁻ z, k.residual z ∂π : ℝ≥0∞) : EReal) +
          ((∫ x, k.fst x ∂μ : ℝ) : EReal) + ((∫ y, k.snd y ∂ν : ℝ) : EReal) := by
            simp only [← EReal.coe_add, add_assoc]
            congr 1
            norm_cast
            linarith

/-- The signed transport cost is independent of the chosen integrable split lower bound. -/
theorem transportCostBddBelow_congr_lowerBound
    (h k : IntegrableSplitLowerBound c μ ν) :
    transportCostBddBelow c μ ν h = transportCostBddBelow c μ ν k := by
  simp only [transportCostBddBelow]
  exact iInf_congr fun π ↦ iInf_congr fun hπ ↦ planCostBddBelow_congr_lowerBound h k hπ

private theorem coe_iInf_ennreal {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅ i, f i : ℝ≥0∞) : EReal) = ⨅ i, (f i : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le f i)
  · have hnonneg : 0 ≤ (⨅ i, (f i : EReal)) :=
      le_iInf fun i ↦ EReal.coe_ennreal_nonneg (f i)
    rw [← EReal.coe_toENNReal hnonneg]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 <| le_iInf fun i ↦
      (EReal.toENNReal_le_toENNReal (iInf_le (fun j ↦ (f j : EReal)) i)).trans_eq
        EReal.toENNReal_coe

/-- For a nonnegative `ℝ≥0∞`-valued cost, the bounded-below signed interface agrees exactly
with the original nonnegative transport cost, for any valid split lower bound. -/
theorem transportCostBddBelow_coe_eq_transportCost (c : X × Y → ℝ≥0∞)
    (μ : Measure X) (ν : Measure Y)
    (h : IntegrableSplitLowerBound (fun z ↦ (c z : EReal)) μ ν) :
    transportCostBddBelow (fun z ↦ (c z : EReal)) μ ν h =
      (transportCost c μ ν : EReal) := by
  rw [transportCostBddBelow_congr_lowerBound h
    (IntegrableSplitLowerBound.ofNonneg (fun _ ↦ EReal.coe_ennreal_nonneg _) μ ν)]
  rw [transportCost_def, coe_iInf_ennreal]
  apply iInf_congr
  intro π
  rw [coe_iInf_ennreal]
  simp only [planCostBddBelow, IntegrableSplitLowerBound.residual,
    IntegrableSplitLowerBound.ofNonneg,
    Pi.zero_apply, sub_zero,
    EReal.toENNReal_coe, integral_zero, EReal.coe_zero, add_zero]

end TauCeti
