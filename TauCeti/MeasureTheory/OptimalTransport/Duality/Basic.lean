/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Kantorovich dual feasibility and weak duality

For a nonnegative extended cost `c : X × Y → ℝ≥0∞`, a pair of real potentials `φ` and `ψ` is
dual feasible when

`φ x + ψ y ≤ c (x, y)`.

The comparison is made in `EReal`, so negative potential values and the value `∞` of a forbidden
pair are both represented honestly. The dual value is the sum of the two marginal integrals.
The weak-duality theorems and integral manipulations that need it require both potentials to be
integrable. Integrability is not part of pointwise feasibility, since later `c`-transform arguments
study feasibility before choosing marginals.

Weak duality says that the value of every integrable feasible pair is at most the cost of every
coupling, and hence at most the primal transport cost. Neither the cost nor its integral needs to
be finite or measurable.

## Main definitions

* `TauCeti.DualFeasible c φ ψ` — the pointwise dual constraint;
* `TauCeti.kantorovichDualValue μ ν φ ψ` — the sum of the two marginal integrals.

## Main statements

* `TauCeti.dualFeasible_ofReal_iff` — for a nonnegative real cost, feasibility for the
  associated extended cost is the plain real pointwise inequality;
* `TauCeti.kantorovichDualValue_eq_integral` — against any coupling the dual value is the
  integral of the split sum of the two potentials;
* `TauCeti.DualFeasible.kantorovichDualValue_le_lintegral` — weak duality against one coupling;
* `TauCeti.DualFeasible.kantorovichDualValue_le_transportCost` — weak duality against the primal
  infimum;
* `TauCeti.DualFeasible.add_const_sub_const` and
  `TauCeti.kantorovichDualValue_add_const_sub_const` — feasibility and value are unchanged by
  the usual opposite additive shifts when the marginals have equal finite mass.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.1, for the Kantorovich dual constraint and weak duality.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 5.

This is Layer 2, item 1 of the optimal-transport roadmap.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c c' : X × Y → ℝ≥0∞}
  {φ : X → ℝ} {ψ : Y → ℝ}

/-- A pair of real-valued potentials is dual feasible for `c` when their split sum is bounded by
the cost. The inequality is in `EReal`, retaining both negative potential values and infinite
costs. -/
def DualFeasible (c : X × Y → ℝ≥0∞) (φ : X → ℝ) (ψ : Y → ℝ) : Prop :=
  ∀ x y, (φ x : EReal) + (ψ y : EReal) ≤ (c (x, y) : EReal)

/-- Dual feasibility in the equivalent extended-nonnegative form used by `lintegral`. Taking
`ENNReal.ofReal` loses no information because the cost is nonnegative. -/
theorem dualFeasible_iff_ofReal_add_le : DualFeasible c φ ψ ↔
    ∀ x y, ENNReal.ofReal (φ x + ψ y) ≤ c (x, y) := by
  constructor
  · intro h x y
    have hxy : ((φ x + ψ y : ℝ) : EReal) ≤ (c (x, y) : EReal) := by
      simpa only [EReal.coe_add] using h x y
    simpa only [EReal.real_coe_toENNReal, EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal hxy
  · intro h x y
    have hcast : (ENNReal.ofReal (φ x + ψ y) : EReal) ≤ (c (x, y) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 (h x y)
    have hsum : ((φ x + ψ y : ℝ) : EReal) ≤ (ENNReal.ofReal (φ x + ψ y) : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact le_max_left ((φ x + ψ y : ℝ) : EReal) 0
    simpa only [EReal.coe_add] using hsum.trans hcast

/-- A dual-feasible pair satisfies the extended-nonnegative pointwise constraint. -/
theorem DualFeasible.ofReal_add_le (h : DualFeasible c φ ψ) (x : X) (y : Y) :
    ENNReal.ofReal (φ x + ψ y) ≤ c (x, y) :=
  dualFeasible_iff_ofReal_add_le.1 h x y

/-- Dual feasibility for the extended cost attached to a nonnegative real cost is the plain
real pointwise inequality. This is the bridge from a real linear-programming dual constraint to
the canonical `TauCeti.DualFeasible` predicate. -/
theorem dualFeasible_ofReal_iff {c : X × Y → ℝ} (hc : ∀ z, 0 ≤ c z) (φ : X → ℝ) (ψ : Y → ℝ) :
    DualFeasible (fun z ↦ ENNReal.ofReal (c z)) φ ψ ↔ ∀ x y, φ x + ψ y ≤ c (x, y) := by
  rw [dualFeasible_iff_ofReal_add_le]
  exact forall_congr' fun x ↦ forall_congr' fun y ↦ ENNReal.ofReal_le_ofReal_iff (hc (x, y))

/-- Increasing the cost preserves dual feasibility. -/
theorem DualFeasible.mono_cost (h : DualFeasible c φ ψ) (hcc' : c ≤ c') :
    DualFeasible c' φ ψ :=
  fun x y ↦ (h x y).trans <| EReal.coe_ennreal_le_coe_ennreal_iff.2 (hcc' (x, y))

/-- The zero potentials are feasible for every nonnegative extended cost. -/
@[simp]
theorem dualFeasible_zero (c : X × Y → ℝ≥0∞) :
    DualFeasible c (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro x y
  simpa only [EReal.coe_zero, zero_add] using EReal.coe_ennreal_nonneg (c (x, y))

/-- Adding a constant to the first potential and subtracting it from the second preserves dual
feasibility. -/
theorem DualFeasible.add_const_sub_const (h : DualFeasible c φ ψ) (a : ℝ) :
    DualFeasible c (fun x ↦ φ x + a) (fun y ↦ ψ y - a) := by
  intro x y
  calc
    ((φ x + a : ℝ) : EReal) + ((ψ y - a : ℝ) : EReal) =
        (((φ x + a) + (ψ y - a) : ℝ) : EReal) := (EReal.coe_add _ _).symm
    _ = ((φ x + ψ y : ℝ) : EReal) := by congr 1; ring
    _ = (φ x : EReal) + (ψ y : EReal) := EReal.coe_add _ _
    _ ≤ (c (x, y) : EReal) := h x y

section Measure

variable [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}

/-- The value of a pair of Kantorovich potentials: the sum of its two marginal integrals.
The weak-duality theorems require both potentials to be integrable. -/
def kantorovichDualValue (μ : Measure X) (ν : Measure Y) (φ : X → ℝ) (ψ : Y → ℝ) : ℝ :=
  ∫ x, φ x ∂μ + ∫ y, ψ y ∂ν

/-- The dual value is the sum of the two marginal integrals. The definition's body is not
exposed, so this is the lemma downstream modules should rewrite with. -/
theorem kantorovichDualValue_def (μ : Measure X) (ν : Measure Y) (φ : X → ℝ) (ψ : Y → ℝ) :
    kantorovichDualValue μ ν φ ψ = ∫ x, φ x ∂μ + ∫ y, ψ y ∂ν := (rfl)

/-- The zero potentials have dual value zero. -/
@[simp]
theorem kantorovichDualValue_zero :
    kantorovichDualValue μ ν (fun _ ↦ 0) (fun _ ↦ 0) = 0 := by
  simp [kantorovichDualValue_def]

/-- Opposite additive shifts do not change the dual value when the first marginal is finite and
the two marginals have the same mass. -/
theorem kantorovichDualValue_add_const_sub_const [IsFiniteMeasure μ]
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) (hmass : μ Set.univ = ν Set.univ) (a : ℝ) :
    kantorovichDualValue μ ν (fun x ↦ φ x + a) (fun y ↦ ψ y - a) =
      kantorovichDualValue μ ν φ ψ := by
  let _ : IsFiniteMeasure ν := ⟨by rw [← hmass]; exact IsFiniteMeasure.measure_univ_lt_top⟩
  rw [kantorovichDualValue_def, kantorovichDualValue_def, integral_add hφ (integrable_const a),
    integral_sub hψ (integrable_const a), integral_const, integral_const]
  have hmassReal : μ.real Set.univ = ν.real Set.univ := congrArg ENNReal.toReal hmass
  rw [hmassReal]
  ring

/-- Against any coupling of the two marginals, the dual value is the integral of the split sum
`(x, y) ↦ φ x + ψ y` of the two potentials. This identity is what turns the dual value into a
statement about a single plan; it underlies both weak duality and complementary slackness. -/
theorem kantorovichDualValue_eq_integral (hπ : IsCoupling π μ ν) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) :
    kantorovichDualValue μ ν φ ψ = ∫ z, (φ z.1 + ψ z.2) ∂π := by
  rw [kantorovichDualValue_def,
    integral_add (hπ.integrable_comp_fst hφ) (hπ.integrable_comp_snd hψ),
    hπ.integral_comp_fst hφ.aestronglyMeasurable,
    hπ.integral_comp_snd hψ.aestronglyMeasurable]

section WeakDuality

private theorem real_coe_le_ennreal_coe_of_ofReal_le {x : ℝ} {a : ℝ≥0∞}
    (h : ENNReal.ofReal x ≤ a) : (x : EReal) ≤ (a : EReal) := by
  calc
    (x : EReal) ≤ (ENNReal.ofReal x : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact le_max_left (x : EReal) 0
    _ ≤ (a : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h

/-- **Weak duality against a fixed coupling, in extended-nonnegative form.** The positive part of
the dual value is bounded by the cost of every coupling. -/
theorem DualFeasible.ofReal_kantorovichDualValue_le_lintegral (h : DualFeasible c φ ψ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) (hπ : IsCoupling π μ ν) :
    ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ ∫⁻ z, c z ∂π := by
  rw [kantorovichDualValue_eq_integral hπ hφ hψ]
  exact
    (TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal
      (μ := π) (f := fun z : X × Y ↦ φ z.1 + ψ z.2)).trans <|
      lintegral_mono fun z ↦ h.ofReal_add_le z.1 z.2

/-- **Weak duality against a fixed coupling.** The real dual value is at most the possibly
infinite coupling cost, with both sides compared in `EReal`. -/
theorem DualFeasible.kantorovichDualValue_le_lintegral (h : DualFeasible c φ ψ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) (hπ : IsCoupling π μ ν) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ ((∫⁻ z, c z ∂π) : ℝ≥0∞) := by
  exact real_coe_le_ennreal_coe_of_ofReal_le <| h.ofReal_kantorovichDualValue_le_lintegral hφ hψ hπ

/-- **Kantorovich weak duality, in extended-nonnegative form.** The positive part of every
integrable feasible dual value is at most the primal transport cost. -/
theorem DualFeasible.ofReal_kantorovichDualValue_le_transportCost (h : DualFeasible c φ ψ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
  ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) ≤ transportCost c μ ν :=
  le_transportCost fun _π hπ ↦ h.ofReal_kantorovichDualValue_le_lintegral hφ hψ hπ

/-- **Kantorovich weak duality in finite real form.** If the primal value is finite, every
integrable feasible dual value is at most its real representative. -/
theorem DualFeasible.kantorovichDualValue_le_toReal_transportCost (h : DualFeasible c φ ψ)
    (hne : transportCost c μ ν ≠ ⊤) (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    kantorovichDualValue μ ν φ ψ ≤ (transportCost c μ ν).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hne).1
    (h.ofReal_kantorovichDualValue_le_transportCost hφ hψ)

/-- **Kantorovich weak duality.** Every integrable feasible dual value is at most the primal
transport cost. The comparison in `EReal` remains meaningful when the primal value is `∞`. -/
theorem DualFeasible.kantorovichDualValue_le_transportCost (h : DualFeasible c φ ψ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ (transportCost c μ ν : ℝ≥0∞) := by
  exact real_coe_le_ennreal_coe_of_ofReal_le <| h.ofReal_kantorovichDualValue_le_transportCost hφ hψ

end WeakDuality

end Measure

end TauCeti
