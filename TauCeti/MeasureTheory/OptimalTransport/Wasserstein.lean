/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.MeasureTheory.OptimalTransport.Existence
public import TauCeti.MeasureTheory.OptimalTransport.Gluing

/-!
# The Wasserstein distance of two measures

For an exponent `p : ℝ≥0∞` the *`p`-Wasserstein distance* of two measures `μ` and `ν` on a common
space carrying an extended distance is

`W_p (μ, ν) = ⨅ π, eLpNorm (fun z ↦ edist z.1 z.2) p π`,

the infimum taken over the couplings `π` of `μ` and `ν`. This file defines
`TauCeti.wassersteinEDist` and proves the identities that make it a distance: it vanishes on the
diagonal, it is symmetric, it is monotone in the exponent, it satisfies the triangle inequality,
and — on a genuine metric space with the hypotheses under which the infimum is attained — it
separates measures.

Writing the objective as an `eLpNorm` rather than as a root of an integral is what makes the
exponent `p = ∞` a case of the definition instead of a separate one: at that endpoint the value is
the infimum of the coupling-wise essential suprema of the ground distance. For `1 ≤ p < ∞` the two
readings agree, and `TauCeti.wassersteinEDist_rpow_eq_transportCost` is the exact bridge to the
primal Kantorovich problem of `TauCeti.transportCost` for the cost `edist ^ p`.

Almost every theorem below assumes joint measurability of the ground extended distance,
`Measurable fun z : X × X ↦ edist z.1 z.2`. This is not automatic for an abstract
`PseudoEMetricSpace` sitting on an unrelated measurable space, and it is exactly what is needed to
move the objective along a pushforward; on a second countable Borel space it is Mathlib's
`measurable_edist`. Nothing else about the topology is assumed until the triangle inequality asks
for a standard Borel structure, which is what the gluing lemma consumes.

## Main definitions

* `TauCeti.wassersteinEDist p μ ν` — the infimum of `eLpNorm (fun z ↦ edist z.1 z.2) p π` over the
  couplings `π` of `μ` and `ν`.

## Main statements

* `TauCeti.wassersteinEDist_le` and `TauCeti.le_wassersteinEDist` — the two halves of the universal
  property of the infimum, with `TauCeti.wassersteinEDist_lt_iff` its order-theoretic restatement;
* `TauCeti.wassersteinEDist_self`, `TauCeti.wassersteinEDist_comm` and
  `TauCeti.wassersteinEDist_triangle` — the three axioms of an extended pseudodistance, the last
  proved by gluing two plans and applying Minkowski's inequality on the glued space;
* `TauCeti.wassersteinEDist_mono_exponent` — monotonicity in `p`, which holds because a coupling of
  two probability measures is a probability measure;
* `TauCeti.wassersteinEDist_dirac_left`, `TauCeti.wassersteinEDist_dirac_right` and
  `TauCeti.wassersteinEDist_dirac_dirac` — the unique-coupling identity
  `W_p (δ_x, ν) = ‖edist x ·‖_{L^p (ν)}`, its mirror image, and the two-Dirac value `edist x y`;
* `TauCeti.wassersteinEDist_dirac_left_le_add` and `TauCeti.wassersteinEDist_dirac_left_ne_top` —
  basepoint independence of the `p`-moment condition, inside a fixed finite-distance component;
* `TauCeti.eLpNorm_edist_rpow_eq_lintegral`, `TauCeti.wassersteinEDist_rpow_eq_transportCost` and
  `TauCeti.wassersteinEDist_eq_transportCost_rpow` — for `0 < p < ∞`, the exact bridge to Layer 1's
  transport cost of `edist ^ p`, with `TauCeti.wassersteinEDist_one_eq_transportCost` the case
  `p = 1`;
* `TauCeti.exists_isCoupling_eLpNorm_eq_wassersteinEDist` — on a Polish metric space and for a
  finite exponent the infimum is attained, so `W_p` is a minimum;
* `TauCeti.wassersteinEDist_eq_zero_iff` — on a Polish metric space and for a finite nonzero
  exponent, `W_p (μ, ν) = 0` exactly when `μ = ν`.

## Implementation notes

The infimum is an iterated `⨅` over plans and over proofs of `TauCeti.IsCoupling`, matching
`TauCeti.transportCost`: measures with no coupling at all — for instance two finite measures of
different total mass — get the value `∞` with no case split, and `TauCeti.wassersteinEDist_le` is
`iInf₂_le`.

The exponent is unrestricted in the definition. Only `1 ≤ p` makes the triangle inequality true,
and `TauCeti.wassersteinEDist_exponent_zero` records that the value collapses to `0` at `p = 0`
whenever the two measures are coupled at all; every theorem that needs `p ≠ 0` says so.

The measures are raw `MeasureTheory.Measure`s, not bundled probability measures. The theorems that
genuinely need normalisation — monotonicity in the exponent, the Dirac identities, attainment —
take the `MeasureTheory.IsProbabilityMeasure` instances they use, while the order-theoretic API,
symmetry and the vanishing on the diagonal hold for arbitrary measures.

This is Layer 3, item 1 of the optimal-transport roadmap. The basepoint-independence lemmas that
item 2 rests on are proved here, on the Dirac identity; the finite-moment spaces `P_p (X)`
themselves and the metric structure carried by an anchored finite-distance component are item 2
and are not built here.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  `W_p` is defined by the same infimum and the triangle inequality is proved by the gluing lemma.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, AMS 2003,
  §7.1, Theorem 7.3 (the Wasserstein distances are distances).
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p q : ℝ≥0∞} {a : ℝ≥0∞}

section EDist

variable [EDist X] {μ ν : Measure X} {π : Measure (X × X)}

/-- The **`p`-Wasserstein distance** of `μ` and `ν`: the infimum, over the couplings `π` of `μ`
and `ν`, of the `L^p (π)` seminorm of the ground extended distance `fun z ↦ edist z.1 z.2`.

It is `∞` when `μ` and `ν` have no coupling at all. At `p = ∞` the objective is the
`π`-essential supremum of the ground distance, by Mathlib's `MeasureTheory.eLpNorm`
convention. -/
def wassersteinEDist (p : ℝ≥0∞) (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × X)) (_ : IsCoupling π μ ν), eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π

/-- The Wasserstein distance as the infimum over all feasible plans. -/
theorem wassersteinEDist_def :
    wassersteinEDist p μ ν =
      ⨅ (π : Measure (X × X)) (_ : IsCoupling π μ ν),
        eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π :=
  (rfl)

/-- Every coupling bounds the Wasserstein distance from above. -/
theorem wassersteinEDist_le (hπ : IsCoupling π μ ν) (p : ℝ≥0∞) :
    wassersteinEDist p μ ν ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the Wasserstein distance from below. -/
theorem le_wassersteinEDist
    (h : ∀ π, IsCoupling π μ ν → a ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π) :
    a ≤ wassersteinEDist p μ ν :=
  le_iInf₂ h

/-- The Wasserstein distance is below a threshold exactly when some coupling is. -/
theorem wassersteinEDist_lt_iff :
    wassersteinEDist p μ ν < a ↔
      ∃ π, IsCoupling π μ ν ∧ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π < a := by
  simp only [wassersteinEDist, iInf_lt_iff, exists_prop]

/-- Measures with no coupling — by `TauCeti.exists_isCoupling_iff`, a finite measure and a measure
of a different total mass — are at Wasserstein distance `∞`. -/
theorem wassersteinEDist_eq_top_of_not_exists_isCoupling (h : ¬ ∃ π, IsCoupling π μ ν)
    (p : ℝ≥0∞) : wassersteinEDist p μ ν = ⊤ :=
  eq_top_iff.2 <| le_wassersteinEDist fun π hπ ↦ absurd ⟨π, hπ⟩ h

/-- A finite Wasserstein distance is witnessed by a coupling. The converse fails: a coupling whose
ground distance is not `p`-integrable leaves the value `∞`. -/
theorem exists_isCoupling_of_wassersteinEDist_ne_top (h : wassersteinEDist p μ ν ≠ ⊤) :
    ∃ π, IsCoupling π μ ν := by
  obtain ⟨π, hπ, -⟩ := wassersteinEDist_lt_iff.1 h.lt_top
  exact ⟨π, hπ⟩

/-- At the exponent `0` the objective is identically `0`, so the Wasserstein distance of any two
coupled measures vanishes. This is why every theorem below that compares exponents or that treats
`W_p` as a distance excludes `p = 0`. -/
theorem wassersteinEDist_exponent_zero (h : ∃ π, IsCoupling π μ ν) :
    wassersteinEDist 0 μ ν = 0 := by
  obtain ⟨π, hπ⟩ := h
  simpa using wassersteinEDist_le hπ 0

end EDist

section Measurable

variable [PseudoEMetricSpace X]

/-- Vanishing on the diagonal: the diagonal plan `TauCeti.graphPlan id μ` couples `μ` with itself
and gives the ground distance the value `0` everywhere on its support. -/
@[simp]
theorem wassersteinEDist_self (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞)
    (μ : Measure X) : wassersteinEDist p μ μ = 0 := by
  refine le_antisymm ?_ (zero_le ..)
  calc wassersteinEDist p μ μ
      ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (graphPlan id μ) :=
        wassersteinEDist_le (isCoupling_graphPlan_id μ) p
    _ = eLpNorm (fun _ : X ↦ (0 : ℝ≥0∞)) p μ := by
        rw [graphPlan_def, eLpNorm_map_measure hd.aestronglyMeasurable (by fun_prop)]
        simp [Function.comp_def]
    _ = 0 := eLpNorm_zero

/-- **Symmetry.** Exchanging the two coordinates of a plan is a bijection between the couplings of
`μ` with `ν` and those of `ν` with `μ`, and it leaves the objective unchanged because `edist`
is symmetric. -/
theorem wassersteinEDist_comm (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞)
    (μ ν : Measure X) : wassersteinEDist p μ ν = wassersteinEDist p ν μ := by
  have key : ∀ (μ ν : Measure X), wassersteinEDist p ν μ ≤ wassersteinEDist p μ ν := by
    intro μ ν
    refine le_wassersteinEDist fun π hπ ↦ ?_
    calc wassersteinEDist p ν μ
        ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (π.map Prod.swap) :=
          wassersteinEDist_le (isCoupling_map_swap_iff.2 hπ) p
      _ = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
          rw [eLpNorm_map_measure hd.aestronglyMeasurable measurable_swap.aemeasurable]
          exact eLpNorm_congr_ae (.of_forall fun z ↦ edist_comm z.2 z.1)
  exact le_antisymm (key ν μ) (key μ ν)

/-- **Monotonicity in the exponent.** A coupling of two probability measures is a probability
measure, so Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le` applies plan by plan. -/
theorem wassersteinEDist_mono_exponent (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hpq : p ≤ q) (μ ν : Measure X) [IsProbabilityMeasure μ] :
    wassersteinEDist p μ ν ≤ wassersteinEDist q μ ν := by
  refine iInf₂_mono fun π hπ ↦ ?_
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  exact eLpNorm_le_eLpNorm_of_exponent_le hpq hd.aestronglyMeasurable

section Dirac

/-- **The unique-coupling identity.** A Dirac source has exactly one coupling with each
probability target, so the Wasserstein distance from `δ x` is the `L^p (ν)` seminorm of the ground
distance to `x`. This is the identity that later identifies the finite-moment space `P_p (X)` with
the finite-distance component of a Dirac law. -/
@[simp]
theorem wassersteinEDist_dirac_left (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞)
    (x : X) (ν : Measure X) [IsProbabilityMeasure ν] :
    wassersteinEDist p (Measure.dirac x) ν = eLpNorm (fun y ↦ edist x y) p ν := by
  have hmap : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (ν.map (Prod.mk x))
      = eLpNorm (fun y ↦ edist x y) p ν := by
    rw [eLpNorm_map_measure hd.aestronglyMeasurable measurable_prodMk_left.aemeasurable]
    rfl
  refine le_antisymm ?_ (le_wassersteinEDist fun π hπ ↦ ?_)
  · exact hmap ▸ wassersteinEDist_le (isCoupling_map_prodMk x ν) p
  · rw [hπ.eq_map_prodMk, hmap]

/-- The mirror image of `TauCeti.wassersteinEDist_dirac_left`: the Wasserstein distance to a Dirac
target is the `L^p (μ)` seminorm of the ground distance to the atom. -/
@[simp]
theorem wassersteinEDist_dirac_right (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞)
    (μ : Measure X) [IsProbabilityMeasure μ] (y : X) :
    wassersteinEDist p μ (Measure.dirac y) = eLpNorm (fun x ↦ edist x y) p μ := by
  rw [wassersteinEDist_comm hd, wassersteinEDist_dirac_left hd]
  exact eLpNorm_congr_ae (.of_forall fun x ↦ edist_comm y x)

/-- **The two-Dirac value.** The only coupling of `δ x` with `δ y` is `δ (x, y)`, so the
Wasserstein distance of two Dirac measures is the ground distance of their atoms, for every
nonzero exponent. This is the acceptance check `W_p (δ_x, δ_y) = d (x, y)`.

Unlike the two one-sided Dirac identities this is not a `simp` lemma: its left-hand side is
already normalised by `TauCeti.wassersteinEDist_dirac_right` followed by Mathlib's
`MeasureTheory.eLpNorm_dirac`, and the `simpNF` linter rejects the redundant tag. -/
theorem wassersteinEDist_dirac_dirac [MeasurableSingletonClass X]
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : p ≠ 0) (x y : X) :
    wassersteinEDist p (Measure.dirac x) (Measure.dirac y) = edist x y := by
  rw [wassersteinEDist_dirac_left hd, eLpNorm_dirac _ y hp, enorm_eq_self]

/-- **Basepoint independence of the `p`-moment.** By `TauCeti.wassersteinEDist_dirac_left` the
Wasserstein distance from a Dirac law is the `p`-th moment of `ν` about its atom, and moving the
basepoint costs at most the ground distance between the two basepoints: the constant function is
in every `L^p` of a probability measure, and Minkowski's inequality does the rest. -/
theorem wassersteinEDist_dirac_left_le_add (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp : 1 ≤ p) (x₀ x₁ : X) (ν : Measure X) [IsProbabilityMeasure ν] :
    wassersteinEDist p (Measure.dirac x₁) ν
      ≤ edist x₁ x₀ + wassersteinEDist p (Measure.dirac x₀) ν := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hconst : eLpNorm (fun _ : X ↦ edist x₁ x₀) p ν = edist x₁ x₀ := by
    rw [eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero ν)]
    simp
  rw [wassersteinEDist_dirac_left hd, wassersteinEDist_dirac_left hd, ← hconst]
  calc eLpNorm (fun y ↦ edist x₁ y) p ν
      ≤ eLpNorm ((fun _ : X ↦ edist x₁ x₀) + fun y ↦ edist x₀ y) p ν :=
        eLpNorm_mono_enorm fun y ↦ by simpa using edist_triangle x₁ x₀ y
    _ ≤ eLpNorm (fun _ : X ↦ edist x₁ x₀) p ν + eLpNorm (fun y ↦ edist x₀ y) p ν :=
        eLpNorm_add_le aestronglyMeasurable_const
          (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hp

/-- A finite `p`-moment about one basepoint is a finite `p`-moment about any basepoint at finite
ground distance from it. On an extended pseudometric space the finite-distance hypothesis cannot be
dropped: two basepoints in different components have unrelated moment conditions, which is why the
guardrail is stated rather than an unconditional equivalence. -/
theorem wassersteinEDist_dirac_left_ne_top (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp : 1 ≤ p) {x₀ x₁ : X} (hx : edist x₁ x₀ ≠ ∞) (ν : Measure X) [IsProbabilityMeasure ν]
    (h : wassersteinEDist p (Measure.dirac x₀) ν ≠ ∞) :
    wassersteinEDist p (Measure.dirac x₁) ν ≠ ∞ :=
  ((wassersteinEDist_dirac_left_le_add hd hp x₀ x₁ ν).trans_lt
    (ENNReal.add_lt_top.2 ⟨hx.lt_top, h.lt_top⟩)).ne

end Dirac

section Triangle

variable [StandardBorelSpace X]

/-- **The triangle inequality.** Two plans sharing their middle marginal are glued to a joint law
on `X × X × X`; its outer marginal couples `μ` with `ρ`, the ground distance on the outer pair is
dominated by the sum of the two consecutive ones, and Minkowski's inequality — available exactly
because `1 ≤ p` — separates the two terms.

Only the middle measure is asked to be finite, and only so that the plan being disintegrated is;
if either of the two other pairs has no coupling the right-hand side is `∞` and there is nothing
to prove. -/
theorem wassersteinEDist_triangle (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (μ : Measure X) (ν : Measure X) [IsFiniteMeasure ν] (ρ : Measure X) :
    wassersteinEDist p μ ρ ≤ wassersteinEDist p μ ν + wassersteinEDist p ν ρ := by
  refine ENNReal.le_iInf₂_add_iInf₂ fun π hπ σ hσ ↦ ?_
  have : IsFiniteMeasure σ := hσ.isFiniteMeasure
  obtain ⟨γ, hγπ, hγσ⟩ := Measure.exists_glue_of_standardBorel_right π σ (by
    rw [hπ.snd_eq, hσ.fst_eq])
  have hcoup : IsCoupling (γ.map (Prod.map id Prod.snd)) μ ρ :=
    ⟨(Measure.fst_map_prodMap_id_snd hγπ).trans hπ.fst_eq,
      (Measure.snd_map_prodMap_id_snd hγσ).trans hσ.snd_eq⟩
  refine (wassersteinEDist_le hcoup p).trans ?_
  have houter : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (γ.map (Prod.map id Prod.snd))
      = eLpNorm (fun w : X × X × X ↦ edist w.1 w.2.2) p γ := by
    rw [eLpNorm_map_measure hd.aestronglyMeasurable
      (measurable_id.prodMap measurable_snd).aemeasurable]
    rfl
  have hfirst : eLpNorm (fun w : X × X × X ↦ edist w.1 w.2.1) p γ
      = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
    rw [← hγπ, eLpNorm_map_measure hd.aestronglyMeasurable
      (measurable_id.prodMap measurable_fst).aemeasurable]
    rfl
  have hsecond : eLpNorm (fun w : X × X × X ↦ edist w.2.1 w.2.2) p γ
      = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p σ := by
    rw [← hγσ, Measure.snd, eLpNorm_map_measure hd.aestronglyMeasurable
      measurable_snd.aemeasurable]
    rfl
  rw [houter, ← hfirst, ← hsecond]
  calc eLpNorm (fun w : X × X × X ↦ edist w.1 w.2.2) p γ
      ≤ eLpNorm ((fun w : X × X × X ↦ edist w.1 w.2.1)
          + fun w : X × X × X ↦ edist w.2.1 w.2.2) p γ :=
        eLpNorm_mono_enorm fun w ↦ by
          simpa using edist_triangle w.1 w.2.1 w.2.2
    _ ≤ eLpNorm (fun w : X × X × X ↦ edist w.1 w.2.1) p γ
          + eLpNorm (fun w : X × X × X ↦ edist w.2.1 w.2.2) p γ :=
        eLpNorm_add_le (hd.comp (measurable_id.prodMap measurable_fst)).aestronglyMeasurable
          (hd.comp measurable_snd).aestronglyMeasurable hp

end Triangle

end Measurable

section Bridge

variable [PseudoEMetricSpace X]

/-- The objective of a fixed plan, raised to the power `p`, is the integral of `edist ^ p`: this
is the pointwise form of the bridge between the `L^p` seminorm and the primal cost, valid for
every finite nonzero exponent. -/
theorem eLpNorm_edist_rpow_eq_lintegral (hp0 : p ≠ 0) (hp : p ≠ ∞) (π : Measure (X × X)) :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π ^ p.toReal
      = ∫⁻ z, edist z.1 z.2 ^ p.toReal ∂π := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]
  simp

/-- **The bridge to the primal Kantorovich problem.** For a finite nonzero exponent the `p`-th
power of the Wasserstein distance is the transport cost of the cost `edist ^ p`, so the two
infima — one of `L^p` seminorms, one of integrals — are the same optimisation problem. -/
theorem wassersteinEDist_rpow_eq_transportCost (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X) :
    wassersteinEDist p μ ν ^ p.toReal
      = transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have key := eLpNorm_edist_rpow_eq_lintegral (X := X) hp0 hp
  refine le_antisymm (le_transportCost fun π hπ ↦ ?_) ?_
  · rw [← key π]
    exact ENNReal.rpow_le_rpow (wassersteinEDist_le hπ p) hr.le
  · have hle : transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν ^ (1 / p.toReal)
        ≤ wassersteinEDist p μ ν := by
      refine le_wassersteinEDist fun π hπ ↦ ?_
      calc transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν ^ (1 / p.toReal)
          ≤ (eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π ^ p.toReal) ^ (1 / p.toReal) := by
            refine ENNReal.rpow_le_rpow ?_ (by positivity)
            rw [key π]
            exact transportCost_le_lintegral hπ _
        _ = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
    calc transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν
        = (transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν ^ (1 / p.toReal))
            ^ p.toReal := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
      _ ≤ wassersteinEDist p μ ν ^ p.toReal := ENNReal.rpow_le_rpow hle hr.le

/-- The root form of `TauCeti.wassersteinEDist_rpow_eq_transportCost`: for a finite nonzero
exponent the Wasserstein distance is the `p`-th root of the transport cost of `edist ^ p`. -/
theorem wassersteinEDist_eq_transportCost_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X) :
    wassersteinEDist p μ ν
      = transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) μ ν ^ (1 / p.toReal) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← wassersteinEDist_rpow_eq_transportCost hp0 hp, ← ENNReal.rpow_mul,
    mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- At the exponent `1` the Wasserstein distance is the transport cost of the ground distance
itself: the Kantorovich–Rubinstein problem is the primal problem for the cost `edist`. -/
theorem wassersteinEDist_one_eq_transportCost (μ ν : Measure X) :
    wassersteinEDist 1 μ ν = transportCost (fun z : X × X ↦ edist z.1 z.2) μ ν := by
  simpa using wassersteinEDist_eq_transportCost_rpow (X := X) one_ne_zero ENNReal.one_ne_top μ ν

end Bridge

section Polish

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]

/-- **Attainment.** On a Polish metric space and for a finite nonzero exponent the infimum
defining the Wasserstein distance is a minimum: some coupling realises it. This is the primal
attainment of `TauCeti.exists_isOptimalCoupling_edist_rpow`, transported across the bridge
`TauCeti.wassersteinEDist_rpow_eq_transportCost`. -/
theorem exists_isCoupling_eLpNorm_eq_wassersteinEDist (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = wassersteinEDist p μ ν := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_edist_rpow μ ν p.toReal
  have hpow : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π ^ p.toReal
      = wassersteinEDist p μ ν ^ p.toReal := by
    rw [eLpNorm_edist_rpow_eq_lintegral hp0 hp, wassersteinEDist_rpow_eq_transportCost hp0 hp,
      hπ.lintegral_eq]
  exact ⟨π, hπ.toIsCoupling, ENNReal.rpow_left_injective hr.ne' hpow⟩

/-- **Separation of measures.** On a Polish metric space and for a finite nonzero exponent the
Wasserstein distance vanishes exactly on equal measures: an optimal plan of zero cost is carried
by the diagonal, and its two marginals are then the same measure. -/
theorem wassersteinEDist_eq_zero_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ wassersteinEDist_self measurable_edist p μ⟩
  obtain ⟨π, hπ, hval⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp μ ν
  have hzero : (fun z : X × X ↦ edist z.1 z.2) =ᵐ[π] 0 :=
    (eLpNorm_eq_zero_iff measurable_edist.aestronglyMeasurable hp0).1 (hval.trans h)
  have hdiag : (Prod.fst : X × X → X) =ᵐ[π] Prod.snd := by
    filter_upwards [hzero] with z hz using edist_eq_zero.1 hz
  rw [← hπ.fst_eq, ← hπ.snd_eq, Measure.fst, Measure.snd, Measure.map_congr hdiag]

end Polish

end TauCeti
