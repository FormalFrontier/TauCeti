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

The two-variable transport identities below assume joint measurability of the ground extended
distance, `Measurable fun z : X × X ↦ edist z.1 z.2`. This is not automatic for an abstract
`PseudoEMetricSpace` sitting on an unrelated measurable space, and it is exactly what is needed to
move the objective along a pushforward; on a second countable Borel space it is Mathlib's
`measurable_edist`. The pure finite-moment results use only almost-everywhere strong measurability
of the relevant distance sections, the two-Dirac value needs no measurability at all, and the
vanishing on the diagonal needs only a measurable diagonal, `MeasurableEq`. Nothing else about the
topology is assumed until the triangle inequality asks for a standard Borel structure, which is
what the gluing lemma consumes.

## Main definitions

* `TauCeti.wassersteinEDist p μ ν` — the infimum of `eLpNorm (fun z ↦ edist z.1 z.2) p π` over the
  couplings `π` of `μ` and `ν`.
* `TauCeti.HasFiniteMoment p μ` — the `MemLp` finite-moment condition about some basepoint.

## Main statements

* `TauCeti.wassersteinEDist_le` and `TauCeti.le_wassersteinEDist` — the two halves of the universal
  property of the infimum, with `TauCeti.wassersteinEDist_lt_iff` its order-theoretic restatement
  and `TauCeti.wassersteinEDist_eq_top_iff` the characterization of an infinite value;
* `TauCeti.wassersteinEDist_top` — the `p = ∞` characterization by coupling-wise essential
  suprema;
* `TauCeti.wassersteinEDist_self`, `TauCeti.wassersteinEDist_comm` and
  `TauCeti.wassersteinEDist_triangle` — the three axioms of an extended pseudodistance;
* `TauCeti.wassersteinEDist_mono_exponent` — monotonicity in `p` when the first marginal is a
  probability measure;
* `TauCeti.wassersteinEDist_dirac_left`, `TauCeti.wassersteinEDist_dirac_right` and
  `TauCeti.wassersteinEDist_dirac_dirac` — the unique-coupling identity
  `W_p (δ_x, ν) = ‖edist x ·‖_{L^p (ν)}`, its mirror image, and the two-Dirac value `edist x y`;
* `TauCeti.wassersteinEDist_dirac_left_le_add` and `TauCeti.wassersteinEDist_dirac_left_ne_top` —
  bounds for changing the basepoint, inside a fixed finite-distance component;
* `TauCeti.memLp_edist_iff_wassersteinEDist_dirac_ne_top` and
  `TauCeti.memLp_edist_iff_of_edist_ne_top` — the `MemLp` form of the Dirac identity and
  basepoint independence;
* `TauCeti.wassersteinEDist_rpow_eq_transportCost` and
  `TauCeti.wassersteinEDist_eq_transportCost_rpow` — for `0 < p < ∞`, the exact bridge to Layer 1's
  transport cost of `edist ^ p`, with `TauCeti.isOptimalCoupling_edist_rpow_iff` identifying the
  minimizers and `TauCeti.wassersteinEDist_one_eq_transportCost` giving the case `p = 1`;
* `TauCeti.exists_isCoupling_eLpNorm_eq_wassersteinEDist` — on a Polish metric space and for a
  finite nonzero exponent, between finite measures that admit a coupling, the infimum is attained;
* `TauCeti.wassersteinEDist_eq_zero_iff` — on a Polish metric space and for a finite nonzero
  exponent, `W_p (μ, ν) = 0` exactly when `μ = ν` if the source measure is finite, with
  `TauCeti.wassersteinEDist_top_eq_zero_iff` giving the endpoint `p = ∞` under the same
  finiteness hypothesis.

## Implementation notes

The infimum is an iterated `⨅` over plans and over proofs of `TauCeti.IsCoupling`, matching
`TauCeti.transportCost`: measures with no coupling at all — for instance two finite measures of
different total mass — get the value `∞` with no case split, and `TauCeti.wassersteinEDist_le` is
`iInf₂_le`.

The exponent is unrestricted in the definition. Only `1 ≤ p` makes the triangle inequality true,
and `TauCeti.wassersteinEDist_exponent_zero` records that the value collapses to `0` at `p = 0`
whenever the two measures are coupled at all. A theorem carries `p ≠ 0` exactly when it needs it:
the two-Dirac value, the transport-cost bridge, attainment and separation do, while the
order-theoretic API, the vanishing on the diagonal, symmetry, the one-sided Dirac identities and
`TauCeti.wassersteinEDist_mono_exponent` — monotonicity holds already from `p = 0` — do not.

The measures are raw `MeasureTheory.Measure`s, not bundled probability measures. Monotonicity in
the exponent and the Dirac identities take the `MeasureTheory.IsProbabilityMeasure` instances they
use. Attainment and separation apply to finite equal-mass measures by normalising and rescaling,
while the order-theoretic API, symmetry and the vanishing on the diagonal hold for arbitrary
measures.

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

/-- At exponent `∞`, the Wasserstein distance is the infimum of the coupling-wise essential
suprema of the ground distance. -/
theorem wassersteinEDist_top (μ ν : Measure X) :
    wassersteinEDist ∞ μ ν =
      ⨅ (π : Measure (X × X)) (_ : IsCoupling π μ ν),
        eLpNormEssSup (fun z : X × X ↦ edist z.1 z.2) π := by
  simp only [wassersteinEDist, eLpNorm_exponent_top]

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

/-- The Wasserstein distance is infinite exactly when every coupling has an infinite objective.
Measures with no coupling at all satisfy the right-hand side vacuously. -/
@[simp]
theorem wassersteinEDist_eq_top_iff :
    wassersteinEDist p μ ν = ⊤ ↔
      ∀ π, IsCoupling π μ ν → eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = ⊤ := by
  simp only [wassersteinEDist, iInf_eq_top]

/-- Measures with no coupling — by `TauCeti.exists_isCoupling_iff`, a finite measure and a measure
of a different total mass — are at Wasserstein distance `∞`. -/
theorem wassersteinEDist_eq_top_of_not_exists_isCoupling (h : ¬ ∃ π, IsCoupling π μ ν)
    (p : ℝ≥0∞) : wassersteinEDist p μ ν = ⊤ :=
  wassersteinEDist_eq_top_iff.2 fun π hπ ↦ absurd ⟨π, hπ⟩ h

/-- A finite Wasserstein distance is witnessed by a coupling. The converse fails: a coupling whose
ground distance is not `p`-integrable leaves the value `∞`. -/
theorem exists_isCoupling_of_wassersteinEDist_ne_top (h : wassersteinEDist p μ ν ≠ ⊤) :
    ∃ π, IsCoupling π μ ν := by
  obtain ⟨π, hπ, -⟩ := wassersteinEDist_lt_iff.1 h.lt_top
  exact ⟨π, hπ⟩

/-- At the exponent `0` the objective is identically `0`, so the Wasserstein distance of any two
coupled measures vanishes. Thus distance-specific results below exclude `p = 0`, although
monotonicity in the exponent remains valid when its lower exponent is `0`. -/
theorem wassersteinEDist_exponent_zero (h : ∃ π, IsCoupling π μ ν) :
    wassersteinEDist 0 μ ν = 0 := by
  obtain ⟨π, hπ⟩ := h
  simpa using wassersteinEDist_le hπ 0

/-- Scaling both measures by the same nonzero finite factor scales their Wasserstein distance by
the corresponding `L^p` factor. At `p = ∞` this factor is one. -/
theorem wassersteinEDist_smul (hc₀ : a ≠ 0) (hc_top : a ≠ ∞) :
    wassersteinEDist p (a • μ) (a • ν) =
      a ^ (1 / p).toReal * wassersteinEDist p μ ν := by
  have hc₀' : a ^ (1 / p).toReal ≠ 0 := by
    intro h
    rcases ENNReal.rpow_eq_zero_iff.mp h with ⟨ha, -⟩ | ⟨ha, -⟩
    · exact hc₀ ha
    · exact hc_top ha
  have hc_top' : a ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc_top
  apply le_antisymm
  · nth_rewrite 2 [wassersteinEDist]
    rw [ENNReal.mul_iInf_of_ne hc₀' hc_top']
    simp_rw [ENNReal.mul_iInf_of_ne hc₀' hc_top']
    refine le_iInf fun π ↦ le_iInf fun hπ ↦ ?_
    calc
      wassersteinEDist p (a • μ) (a • ν)
          ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (a • π) :=
        wassersteinEDist_le (hπ.smul a) p
      _ = a ^ (1 / p).toReal * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
        simpa only [smul_eq_mul] using
          eLpNorm_smul_measure_of_ne_zero hc₀
            (fun z : X × X ↦ edist z.1 z.2) p π
  · refine le_wassersteinEDist fun π hπ ↦ ?_
    have hπ' : IsCoupling (a⁻¹ • π) μ ν := by
      simpa only [smul_smul, ENNReal.inv_mul_cancel hc₀ hc_top, one_smul] using hπ.smul a⁻¹
    calc
      a ^ (1 / p).toReal * wassersteinEDist p μ ν
          ≤ a ^ (1 / p).toReal *
              eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (a⁻¹ • π) :=
        by simpa only [mul_comm] using
          mul_le_mul_left (wassersteinEDist_le hπ' p) (a ^ (1 / p).toReal)
      _ = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
        simpa only [smul_eq_mul, smul_smul, ENNReal.mul_inv_cancel hc₀ hc_top, one_smul]
          using (eLpNorm_smul_measure_of_ne_zero hc₀
            (fun z : X × X ↦ edist z.1 z.2) p (a⁻¹ • π)).symm

end EDist

section Measurable

variable [PseudoEMetricSpace X]

/-- The Wasserstein distance from a measure to itself vanishes: the diagonal coupling has zero
displacement almost everywhere.

Some measurability is unavoidable here — for the trivial `σ`-algebra on an unbounded metric space
every coupling has infinite objective at `p = ∞` — but a measurable diagonal is enough, and it is
an instance rather than a side condition, which is what makes this usable as a `simp` lemma. -/
@[simp]
theorem wassersteinEDist_self [MeasurableEq X] (p : ℝ≥0∞) (μ : Measure X) :
    wassersteinEDist p μ μ = 0 := by
  refine le_antisymm ((wassersteinEDist_le (isCoupling_graphPlan_id μ) p).trans_eq ?_) (zero_le ..)
  refine eLpNorm_eq_zero_of_ae_zero ?_
  filter_upwards [ae_snd_eq_graphPlan (T := (id : X → X)) (μ := μ) aemeasurable_id] with z hz
  simp [hz]

/-- **Symmetry.** Exchanging the two measures does not change their Wasserstein distance. -/
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

end Measurable

section MeasurableEDist

variable [EDist X]

/-- **Monotonicity in the exponent.** If the first marginal is a probability measure, then the
Wasserstein distance is monotone in `p`. -/
theorem wassersteinEDist_mono_exponent (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hpq : p ≤ q) (μ ν : Measure X) [IsProbabilityMeasure μ] :
    wassersteinEDist p μ ν ≤ wassersteinEDist q μ ν := by
  refine iInf₂_mono fun π hπ ↦ ?_
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  exact eLpNorm_le_eLpNorm_of_exponent_le hpq hd.aestronglyMeasurable

section Dirac

/-- A measure has finite `p`-moment if its extended distance from some basepoint belongs to
`L^p`. On an extended pseudometric space, this condition refers to one finite-distance component;
see `TauCeti.memLp_edist_iff_of_edist_ne_top` for independence within that component. -/
def HasFiniteMoment (p : ℝ≥0∞) (ν : Measure X) : Prop :=
  ∃ x : X, MemLp (fun y ↦ edist x y) p ν

/-- A measure has finite `p`-moment exactly when its distance from some basepoint belongs to
`L^p`. -/
theorem hasFiniteMoment_def :
    HasFiniteMoment p ν ↔ ∃ x : X, MemLp (fun y ↦ edist x y) p ν :=
  Iff.rfl

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

/-- The finite-moment condition about a specified basepoint is exactly finite Wasserstein distance
from its Dirac measure. -/
theorem memLp_edist_iff_wassersteinEDist_dirac_ne_top
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (x : X) (ν : Measure X)
    [IsProbabilityMeasure ν] :
    MemLp (fun y ↦ edist x y) p ν ↔ wassersteinEDist p (Measure.dirac x) ν ≠ ∞ := by
  rw [wassersteinEDist_dirac_left hd]
  exact ⟨MemLp.eLpNorm_ne_top, fun h ↦
    ⟨(hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, h.lt_top⟩⟩

/-- The existential finite-moment predicate is equivalently finite Wasserstein distance from some
Dirac measure. -/
theorem hasFiniteMoment_iff_exists_wassersteinEDist_dirac_ne_top
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (ν : Measure X)
    [IsProbabilityMeasure ν] :
    HasFiniteMoment p ν ↔ ∃ x, wassersteinEDist p (Measure.dirac x) ν ≠ ∞ := by
  simp only [HasFiniteMoment, memLp_edist_iff_wassersteinEDist_dirac_ne_top hd]

/-- **The two-Dirac value.** The only coupling of `δ x` with `δ y` is `δ (x, y)`, so the
Wasserstein distance of two Dirac measures is the ground distance of their atoms, for every
nonzero exponent. This is the acceptance check `W_p (δ_x, δ_y) = d (x, y)`.

Uniqueness of the coupling pins the infimum down without any measurability of the ground
distance, which is also what makes this a usable `simp` lemma: the one-sided Dirac identities
that would otherwise normalise its left-hand side all ask for a jointly measurable ground
distance, so they do not fire here. -/
@[simp]
theorem wassersteinEDist_dirac_dirac [MeasurableSingletonClass X] (hp : p ≠ 0) (x y : X) :
    wassersteinEDist p (Measure.dirac x) (Measure.dirac y) = edist x y := by
  have hdirac : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (Measure.dirac (x, y)) = edist x y := by
    rw [eLpNorm_dirac _ (x, y) hp, enorm_eq_self]
  refine le_antisymm ?_ (le_wassersteinEDist fun π hπ ↦ ?_)
  · exact hdirac ▸ wassersteinEDist_le (isCoupling_dirac_dirac x y) p
  · rw [hπ.eq_dirac, hdirac]

end Dirac

end MeasurableEDist

section Measurable

variable [PseudoEMetricSpace X]

section Dirac

/-- The mirror image of `TauCeti.wassersteinEDist_dirac_left`: the Wasserstein distance to a Dirac
target is the `L^p (μ)` seminorm of the ground distance to the atom. -/
@[simp]
theorem wassersteinEDist_dirac_right (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞)
    (μ : Measure X) [IsProbabilityMeasure μ] (y : X) :
    wassersteinEDist p μ (Measure.dirac y) = eLpNorm (fun x ↦ edist x y) p μ := by
  rw [wassersteinEDist_comm hd, wassersteinEDist_dirac_left hd]
  exact eLpNorm_congr_ae (.of_forall fun x ↦ edist_comm y x)

/-- Moving the basepoint of the Dirac source costs at most the ground distance between the
basepoints. See `TauCeti.memLp_edist_iff_of_edist_ne_top` for basepoint independence of the
finite-moment condition. -/
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

/-- Finite `p`-moment about a basepoint is independent of the basepoint inside a fixed
finite-distance component. On an extended pseudometric space the finite-distance hypothesis cannot
be dropped: basepoints in different components can have unrelated moment conditions. -/
theorem memLp_edist_iff_of_edist_ne_top
    {x₀ x₁ : X} {ν : Measure X}
    (h₀ : AEStronglyMeasurable (fun y ↦ edist x₀ y) ν)
    (h₁ : AEStronglyMeasurable (fun y ↦ edist x₁ y) ν)
    (hx : edist x₁ x₀ ≠ ∞) [IsFiniteMeasure ν] :
    MemLp (fun y ↦ edist x₀ y) p ν ↔ MemLp (fun y ↦ edist x₁ y) p ν := by
  constructor
  · intro h
    exact ((memLp_const_enorm (μ := ν) (p := p) (c := edist x₁ x₀) hx).add h).of_le_enorm h₁
      (.of_forall fun y ↦ by
        simpa only [Pi.add_apply, enorm_eq_self] using edist_triangle x₁ x₀ y)
  · intro h
    have hx' : edist x₀ x₁ ≠ ∞ := edist_comm x₀ x₁ ▸ hx
    exact ((memLp_const_enorm (μ := ν) (p := p) (c := edist x₀ x₁) hx').add h).of_le_enorm h₀
      (.of_forall fun y ↦ by
        simpa only [Pi.add_apply, enorm_eq_self] using edist_triangle x₀ x₁ y)

/-- Finiteness of the Wasserstein distance from a Dirac source transfers to every basepoint at
finite ground distance from the original basepoint. -/
theorem wassersteinEDist_dirac_left_ne_top (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    {x₀ x₁ : X} (hx : edist x₁ x₀ ≠ ∞) (ν : Measure X) [IsProbabilityMeasure ν]
    (h : wassersteinEDist p (Measure.dirac x₀) ν ≠ ∞) :
    wassersteinEDist p (Measure.dirac x₁) ν ≠ ∞ := by
  rw [← memLp_edist_iff_wassersteinEDist_dirac_ne_top hd] at h ⊢
  exact (memLp_edist_iff_of_edist_ne_top
    (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hx).1 h

end Dirac

section Triangle

variable [StandardBorelSpace X]

/-- **The triangle inequality.** This holds for `1 ≤ p` when the middle measure is finite and the
measurable space is standard Borel. -/
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

section MetricMoment

variable [PseudoMetricSpace X]

/-- On an ordinary pseudometric space, the real-distance and extended-distance formulations of
finite `p`-moment at a basepoint agree. -/
theorem memLp_dist_iff_memLp_edist
    {x : X} {ν : Measure X}
    (hd : AEStronglyMeasurable (fun y ↦ dist y x) ν) :
    MemLp (fun y ↦ dist y x) p ν ↔ MemLp (fun y ↦ edist x y) p ν := by
  apply memLp_congr_enorm
  · exact hd
  · exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable hd).congr
      (.of_forall fun y ↦ by simp only [edist_dist, dist_comm])
  · exact .of_forall fun y ↦ by
      simp only [edist_dist, dist_comm, enorm_eq_self]
      exact Real.enorm_eq_ofReal dist_nonneg

/-- On an ordinary pseudometric space, a finite measure with finite `p`-moment at some basepoint
has finite `p`-moment at every basepoint whose distance section is almost-everywhere strongly
measurable. -/
theorem HasFiniteMoment.memLp
    (h : HasFiniteMoment p ν) {x : X}
    (hd : AEStronglyMeasurable (fun y ↦ edist x y) ν)
    [IsFiniteMeasure ν] : MemLp (fun y ↦ edist x y) p ν := by
  obtain ⟨x₀, hx₀⟩ := h
  exact (memLp_edist_iff_of_edist_ne_top hx₀.1 hd (edist_ne_top x x₀)).1 hx₀

end MetricMoment

section Bridge

variable [EDist X]

private theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α]
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : α → ℝ≥0∞) (μ : Measure α) :
    eLpNorm f p μ ^ p.toReal = ∫⁻ a, f a ^ p.toReal ∂μ := by
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
  have key (π : Measure (X × X)) := eLpNorm_rpow_eq_lintegral hp0 hp
    (fun z : X × X ↦ edist z.1 z.2) π
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

/-- A coupling minimizes the `p`-power transport cost exactly when its `L^p` displacement realizes
the Wasserstein infimum. This connects Wasserstein minimizers to the existing optimal-coupling
API. -/
theorem isOptimalCoupling_edist_rpow_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) π μ ν ↔
      IsCoupling π μ ν ∧
        eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = wassersteinEDist p μ ν := by
  have hr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  constructor
  · intro hπ
    refine ⟨hπ.toIsCoupling, ENNReal.rpow_left_injective hr ?_⟩
    have hpow : eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π ^ p.toReal =
        wassersteinEDist p μ ν ^ p.toReal := by
      rw [eLpNorm_rpow_eq_lintegral hp0 hp, hπ.lintegral_eq,
        wassersteinEDist_rpow_eq_transportCost hp0 hp]
    exact hpow
  · rintro ⟨hπ, hval⟩
    refine ⟨hπ, ?_⟩
    rw [← eLpNorm_rpow_eq_lintegral hp0 hp, hval,
      wassersteinEDist_rpow_eq_transportCost hp0 hp]

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

/-- **Attainment.** On a Polish metric space and for a finite nonzero exponent, the infimum between
two finite measures that admit a coupling is a minimum. -/
theorem exists_isCoupling_eLpNorm_eq_wassersteinEDist (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X)
    [IsFiniteMeasure μ] (hcoup : ∃ π, IsCoupling π μ ν) :
    ∃ π, IsCoupling π μ ν ∧
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π = wassersteinEDist p μ ν := by
  obtain ⟨π₀, hπ₀⟩ := hcoup
  let _ : IsFiniteMeasure ν := ⟨by
    rw [← hπ₀.measure_univ_eq]
    exact measure_lt_top μ univ⟩
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp <| by
      rw [← hπ₀.measure_univ_eq, hμ]
      simp
    subst μ
    subst ν
    exact ⟨0, ⟨Measure.fst_zero, Measure.snd_zero⟩, by
      rw [eLpNorm_measure_zero, wassersteinEDist_self]⟩
  have hν : ν ≠ 0 := fun hν ↦ hμ <| Measure.measure_univ_eq_zero.mp <| by
    rw [hπ₀.measure_univ_eq, hν]
    simp
  let m := μ univ
  have hm0 : m ≠ 0 := by simp [m, Measure.measure_univ_eq_zero, hμ]
  have hmtop : m ≠ ∞ := by simp [m]
  let μ' := m⁻¹ • μ
  let ν' := m⁻¹ • ν
  let _ : NeZero μ := ⟨hμ⟩
  have hμ'eq : μ' = (μ univ)⁻¹ • μ := rfl
  have hν'eq : ν' = (ν univ)⁻¹ • ν := by
    simp only [ν', m, hπ₀.measure_univ_eq]
  let _ : IsProbabilityMeasure μ' := hμ'eq ▸ inferInstance
  let _ : NeZero ν := ⟨hν⟩
  let _ : IsProbabilityMeasure ν' := hν'eq ▸ inferInstance
  have hμeq : m • μ' = μ := by
    simp [μ', smul_smul, ENNReal.mul_inv_cancel hm0 hmtop]
  have hνeq : m • ν' = ν := by
    simp [ν', smul_smul, ENNReal.mul_inv_cancel hm0 hmtop]
  -- Normalise the marginals, optimise the resulting probability problem, and rescale its plan.
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_edist_rpow μ' ν' p.toReal
  obtain ⟨hπc, hval⟩ := (isOptimalCoupling_edist_rpow_iff hp0 hp).1 hπ
  have hscaled : IsCoupling (m • π) μ ν := hμeq ▸ hνeq ▸ hπc.smul m
  refine ⟨m • π, hscaled, ?_⟩
  rw [eLpNorm_smul_measure_of_ne_zero hm0, smul_eq_mul, hval, ← hμeq, ← hνeq,
    wassersteinEDist_smul hm0 hmtop]

/-- **Separation of measures.** On a Polish metric space and for a finite nonzero exponent, the
Wasserstein distance between finite measures vanishes exactly when they are equal. -/
theorem wassersteinEDist_eq_zero_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X)
    [IsFiniteMeasure μ] :
    wassersteinEDist p μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ wassersteinEDist_self p μ⟩
  obtain ⟨π₀, hπ₀⟩ :=
    exists_isCoupling_of_wassersteinEDist_ne_top (h.trans_ne ENNReal.zero_ne_top)
  obtain ⟨π, hπ, hval⟩ :=
    exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp μ ν ⟨π₀, hπ₀⟩
  have hzero : (fun z : X × X ↦ edist z.1 z.2) =ᵐ[π] 0 :=
    (eLpNorm_eq_zero_iff measurable_edist.aestronglyMeasurable hp0).1 (hval.trans h)
  have hdiag : (Prod.fst : X × X → X) =ᵐ[π] Prod.snd := by
    filter_upwards [hzero] with z hz using edist_eq_zero.1 hz
  rw [← hπ.fst_eq, ← hπ.snd_eq, Measure.fst, Measure.snd, Measure.map_congr hdiag]

/-- **Separation at the infinite exponent.** On a Polish metric space, the infinite-exponent
Wasserstein distance between finite measures vanishes exactly when they are equal. Only the first
measure is assumed finite: finite distance supplies a coupling, so the second has the same finite
mass. -/
theorem wassersteinEDist_top_eq_zero_iff (μ ν : Measure X) [IsFiniteMeasure μ] :
    wassersteinEDist ∞ μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ wassersteinEDist_self ∞ μ⟩
  obtain ⟨π₀, hπ₀⟩ :=
    exists_isCoupling_of_wassersteinEDist_ne_top (h.trans_ne ENNReal.zero_ne_top)
  let _ : IsFiniteMeasure ν := ⟨by
    rw [← hπ₀.measure_univ_eq]
    exact measure_lt_top μ univ⟩
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp <| by
      rw [← hπ₀.measure_univ_eq, hμ]
      simp
    exact hμ.trans hν.symm
  have hν : ν ≠ 0 := fun hν ↦ hμ <| Measure.measure_univ_eq_zero.mp <| by
    rw [hπ₀.measure_univ_eq, hν]
    simp
  let m := μ univ
  have hm₀ : m ≠ 0 := by simp [m, Measure.measure_univ_eq_zero, hμ]
  have hm_top : m ≠ ∞ := by simp [m]
  have hminv₀ : m⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hm_top
  have hminv_top : m⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm₀
  let μ' := m⁻¹ • μ
  let ν' := m⁻¹ • ν
  let _ : NeZero μ := ⟨hμ⟩
  have hμ'eq : μ' = (μ univ)⁻¹ • μ := rfl
  have hν'eq : ν' = (ν univ)⁻¹ • ν := by
    simp only [ν', m, hπ₀.measure_univ_eq]
  let _ : IsProbabilityMeasure μ' := hμ'eq ▸ inferInstance
  let _ : NeZero ν := ⟨hν⟩
  let _ : IsProbabilityMeasure ν' := hν'eq ▸ inferInstance
  have htop : wassersteinEDist ∞ μ' ν' = 0 := by
    calc
      wassersteinEDist ∞ μ' ν' =
          m⁻¹ ^ (1 / (∞ : ℝ≥0∞)).toReal * wassersteinEDist ∞ μ ν := by
        simpa only [μ', ν'] using
          wassersteinEDist_smul (p := ∞) (a := m⁻¹) hminv₀ hminv_top
      _ = 0 := by rw [h, mul_zero]
  have hone : wassersteinEDist 1 μ' ν' = 0 := nonpos_iff_eq_zero.mp <|
    (wassersteinEDist_mono_exponent measurable_edist le_top μ' ν').trans_eq htop
  have heq : μ' = ν' :=
    (wassersteinEDist_eq_zero_iff one_ne_zero ENNReal.one_ne_top μ' ν').1 hone
  calc
    μ = m • μ' := by
      simp [μ', smul_smul, ENNReal.mul_inv_cancel hm₀ hm_top]
    _ = m • ν' := congrArg (m • ·) heq
    _ = ν := by
      simp [ν', smul_smul, ENNReal.mul_inv_cancel hm₀ hm_top]

end Polish

end TauCeti
