/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Wasserstein distance under pushforward

A Lipschitz map sends every coupling to a coupling of the pushforward measures, while increasing
the displacement of each coupled pair by at most its Lipschitz constant. Consequently pushforward
is Lipschitz for every Wasserstein exponent, including the essential-supremum endpoint.

This file proves the estimate first for the objective of a specified coupling and then for the
infimum over all couplings. The latter needs no hypothesis on the measures once the Lipschitz
constant is nonzero; for a zero constant it is stated for measures known to admit a coupling, a
condition the probability-measure specialization discharges with the independent coupling.
It also records preservation of finite moments, so the same map acts on finite-moment Wasserstein
spaces.

## Main statements

* `TauCeti.wassersteinEDist_map_le_mul_eLpNorm` bounds the Wasserstein distance of two
  pushforwards by the Lipschitz constant times the objective of a specified source coupling.
* `TauCeti.wassersteinEDist_map_le_mul_of_ne_zero` gives the pushforward estimate for arbitrary
  measures and a nonzero Lipschitz constant.
* `TauCeti.wassersteinEDist_map_le_mul_of_exists_isCoupling` gives the pushforward estimate for any
  two measures admitting a coupling.
* `TauCeti.wassersteinEDist_map_le_mul` is the probability-measure specialization.
* `TauCeti.HasFiniteMoment.map` shows that Lipschitz pushforward preserves finite moments.
* `TauCeti.wassersteinEDist_map_eq` gives invariance under a measurable isometric equivalence.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {p : ℝ≥0∞} {K : ℝ≥0} {f : X → Y} {μ ν : Measure X} {π : Measure (X × X)}

/-- The image of a specified coupling under a Lipschitz map bounds the Wasserstein distance of the
pushforward measures. This is the coupling-level estimate from which functoriality follows. -/
theorem wassersteinEDist_map_le_mul_eLpNorm
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) (hf : Measurable f)
    (hLip : LipschitzWith K f) (hπ : IsCoupling π μ ν) :
    wassersteinEDist p (μ.map f) (ν.map f) ≤
      K * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
  calc
    wassersteinEDist p (μ.map f) (ν.map f)
        ≤ eLpNorm (fun z : Y × Y ↦ edist z.1 z.2) p (π.map (Prod.map f f)) :=
      wassersteinEDist_le (hπ.map hf hf) p
    _ = eLpNorm (fun z : X × X ↦ edist (f z.1) (f z.2)) p π := by
      have hcomp : (fun z : Y × Y ↦ edist z.1 z.2) ∘ Prod.map f f
          = fun z : X × X ↦ edist (f z.1) (f z.2) := by
        funext z
        simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
      rw [eLpNorm_map_measure hdY.aestronglyMeasurable (hf.prodMap hf).aemeasurable, hcomp]
    _ ≤ K * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
      apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      exact .of_forall fun z ↦ by
        simpa only [enorm_eq_self, ENNReal.smul_def] using hLip.edist_le_mul z.1 z.2

/-- A Lipschitz map contracts Wasserstein distance up to a nonzero Lipschitz constant, for
arbitrary measures. Nothing is assumed about `μ` and `ν`: if they admit no coupling their distance
is `⊤`, and multiplying by a nonzero constant leaves the bound at `⊤`. -/
theorem wassersteinEDist_map_le_mul_of_ne_zero
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) (hf : Measurable f)
    (hLip : LipschitzWith K f) (hK : K ≠ 0) (μ ν : Measure X) :
    wassersteinEDist p (μ.map f) (ν.map f) ≤ K * wassersteinEDist p μ ν := by
  by_contra hbound
  have hlt : K * wassersteinEDist p μ ν < wassersteinEDist p (μ.map f) (ν.map f) :=
    lt_of_not_ge hbound
  have hsource : wassersteinEDist p μ ν <
      wassersteinEDist p (μ.map f) (ν.map f) / K := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.coe_ne_zero.2 hK))
      (Or.inl ENNReal.coe_ne_top)).2
    simpa only [mul_comm] using hlt
  obtain ⟨π, hπ, hπlt⟩ := wassersteinEDist_lt_iff.1 hsource
  have hmap := wassersteinEDist_map_le_mul_eLpNorm (p := p) hdY hf hLip hπ
  have hobj : K * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π <
      wassersteinEDist p (μ.map f) (ν.map f) := by
    simpa only [mul_comm] using ENNReal.mul_lt_of_lt_div hπlt
  exact (not_le_of_gt hobj) hmap

/-- A Lipschitz map contracts Wasserstein distance up to its Lipschitz constant, for arbitrary
measures admitting a coupling. The existence hypothesis is needed only when the Lipschitz
constant is zero: with Mathlib's extended-nonnegative-real convention, `0 * ∞ = 0`, whereas
measures of unequal mass have no coupling and remain at infinite distance after pushforward. -/
theorem wassersteinEDist_map_le_mul_of_exists_isCoupling
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) (hf : Measurable f)
    (hLip : LipschitzWith K f) (hμν : ∃ π, IsCoupling π μ ν) :
    wassersteinEDist p (μ.map f) (ν.map f) ≤ K * wassersteinEDist p μ ν := by
  by_cases hK : K = 0
  · obtain ⟨π, hπ⟩ := hμν
    refine (wassersteinEDist_map_le_mul_eLpNorm hdY hf hLip hπ).trans_eq ?_
    simp only [hK, ENNReal.coe_zero, zero_mul]
  · exact wassersteinEDist_map_le_mul_of_ne_zero hdY hf hLip hK μ ν

/-- Pushforward by a `K`-Lipschitz measurable map is `K`-Lipschitz for the `p`-Wasserstein
distance between probability measures. The statement includes `K = 0`, `p = 0`, and `p = ∞`. -/
theorem wassersteinEDist_map_le_mul
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) (hf : Measurable f)
    (hLip : LipschitzWith K f) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    wassersteinEDist p (μ.map f) (ν.map f) ≤ K * wassersteinEDist p μ ν :=
  wassersteinEDist_map_le_mul_of_exists_isCoupling hdY hf hLip ⟨μ.prod ν, isCoupling_prod μ ν⟩

/-- A Lipschitz measurable map sends a measure with finite `p`-moment to another measure with
finite `p`-moment. -/
theorem HasFiniteMoment.map (hμ : HasFiniteMoment p μ)
    (hdY : ∀ y : Y, Measurable fun z : Y ↦ edist y z) (hf : Measurable f)
    (hLip : LipschitzWith K f) : HasFiniteMoment p (μ.map f) := by
  rw [hasFiniteMoment_def] at hμ ⊢
  obtain ⟨x, hx⟩ := hμ
  refine ⟨f x, ?_⟩
  have hdist : AEStronglyMeasurable (fun y : Y ↦ edist (f x) y) (μ.map f) :=
    (hdY (f x)).aestronglyMeasurable
  rw [memLp_map_measure_iff hdist hf.aemeasurable]
  apply hx.of_enorm_le_mul
  · exact ((hdY (f x)).comp hf).aestronglyMeasurable
  · exact .of_forall fun y ↦ by
      simpa only [Function.comp_apply, enorm_eq_self] using hLip.edist_le_mul x y

section Isometry

variable {e : X ≃ᵐ Y}

/-- A measurable isometric equivalence preserves Wasserstein distance. -/
theorem wassersteinEDist_map_eq
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) (he : Isometry e)
    (μ ν : Measure X) :
    wassersteinEDist p (μ.map e) (ν.map e) = wassersteinEDist p μ ν := by
  let ei : X ≃ᵢ Y := { e.toEquiv with isometry_toFun := he }
  have hdX : Measurable fun z : X × X ↦ edist z.1 z.2 := by
    have hdist_comp : (fun z : Y × Y ↦ edist z.1 z.2) ∘ Prod.map e e =
        fun z : X × X ↦ edist z.1 z.2 := by
      funext z
      exact he.edist_eq z.1 z.2
    rw [← hdist_comp]
    exact hdY.comp (e.measurable.prodMap e.measurable)
  have hforward : wassersteinEDist p (μ.map e) (ν.map e) ≤ wassersteinEDist p μ ν := by
    have h := wassersteinEDist_map_le_mul_of_ne_zero (p := p) hdY e.measurable
      ei.isometry.lipschitzWith one_ne_zero μ ν
    simpa only [ENNReal.coe_one, one_mul] using h
  have hbackward : wassersteinEDist p ((μ.map e).map e.symm) ((ν.map e).map e.symm) ≤
      wassersteinEDist p (μ.map e) (ν.map e) := by
    have h := wassersteinEDist_map_le_mul_of_ne_zero (p := p) hdX e.symm.measurable
      ei.symm.isometry.lipschitzWith one_ne_zero (μ.map e) (ν.map e)
    simpa only [ENNReal.coe_one, one_mul] using h
  refine le_antisymm hforward ?_
  calc
    wassersteinEDist p μ ν =
        wassersteinEDist p ((μ.map e).map e.symm) ((ν.map e).map e.symm) := by
      rw [e.map_symm_map, e.map_symm_map]
    _ ≤ wassersteinEDist p (μ.map e) (ν.map e) := hbackward

/-- A measurable isometric equivalence preserves the finite-moment condition. -/
theorem hasFiniteMoment_map_iff
    (hdY : ∀ y : Y, Measurable fun z : Y ↦ edist y z) (he : Isometry e) :
    HasFiniteMoment p (μ.map e) ↔ HasFiniteMoment p μ := by
  let ei : X ≃ᵢ Y := { e.toEquiv with isometry_toFun := he }
  have hdX : ∀ x : X, Measurable fun z : X ↦ edist x z := fun x ↦ by
    have hdist_comp : (fun y : Y ↦ edist (e x) y) ∘ e =
        fun z : X ↦ edist x z := by
      funext z
      exact he.edist_eq x z
    rw [← hdist_comp]
    exact (hdY (e x)).comp e.measurable
  refine ⟨fun h ↦ ?_, fun h ↦ h.map hdY e.measurable ei.isometry.lipschitzWith⟩
  have hm : (μ.map e).map e.symm = μ := e.map_symm_map
  rw [← hm]
  exact h.map hdX e.symm.measurable ei.symm.isometry.lipschitzWith

end Isometry

end TauCeti
