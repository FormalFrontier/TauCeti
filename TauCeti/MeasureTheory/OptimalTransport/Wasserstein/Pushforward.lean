/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

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
* `TauCeti.WassersteinSpace.map` lifts pushforward to finite-moment probability measures.
* `TauCeti.WassersteinSpace.lipschitzWith_map` gives the induced Lipschitz map between
  Wasserstein spaces.
* `TauCeti.WassersteinSpace.mapIsometryEquiv` lifts measurable isometric equivalences.
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

universe u v w

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {p : ℝ≥0∞} {K : ℝ≥0} {f : X → Y} {μ ν : Measure X} {π : Measure (X × X)}

section PseudoEMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

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

namespace WassersteinSpace

/-- Pushforward by a measurable Lipschitz map, as a map between finite-moment Wasserstein
spaces. -/
noncomputable def map (f : X → Y)
    (hdY : ∀ y : Y, Measurable fun z : Y ↦ edist y z) (hf : Measurable f)
    (hLip : LipschitzWith K f) (mu : WassersteinSpace p X) : WassersteinSpace p Y :=
  .mk ((mu : ProbabilityMeasure X).map f) <| by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      (hasFiniteMoment mu).map hdY hf hLip

/-- The probability measure underlying a Wasserstein-space pushforward is the pushforward of the
underlying probability measure. -/
@[simp]
theorem coe_map (f : X → Y) (hdY : ∀ y : Y, Measurable fun z : Y ↦ edist y z)
    (hf : Measurable f) (hLip : LipschitzWith K f) (mu : WassersteinSpace p X) :
    (map f hdY hf hLip mu : ProbabilityMeasure Y) = (mu : ProbabilityMeasure X).map f :=
  by rw [map, coe_mk]

/-- Pushforward by the identity map is the identity on finite-moment Wasserstein spaces. -/
@[simp]
theorem map_id (hdX : ∀ x : X, Measurable fun z : X ↦ edist x z)
    (mu : WassersteinSpace p X) :
    map id hdX measurable_id LipschitzWith.id mu = mu := by
  apply ext
  rw [coe_map]
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_id]

/-- Pushforward along a composition is the composition of the pushforwards. -/
theorem map_comp {Z : Type w} [MeasurableSpace Z] [PseudoEMetricSpace Z] {g : Y → Z} {K' : ℝ≥0}
    (hdY : ∀ y : Y, Measurable fun z : Y ↦ edist y z)
    (hdZ : ∀ z : Z, Measurable fun w : Z ↦ edist z w)
    (hf : Measurable f) (hLip : LipschitzWith K f)
    (hg : Measurable g) (hgLip : LipschitzWith K' g)
    (mu : WassersteinSpace p X) :
    map (g ∘ f) hdZ (hg.comp hf) (hgLip.comp hLip) mu =
      map g hdZ hg hgLip (map f hdY hf hLip mu) := by
  apply ext
  rw [coe_map, coe_map, coe_map]
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  exact (Measure.map_map hg hf).symm

end WassersteinSpace

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

end PseudoEMetric

namespace WassersteinSpace

variable [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] [Fact (1 ≤ p)]

/-- Pushforward by a measurable `K`-Lipschitz map is `K`-Lipschitz between finite-moment
Wasserstein spaces. -/
theorem lipschitzWith_map (hf : Measurable f) (hLip : LipschitzWith K f) :
    LipschitzWith K (map (p := p) f (fun _ ↦ measurable_edist_right) hf hLip) := by
  intro mu nu
  simpa only [edist_def, coe_map, ProbabilityMeasure.toMeasure_map] using
    wassersteinEDist_map_le_mul (p := p) measurable_edist hf hLip
      ((mu : ProbabilityMeasure X) : Measure X) ((nu : ProbabilityMeasure X) : Measure X)

/-- A measurable isometric equivalence of ground spaces induces an isometric equivalence of their
finite-moment Wasserstein spaces. -/
noncomputable def mapIsometryEquiv (e : X ≃ᵐ Y) (he : Isometry e) :
    WassersteinSpace p X ≃ᵢ WassersteinSpace p Y := by
  have he_symm : Isometry e.symm := he.right_inv e.right_inv
  refine
    { toFun := map (p := p) e (fun _ ↦ measurable_edist_right) e.measurable
        he.lipschitzWith
      invFun := map (p := p) e.symm (fun _ ↦ measurable_edist_right) e.symm.measurable
        he_symm.lipschitzWith
      left_inv := ?_
      right_inv := ?_
      isometry_toFun := ?_ }
  · intro mu
    apply ext
    rw [coe_map, coe_map]
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map] using
      (e.map_symm_map (μ := ((mu : ProbabilityMeasure X) : Measure X)))
  · intro mu
    apply ext
    rw [coe_map, coe_map]
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map] using
      (e.map_map_symm (ν := ((mu : ProbabilityMeasure Y) : Measure Y)))
  · intro mu nu
    simpa only [edist_def, coe_map, ProbabilityMeasure.toMeasure_map] using
      wassersteinEDist_map_eq (p := p) measurable_edist he
        ((mu : ProbabilityMeasure X) : Measure X) ((nu : ProbabilityMeasure X) : Measure X)

/-- The isometric equivalence induced by a measurable isometric equivalence acts by pushforward
along that equivalence. -/
@[simp]
theorem mapIsometryEquiv_apply (e : X ≃ᵐ Y) (he : Isometry e) (mu : WassersteinSpace p X) :
    mapIsometryEquiv (p := p) e he mu =
      map e (fun _ ↦ measurable_edist_right) e.measurable he.lipschitzWith mu :=
  (rfl)

/-- The inverse of the induced isometric equivalence acts by pushforward along the inverse
equivalence. -/
@[simp]
theorem mapIsometryEquiv_symm_apply (e : X ≃ᵐ Y) (he : Isometry e) (nu : WassersteinSpace p Y) :
    (mapIsometryEquiv (p := p) e he).symm nu =
      map e.symm (fun _ ↦ measurable_edist_right) e.symm.measurable
        (he.right_inv e.right_inv : Isometry (e.symm : Y → X)).lipschitzWith nu :=
  (rfl)

end WassersteinSpace

end TauCeti
