/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Basic

/-!
# Complementary slackness, optimality certificates, and `c`-cyclical monotonicity

A pair of integrable potentials `φ`, `ψ` satisfying the Kantorovich dual constraint
`φ x + ψ y ≤ c (x, y)` bounds the cost of every transport plan from below. When a plan is
concentrated on the *contact set* where that constraint is an equality, the two bounds meet:
the plan is optimal, the pair is a dual optimizer, and there is no duality gap. This is
complementary slackness, and the resulting data is the standard optimality certificate that the
Monge and barycentre layers verify instead of re-solving a transport problem.

This file builds that certificate for the raw extended-nonnegative interface — an arbitrary cost
`c : X × Y → ℝ≥0∞` on arbitrary measurable spaces — and shows that it is exact: in the
dual-attainment regime, an optimal plan of almost-everywhere measurable cost is concentrated on
the contact set. Measurability of the cost is needed for that converse only, and never for the
consequences drawn from a certificate. No topology,
compactness, or lower semicontinuity is used, so the certificate applies verbatim to the
Borel-cost regime, where a dual optimizer is produced by other means. It is a statement
about the *unregularized* Kantorovich problem only: an entropy-regularized optimizer is
characterised by the stationarity condition `dπ / d(μ ⊗ ν) = exp ((φ ⊕ ψ - c) / ε)` and is
typically of full support, so it is not concentrated on a contact set and no claim is made
about it here.

The last section connects the cost-level notion of `c`-cyclical monotonicity to certificates by
proving that the contact set of a dual feasible pair is `c`-cyclically monotone. Hence a
certified plan is concentrated on a `c`-cyclically monotone set, which is measurable as soon as
the cost and both potentials are. The converse implication — that
concentration on a `c`-cyclically monotone set forces optimality — is the
Schachermayer--Teichmann theorem and is not proved here.

## Main definitions

* `TauCeti.dualContactSet c φ ψ` — the set where the dual constraint for an
  extended-nonnegative cost holds with equality;
* `TauCeti.IsDualCertificate c π μ ν φ ψ` — a coupling `π` together with an integrable dual
  feasible pair `(φ, ψ)` on whose contact set `π` is concentrated;
* `TauCeti.IsCyclicallyMonotone c S` — finite `c`-cyclical monotonicity of a set of pairs.

## Main statements

* `TauCeti.IsDualCertificate.lintegral_eq_ofReal` — a certified plan costs exactly the value of
  its dual pair, with `TauCeti.IsDualCertificate.transportCost_eq` the resulting absence of a
  duality gap;
* `TauCeti.IsDualCertificate.isOptimalCoupling` and
  `TauCeti.IsDualCertificate.kantorovichDualValue_le` — a certificate proves primal optimality
  of the plan and dual optimality of the pair;
* `TauCeti.isDualCertificate_iff` — **complementary slackness**: for a fixed coupling `π` and a
  fixed feasible integrable pair, being a certificate is exactly having finite cost no larger
  than the dual value, provided `AEMeasurable c π`; so `TauCeti.IsOptimalCoupling.isDualCertificate`
  recovers the certificate from an optimal plan of almost-everywhere measurable cost whenever
  the dual value is attained;
* `TauCeti.isDualCertificate_graphPlan` and
  `TauCeti.transportCost_eq_lintegral_of_ae_mem_dualContactSet` — the Monge form: the
  Kantorovich value is attained at the graph plan of a map whose graph lies almost everywhere in
  the contact set; together with `TauCeti.transportCost_le_lintegral_of_hasLaw`, this exhibits
  the map as a minimizer among transport maps;
* `TauCeti.DualFeasible.isCyclicallyMonotone_dualContactSet` and
  `TauCeti.IsDualCertificate.exists_isCyclicallyMonotone` — contact sets are `c`-cyclically
  monotone, and a certified plan whose cost and potentials are measurable is concentrated on a
  measurable such set.

## Implementation notes

`TauCeti.contactSet` is stated for a *finite real* cost and extended-real potentials, the
signature forced by the `c`-transform calculus, where a transform of a real potential can take
the value `-∞`. The primal problem instead uses an extended-nonnegative cost, so a plan can be
forbidden to charge a pair by setting `c` to `∞` there, while the potentials appearing in an
integrable dual pair are honestly real. `TauCeti.dualContactSet` is the contact set for that
second signature, and `TauCeti.dualContactSet_ofReal` identifies the two whenever both apply.
Membership is an equality of `EReal`s rather than of extended-nonnegative numbers, because
`ENNReal.ofReal` forgets the sign: for `c (x, y) = 0` and `φ x + ψ y = -1` the two
`ENNReal.ofReal` values agree although the dual constraint is strict.

The complementary slackness converse is stated with the real number `(∫⁻ z, c z ∂π).toReal`
rather than with `ENNReal.ofReal (kantorovichDualValue μ ν φ ψ)` on purpose: a dual feasible
pair can have a negative value, and then `ENNReal.ofReal` truncates it to `0` and the
`ℝ≥0∞`-valued inequality holds for reasons that have nothing to do with contact. The example
above, with both spaces a point, is such a pair.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.1 and §2.3, for complementary slackness and cyclical monotonicity;
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Definition 5.1 and
  Theorem 5.10;
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Progress in Nonlinear
  Differential Equations and their Applications 87, 2015, §1.3 and §1.6;
* W. Schachermayer and J. Teichmann, *Characterization of optimal transport plans for the
  Monge--Kantorovich problem*, Proc. Amer. Math. Soc. 137 (2009), 519--529, for the converse
  that is not proved here.

This is Layer 2, items 7 and 8 of the optimal-transport roadmap.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ≥0∞} {φ : X → ℝ} {ψ : Y → ℝ}
  {z : X × Y} {x : X} {y : Y}

/-! ### The contact set of an extended-nonnegative cost -/

/-- The contact set of a pair of real potentials against an extended-nonnegative cost: the set
of pairs where the Kantorovich dual constraint `φ x + ψ y ≤ c (x, y)` holds with equality. The
equality is taken in `EReal`, so a pair at which the potentials sum to a negative number is
never a contact point, and a pair of infinite cost is never one either. -/
def dualContactSet (c : X × Y → ℝ≥0∞) (φ : X → ℝ) (ψ : Y → ℝ) : Set (X × Y) :=
  {z | ((φ z.1 + ψ z.2 : ℝ) : EReal) = (c z : EReal)}

/-- Membership in the contact set, for a point of the product. -/
@[simp]
theorem mem_dualContactSet_iff :
    z ∈ dualContactSet c φ ψ ↔ ((φ z.1 + ψ z.2 : ℝ) : EReal) = (c z : EReal) := Iff.rfl

/-- Membership in the contact set, for an explicit pair. -/
theorem mk_mem_dualContactSet_iff :
    (x, y) ∈ dualContactSet c φ ψ ↔ ((φ x + ψ y : ℝ) : EReal) = (c (x, y) : EReal) := Iff.rfl

/-- Membership in the contact set, in the extended-nonnegative form used by `lintegral`. The
sign condition cannot be dropped: `ENNReal.ofReal` is not injective on the reals. -/
theorem mem_dualContactSet_iff_ofReal_eq :
    z ∈ dualContactSet c φ ψ ↔ 0 ≤ φ z.1 + ψ z.2 ∧ ENNReal.ofReal (φ z.1 + ψ z.2) = c z := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hnn, h⟩ ↦ ?_⟩
  · have hle : (0 : EReal) ≤ ((φ z.1 + ψ z.2 : ℝ) : EReal) := h ▸ EReal.coe_ennreal_nonneg (c z)
    exact_mod_cast hle
  · have h' := congrArg EReal.toENNReal h
    rwa [EReal.real_coe_toENNReal, EReal.toENNReal_coe] at h'
  · rw [mem_dualContactSet_iff, ← h, EReal.coe_ennreal_ofReal, max_eq_left hnn]

/-- At a contact point the two potentials sum to a nonnegative number, since the cost is
nonnegative. -/
theorem add_nonneg_of_mem_dualContactSet (hz : z ∈ dualContactSet c φ ψ) :
    0 ≤ φ z.1 + ψ z.2 :=
  (mem_dualContactSet_iff_ofReal_eq.1 hz).1

/-- At a contact point the cost is the extended-nonnegative image of the sum of the two
potentials. -/
theorem ofReal_eq_of_mem_dualContactSet (hz : z ∈ dualContactSet c φ ψ) :
    ENNReal.ofReal (φ z.1 + ψ z.2) = c z :=
  (mem_dualContactSet_iff_ofReal_eq.1 hz).2

/-- The cost is finite at a contact point: the potentials are real there. -/
theorem ne_top_of_mem_dualContactSet (hz : z ∈ dualContactSet c φ ψ) : c z ≠ ⊤ := by
  rw [← ofReal_eq_of_mem_dualContactSet hz]
  exact ENNReal.ofReal_ne_top

/-- At a contact point the sum of the potentials is the real value of the cost. -/
theorem toReal_eq_of_mem_dualContactSet (hz : z ∈ dualContactSet c φ ψ) :
    (c z).toReal = φ z.1 + ψ z.2 := by
  rw [← ofReal_eq_of_mem_dualContactSet hz,
    ENNReal.toReal_ofReal (add_nonneg_of_mem_dualContactSet hz)]

/-- A pair where the dual constraint is an equality, presented in real terms, is a contact
point. -/
theorem mem_dualContactSet_of_toReal_eq (hc : c z ≠ ⊤) (h : (c z).toReal = φ z.1 + ψ z.2) :
    z ∈ dualContactSet c φ ψ := by
  refine mem_dualContactSet_iff_ofReal_eq.2 ⟨h ▸ ENNReal.toReal_nonneg, ?_⟩
  rw [← h, ENNReal.ofReal_toReal hc]

/-- The contact set of a nonnegative real cost, viewed through `ENNReal.ofReal`, is the contact
set of the `c`-transform calculus. This is the bridge between the two signatures. -/
theorem dualContactSet_ofReal {c : X × Y → ℝ} (hc : ∀ z, 0 ≤ c z) (φ : X → ℝ) (ψ : Y → ℝ) :
    dualContactSet (fun z ↦ ENNReal.ofReal (c z)) φ ψ =
      contactSet c (fun x ↦ (φ x : EReal)) (fun y ↦ (ψ y : EReal)) := by
  ext z
  rw [mem_dualContactSet_iff, mem_contactSet_iff, EReal.coe_ennreal_ofReal, max_eq_left (hc z),
    EReal.coe_add]

section Measurability

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- The contact set of a measurable cost and measurable potentials is measurable. -/
theorem measurableSet_dualContactSet (hc : Measurable c) (hφ : Measurable φ)
    (hψ : Measurable ψ) : MeasurableSet (dualContactSet c φ ψ) := by
  have hsum : Measurable fun z : X × Y ↦ φ z.1 + ψ z.2 :=
    (hφ.comp measurable_fst).add (hψ.comp measurable_snd)
  have hset : dualContactSet c φ ψ =
      {z : X × Y | 0 ≤ φ z.1 + ψ z.2} ∩ {z : X × Y | ENNReal.ofReal (φ z.1 + ψ z.2) = c z} :=
    Set.ext fun _ ↦ mem_dualContactSet_iff_ofReal_eq
  rw [hset]
  exact (measurableSet_le measurable_const hsum).inter
    (measurableSet_eq_fun (ENNReal.measurable_ofReal.comp hsum) hc)

end Measurability

/-! ### Optimality certificates -/

section Certificate

variable [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : Measure (X × Y)}

/-- An *optimality certificate* for the transport problem with cost `c` and marginals `μ`, `ν`:
a coupling `π` together with an integrable dual feasible pair of potentials `(φ, ψ)` such that
`π` gives full measure to the contact set of the pair. Complementary slackness turns this data
into simultaneous primal optimality of `π`, dual optimality of `(φ, ψ)`, and the absence of a
duality gap, with no topological hypothesis whatsoever. -/
structure IsDualCertificate (c : X × Y → ℝ≥0∞) (π : Measure (X × Y)) (μ : Measure X)
    (ν : Measure Y) (φ : X → ℝ) (ψ : Y → ℝ) : Prop extends IsCoupling π μ ν where
  /-- The potentials satisfy the Kantorovich dual constraint everywhere. -/
  dualFeasible : DualFeasible c φ ψ
  /-- The first potential is integrable against the first marginal. -/
  integrable_left : Integrable φ μ
  /-- The second potential is integrable against the second marginal. -/
  integrable_right : Integrable ψ ν
  /-- Complementary slackness: the plan is concentrated on the contact set. -/
  ae_mem_dualContactSet : ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ

/-- A plan concentrated on the contact set of an integrable pair costs exactly the value of that
pair. Dual feasibility is not needed: the contact condition alone pins the cost down. -/
theorem lintegral_eq_ofReal_kantorovichDualValue (hπ : IsCoupling π μ ν) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hae : ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ) :
    ∫⁻ z, c z ∂π = ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) := by
  have hnn : (0 : X × Y → ℝ) ≤ᵐ[π] fun z ↦ φ z.1 + ψ z.2 :=
    hae.mono fun _ hz ↦ add_nonneg_of_mem_dualContactSet hz
  rw [kantorovichDualValue_eq_integral hπ hφ hψ,
    ofReal_integral_eq_lintegral_ofReal (hπ.integrable_add_split hφ hψ) hnn]
  exact lintegral_congr_ae (hae.mono fun _ hz ↦ (ofReal_eq_of_mem_dualContactSet hz).symm)

/-- A plan concentrated on the contact set of an integrable pair has finite cost. -/
theorem lintegral_ne_top_of_ae_mem_dualContactSet (hπ : IsCoupling π μ ν) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hae : ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ) :
    ∫⁻ z, c z ∂π ≠ ⊤ := by
  rw [lintegral_eq_ofReal_kantorovichDualValue hπ hφ hψ hae]
  exact ENNReal.ofReal_ne_top

/-- The value of an integrable pair is nonnegative when a coupling is concentrated on its
contact set. Dual feasibility is not needed. -/
theorem kantorovichDualValue_nonneg_of_ae_mem_dualContactSet (hπ : IsCoupling π μ ν)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) (hae : ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ) :
    0 ≤ kantorovichDualValue μ ν φ ψ := by
  rw [kantorovichDualValue_eq_integral hπ hφ hψ]
  exact integral_nonneg_of_ae
    (hae.mono fun _ hz ↦ add_nonneg_of_mem_dualContactSet hz)

/-- Two couplings concentrated on the same contact set of an integrable pair have equal cost.
Dual feasibility is not needed. -/
theorem lintegral_eq_lintegral_of_ae_mem_dualContactSet {σ : Measure (X × Y)}
    (hπ : IsCoupling π μ ν) (hσ : IsCoupling σ μ ν) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hπae : ∀ᵐ z ∂π, z ∈ dualContactSet c φ ψ)
    (hσae : ∀ᵐ z ∂σ, z ∈ dualContactSet c φ ψ) :
    ∫⁻ z, c z ∂σ = ∫⁻ z, c z ∂π :=
  (lintegral_eq_ofReal_kantorovichDualValue hσ hφ hψ hσae).trans
    (lintegral_eq_ofReal_kantorovichDualValue hπ hφ hψ hπae).symm

namespace IsDualCertificate

variable (h : IsDualCertificate c π μ ν φ ψ)
include h

/-- A certified plan costs exactly the value of its dual pair. -/
theorem lintegral_eq_ofReal :
    ∫⁻ z, c z ∂π = ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) :=
  lintegral_eq_ofReal_kantorovichDualValue h.toIsCoupling h.integrable_left h.integrable_right
    h.ae_mem_dualContactSet

/-- The value of a certified dual pair is nonnegative, because the cost is. -/
theorem kantorovichDualValue_nonneg : 0 ≤ kantorovichDualValue μ ν φ ψ :=
  kantorovichDualValue_nonneg_of_ae_mem_dualContactSet h.toIsCoupling h.integrable_left
    h.integrable_right h.ae_mem_dualContactSet

/-- **No duality gap.** The primal value equals the value of a certified dual pair. -/
theorem transportCost_eq :
    transportCost c μ ν = ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) :=
  le_antisymm (h.lintegral_eq_ofReal ▸ transportCost_le_lintegral h.toIsCoupling c)
    (h.dualFeasible.ofReal_kantorovichDualValue_le_transportCost h.integrable_left
      h.integrable_right)

/-- A certificate exhibits a plan of finite cost, so the primal value is finite. -/
theorem transportCost_ne_top : transportCost c μ ν ≠ ⊤ := by
  rw [h.transportCost_eq]
  exact ENNReal.ofReal_ne_top

/-- **The certificate proves primal optimality.** -/
theorem isOptimalCoupling : IsOptimalCoupling c π μ ν where
  toIsCoupling := h.toIsCoupling
  lintegral_eq := h.lintegral_eq_ofReal.trans h.transportCost_eq.symm

/-- The primal value in real terms. -/
theorem toReal_transportCost_eq :
    (transportCost c μ ν).toReal = kantorovichDualValue μ ν φ ψ := by
  rw [h.transportCost_eq, ENNReal.toReal_ofReal h.kantorovichDualValue_nonneg]

/-- **The certificate proves dual optimality.** No other integrable feasible pair has a larger
value. -/
theorem kantorovichDualValue_le {φ' : X → ℝ} {ψ' : Y → ℝ} (hfeas : DualFeasible c φ' ψ')
    (hφ' : Integrable φ' μ) (hψ' : Integrable ψ' ν) :
    kantorovichDualValue μ ν φ' ψ' ≤ kantorovichDualValue μ ν φ ψ := by
  have hle := hfeas.ofReal_kantorovichDualValue_le_transportCost hφ' hψ'
  rw [h.transportCost_eq] at hle
  exact (ENNReal.ofReal_le_ofReal_iff h.kantorovichDualValue_nonneg).1 hle

/-- Any other coupling concentrated on the same contact set has the same cost. -/
theorem lintegral_eq_of_ae_mem_dualContactSet {σ : Measure (X × Y)} (hσ : IsCoupling σ μ ν)
    (hae : ∀ᵐ z ∂σ, z ∈ dualContactSet c φ ψ) : ∫⁻ z, c z ∂σ = ∫⁻ z, c z ∂π :=
  lintegral_eq_lintegral_of_ae_mem_dualContactSet h.toIsCoupling hσ h.integrable_left
    h.integrable_right h.ae_mem_dualContactSet hae

end IsDualCertificate

/-- **Complementary slackness.** For a fixed coupling and a fixed integrable dual feasible pair,
being an optimality certificate is exactly having finite cost that does not exceed the value of
the pair. The inequality is stated between real numbers: `ENNReal.ofReal` truncates a negative
dual value to `0`, and then the extended-nonnegative inequality carries no information. -/
theorem isDualCertificate_iff (hc : AEMeasurable c π) (hπ : IsCoupling π μ ν)
    (hfeas : DualFeasible c φ ψ) (hφ : Integrable φ μ) (hψ : Integrable ψ ν) :
    IsDualCertificate c π μ ν φ ψ ↔
      ∫⁻ z, c z ∂π ≠ ⊤ ∧ (∫⁻ z, c z ∂π).toReal ≤ kantorovichDualValue μ ν φ ψ := by
  refine ⟨fun h ↦ ⟨lintegral_ne_top_of_ae_mem_dualContactSet hπ hφ hψ h.ae_mem_dualContactSet,
    ?_⟩, fun ⟨htop, hle⟩ ↦ ⟨hπ, hfeas, hφ, hψ, ?_⟩⟩
  · rw [h.lintegral_eq_ofReal, ENNReal.toReal_ofReal h.kantorovichDualValue_nonneg]
  · -- The gap between the cost and the split sum of the potentials is a nonnegative integrable
    -- function with nonpositive integral, hence vanishes almost everywhere.
    have hfin : ∀ᵐ z ∂π, c z < ⊤ := ae_lt_top' hc htop
    have hcint : Integrable (fun z ↦ (c z).toReal) π :=
      integrable_toReal_of_lintegral_ne_top hc htop
    have hsum : Integrable (fun z : X × Y ↦ φ z.1 + ψ z.2) π :=
      hπ.integrable_add_split hφ hψ
    have hgap : Integrable (fun z ↦ (c z).toReal - (φ z.1 + ψ z.2)) π := hcint.sub hsum
    have hnn : (0 : X × Y → ℝ) ≤ᵐ[π] fun z ↦ (c z).toReal - (φ z.1 + ψ z.2) := by
      filter_upwards [hfin] with z hz
      have hz' := (ENNReal.ofReal_le_iff_le_toReal hz.ne).1 (hfeas.ofReal_add_le z.1 z.2)
      simp only [Pi.zero_apply, sub_nonneg]
      exact hz'
    have hint : ∫ z, ((c z).toReal - (φ z.1 + ψ z.2)) ∂π = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hnn)
      rw [integral_sub hcint hsum, integral_toReal hc (hfin.mono fun _ h ↦ h),
        ← kantorovichDualValue_eq_integral hπ hφ hψ, sub_nonpos]
      exact hle
    filter_upwards [hfin, (integral_eq_zero_iff_of_nonneg_ae hnn hgap).1 hint] with z hz hz'
    have hz'' : (c z).toReal - (φ z.1 + ψ z.2) = 0 := hz'
    exact mem_dualContactSet_of_toReal_eq hz.ne (by linarith)

/-- **In the dual-attainment regime, optimality is contact-set concentration.** An optimal plan
of finite cost whose dual value is attained by an integrable feasible pair is certified by that
pair. -/
theorem IsOptimalCoupling.isDualCertificate (hc : AEMeasurable c π)
    (hopt : IsOptimalCoupling c π μ ν) (hfeas : DualFeasible c φ ψ) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (htop : transportCost c μ ν ≠ ⊤)
    (hattain : (transportCost c μ ν).toReal = kantorovichDualValue μ ν φ ψ) :
    IsDualCertificate c π μ ν φ ψ := by
  rw [isDualCertificate_iff hc hopt.toIsCoupling hfeas hφ hψ, hopt.lintegral_eq]
  exact ⟨htop, hattain.le⟩

/-- Once one certificate witnesses dual attainment, every optimal coupling with an
almost-everywhere measurable cost is certified by the same potentials. -/
theorem IsDualCertificate.of_isOptimalCoupling (h : IsDualCertificate c π μ ν φ ψ)
    {σ : Measure (X × Y)} (hcσ : AEMeasurable c σ) (hσ : IsOptimalCoupling c σ μ ν) :
    IsDualCertificate c σ μ ν φ ψ :=
  hσ.isDualCertificate hcσ h.dualFeasible h.integrable_left h.integrable_right
    h.transportCost_ne_top h.toReal_transportCost_eq

end Certificate

/-! ### The Monge form of the certificate -/

section Monge

variable [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} {T : X → Y}

/-- A transport map whose graph lies almost everywhere in the contact set of an integrable dual
feasible pair is certified: its graph plan is an optimality certificate. This is the form in
which the Brenier and polar-factorisation layers verify optimality of a map. -/
theorem isDualCertificate_graphPlan (hc : AEMeasurable c (graphPlan T μ))
    (hT : HasLaw T ν μ) (hfeas : DualFeasible c φ ψ) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hae : ∀ᵐ x ∂μ, (x, T x) ∈ dualContactSet c φ ψ) :
    IsDualCertificate c (graphPlan T μ) μ ν φ ψ where
  toIsCoupling := isCoupling_graphPlan hT
  dualFeasible := hfeas
  integrable_left := hφ
  integrable_right := hψ
  ae_mem_dualContactSet := by
    have hπ := isCoupling_graphPlan hT
    have hsum : AEMeasurable (fun z : X × Y ↦ ((φ z.1 + ψ z.2 : ℝ) : EReal))
        (graphPlan T μ) :=
      measurable_coe_real_ereal.comp_aemeasurable
        (hπ.integrable_add_split hφ hψ).aemeasurable
    have hcost : AEMeasurable (fun z ↦ (c z : EReal)) (graphPlan T μ) :=
      measurable_coe_ennreal_ereal.comp_aemeasurable hc
    have hcontact : NullMeasurableSet (dualContactSet c φ ψ) (graphPlan T μ) := by
      simpa only [dualContactSet] using nullMeasurableSet_eq_fun hsum hcost
    have hf := aemeasurable_prodMk_self hT.aemeasurable
    -- Transport the a.e. statement along the graph map. The contact set is only
    -- `NullMeasurableSet` here, so `ae_map_iff` does not apply and the pushforward is unfolded
    -- by hand through `Measure.map_apply₀`.
    rw [ae_iff, ← Set.compl_def, graphPlan_def,
      Measure.map_apply₀ hf (by simpa only [graphPlan_def] using hcontact.compl),
      Set.preimage_compl, Set.compl_def, ← ae_iff]
    simpa only [Set.mem_preimage] using hae

/-- **The Kantorovich value is attained at the graph plan of a certified transport map.** With
`TauCeti.transportCost_le_lintegral_of_hasLaw`, this exhibits the map as a minimizer among
transport maps. -/
theorem transportCost_eq_lintegral_of_ae_mem_dualContactSet
    (hc : AEMeasurable c (graphPlan T μ)) (hT : HasLaw T ν μ) (hfeas : DualFeasible c φ ψ)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hae : ∀ᵐ x ∂μ, (x, T x) ∈ dualContactSet c φ ψ) :
    transportCost c μ ν = ∫⁻ x, c (x, T x) ∂μ := by
  exact (isOptimalCoupling_graphPlan_iff hT hc).1
    (isDualCertificate_graphPlan hc hT hfeas hφ hψ hae).isOptimalCoupling

end Monge

/-! ### Certificates and `c`-cyclical monotonicity -/

section CyclicallyMonotone

/-- **The contact set of a dual feasible pair is `c`-cyclically monotone.** Rearranging the
targets replaces each equality `φ (x i) + ψ (y i) = c (x i, y i)` by an inequality, while the
two total sums of potentials agree because a permutation does not change a finite sum. -/
theorem DualFeasible.isCyclicallyMonotone_dualContactSet (h : DualFeasible c φ ψ) :
    IsCyclicallyMonotone c (dualContactSet c φ ψ) := by
  rw [isCyclicallyMonotone_iff]
  intro n x y hmem σ
  have hnn : ∀ i, 0 ≤ φ (x i) + ψ (y i) := fun i ↦ add_nonneg_of_mem_dualContactSet (hmem i)
  have hperm : ∑ i, (φ (x i) + ψ (y i)) = ∑ i, (φ (x i) + ψ (y (σ i))) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ fun i ↦ ψ (y i)]
  calc
    ∑ i, c (x i, y i) = ∑ i, ENNReal.ofReal (φ (x i) + ψ (y i)) :=
      Finset.sum_congr rfl fun i _ ↦ (ofReal_eq_of_mem_dualContactSet (hmem i)).symm
    _ = ENNReal.ofReal (∑ i, (φ (x i) + ψ (y i))) :=
      (ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnn i).symm
    _ = ENNReal.ofReal (∑ i, (φ (x i) + ψ (y (σ i)))) := by rw [hperm]
    _ ≤ ∑ i, ENNReal.ofReal (φ (x i) + ψ (y (σ i))) :=
      Finset.le_sum_of_subadditive ENNReal.ofReal ENNReal.ofReal_zero.le
        (fun _ _ ↦ ENNReal.ofReal_add_le) _ _
    _ ≤ ∑ i, c (x i, y (σ i)) :=
      Finset.sum_le_sum fun i _ ↦ h.ofReal_add_le (x i) (y (σ i))

/-- **A certified plan with measurable cost and potentials is concentrated on a measurable
`c`-cyclically monotone set.** The converse implication, that concentration on a
`c`-cyclically monotone set forces optimality, is the Schachermayer--Teichmann theorem and needs
topological hypotheses. -/
theorem IsDualCertificate.exists_isCyclicallyMonotone [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (h : IsDualCertificate c π μ ν φ ψ) (hc : Measurable c) (hφm : Measurable φ)
    (hψm : Measurable ψ) :
    ∃ S : Set (X × Y), MeasurableSet S ∧ IsCyclicallyMonotone c S ∧ π Sᶜ = 0 :=
  ⟨dualContactSet c φ ψ, measurableSet_dualContactSet hc hφm hψm,
    h.dualFeasible.isCyclicallyMonotone_dualContactSet, ae_iff.1 h.ae_mem_dualContactSet⟩

end CyclicallyMonotone

end TauCeti

end

end
