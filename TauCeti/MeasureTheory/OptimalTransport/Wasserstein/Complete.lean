/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Chain
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Completeness of the Wasserstein space

Over a complete separable pseudometric ground space carrying its Borel structure, and for a finite
exponent `1 ≤ p < ∞`, the `p`-Wasserstein distance is a complete pseudometric: on the finite-moment
laws `P_p (X)` of `TauCeti.WassersteinSpace` and, more generally, on every anchored
finite-distance component of `TauCeti.WassersteinComponent`.

The construction behind both statements is carried out once, on measures, in
`TauCeti.exists_isProbabilityMeasure_wassersteinEDist_le_tsum`: a sequence of laws whose
consecutive Wasserstein distances are bounded by a summable sequence has a limit law, together
with the quantitative estimate that its distance to the `n`-th term is at most the `n`-th tail of
those bounds.

That construction is the classical argument on path space rather than an argument by tightness.
Near-optimal couplings of the consecutive laws are glued into a *single* probability measure on
`ℕ → X` by Layer 0's countable gluing `TauCeti.Measure.chainMeasure`, whose consecutive coordinate
pairs are the prescribed couplings. The coordinate process then has summable jumps, so almost
every path is Cauchy and — the ground space being complete — convergent; the limit is measurable
as an almost everywhere limit of the measurable coordinate maps, and the joint law of the `n`-th
coordinate with that limit is a coupling exhibiting the asserted bound.

Two economies keep the argument short. Summability of the jumps is only needed in `L¹`, which the
`L^p` bounds supply for free because the path law is a probability measure, so no `L^p`
Minkowski inequality for a countable sum is required. And the displacement to the limit is
compared with the displacements along the chain by Fatou's lemma for the `L^p` seminorm, in the
`ℝ≥0∞`-valued form that `TauCeti.eLpNorm_rpow_eq_lintegral` makes available; a finite triangle
inequality then bounds each of the latter.

The exponent has to be finite in two places: the seminorm is a root of an integral, and the
distances to the limit are recovered from a pointwise almost everywhere limit. Completeness of the
finite-`W_∞` components is a separate statement, with its own proof by consecutive near-optimal
couplings, and belongs with the rest of the `W_∞` endpoint.

## Main statements

* `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_le_tsum` — a chain of laws with summable
  consecutive Wasserstein distances converges, with the tail bound on the distances to its limit;
* `TauCeti.WassersteinComponent.completeSpace` and
  `TauCeti.WassersteinComponent.instCompleteSpace` — every anchored finite-distance component is
  complete;
* `TauCeti.WassersteinSpace.completeSpace` and `TauCeti.WassersteinSpace.instCompleteSpace` — the
  finite-moment Wasserstein space `P_p (X)` is complete.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  the Wasserstein space over a Polish space is proved to be Polish by this argument.
* F. Bolley, *Separability and completeness for the Wasserstein distance*, Séminaire de
  Probabilités XLI, Lecture Notes in Mathematics 1934, Springer 2008, pp. 371--377.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

universe u

variable {X : Type u} {p : ℝ≥0∞}

/-- **Fatou's lemma for the `L^p` seminorm**, for `ℝ≥0∞`-valued functions and a finite nonzero
exponent: an almost everywhere pointwise limit of functions of `L^p` seminorm at most `c` again has
`L^p` seminorm at most `c`. Mathlib's `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto` is the same
statement for functions valued in a seminormed group, which the extended-valued ground distance of
a transport problem is not; the proof here is the same passage through
`TauCeti.eLpNorm_rpow_eq_lintegral` and Fatou's lemma for the lower integral. -/
private theorem eLpNorm_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hle : ∀ n, eLpNorm (f n) p μ ≤ c) :
    eLpNorm g p μ ≤ c := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have key : eLpNorm g p μ ^ p.toReal ≤ c ^ p.toReal := by
    rw [eLpNorm_rpow_eq_lintegral hp0 hp]
    calc ∫⁻ x, g x ^ p.toReal ∂μ
        = ∫⁻ x, atTop.liminf (fun n ↦ f n x ^ p.toReal) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with x hx
          exact (Tendsto.liminf_eq
            (((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (g x)).comp hx)).symm
      _ ≤ atTop.liminf fun n ↦ ∫⁻ x, f n x ^ p.toReal ∂μ :=
          lintegral_liminf_le' fun n ↦ (hf n).pow_const _
      _ ≤ c ^ p.toReal := by
          refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
          rw [← eLpNorm_rpow_eq_lintegral hp0 hp]
          exact ENNReal.rpow_le_rpow (hle n) hr.le
  exact (ENNReal.rpow_le_rpow_iff hr).1 key

section Limit

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [StandardBorelSpace X]

/-- **A chain of laws with summable Wasserstein jumps converges.** If the `p`-Wasserstein distance
of consecutive terms of a sequence `μ` of probability measures is bounded by a summable sequence
`b`, then there is a probability measure `ν` with `W_p (μ n, ν)` at most the `n`-th tail
`∑' k, b (n + k)`; in particular `W_p (μ n, ν)` tends to `0`.

This is the analytic content of the completeness of the Wasserstein distance, stated on measures
so that it serves both `TauCeti.WassersteinSpace` and every anchored component. The limit measure
is the law of the almost sure limit of the coordinate process of the countable gluing of
near-optimal couplings of the consecutive terms; the tail bound is what identifies that law as the
Wasserstein limit. The hypothesis is a strict inequality because it is applied to a value of the
infimum `TauCeti.wassersteinEDist`, which is what makes near-optimal couplings available. -/
theorem exists_isProbabilityMeasure_wassersteinEDist_le_tsum (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)] {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞) (hμ : ∀ n, wassersteinEDist p (μ n) (μ (n + 1)) < b n) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∀ n, wassersteinEDist p (μ n) ν ≤ ∑' k, b (n + k) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  have : Nonempty X := Measure.nonempty_of_neZero (μ 0)
  -- the near-optimal couplings of consecutive laws, and their countable gluing
  choose π hπ hπb using fun n ↦ wassersteinEDist_lt_iff.1 (hμ n)
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  have hchain : ∀ n, (π n).snd = (π (n + 1)).fst := fun n ↦ by
    rw [(hπ n).snd_eq, (hπ (n + 1)).fst_eq]
  set P : Measure (ℕ → X) := TauCeti.Measure.chainMeasure (X := fun _ ↦ X) π with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hev : ∀ n, Measurable fun x : ℕ → X ↦ x n := fun n ↦ measurable_pi_apply n
  have hcoord : ∀ n, P.map (fun x ↦ x n) = μ n := fun n ↦ by
    rw [hP, TauCeti.Measure.map_eval_chainMeasure π hchain n, (hπ n).fst_eq]
  have hadj : ∀ n, P.map (fun x ↦ (x n, x (n + 1))) = π n := fun n ↦ by
    rw [hP, TauCeti.Measure.map_adjacent_chainMeasure π hchain n]
  -- the jumps of the coordinate process have the prescribed `L^p` sizes
  have hjump : ∀ n, eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P < b n := fun n ↦ by
    have : eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P
        = eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (π n) := by
      rw [← hadj n, eLpNorm_map_measure hd.aestronglyMeasurable
        ((hev n).prodMk (hev (n + 1))).aemeasurable]
      rfl
    rw [this]
    exact hπb n
  have hjumpmeas : ∀ n, Measurable fun x : ℕ → X ↦ edist (x n) (x (n + 1)) :=
    fun n ↦ hd.comp ((hev n).prodMk (hev (n + 1)))
  -- almost every path is Cauchy, since its jumps are summable in `L¹`
  have hint : ∀ n, ∫⁻ x, edist (x n) (x (n + 1)) ∂P ≤ b n := fun n ↦ by
    calc ∫⁻ x, edist (x n) (x (n + 1)) ∂P
        = eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) 1 P := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          simp
      _ ≤ eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + 1))) p P :=
          eLpNorm_le_eLpNorm_of_exponent_le hp (hjumpmeas n).aestronglyMeasurable
      _ ≤ b n := (hjump n).le
  have hcauchy : ∀ᵐ x ∂P, CauchySeq fun n ↦ x n := by
    have hlt : ∫⁻ x, ∑' n, edist (x n) (x (n + 1)) ∂P ≠ ∞ := by
      rw [lintegral_tsum fun n ↦ (hjumpmeas n).aemeasurable]
      exact ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hint)
    filter_upwards [ae_lt_top (Measurable.tsum hjumpmeas) hlt] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top _ (fun _ ↦ le_rfl) hx.ne
  -- hence almost every path converges, to a measurable limit `Z`
  have hgtendsto : ∀ᵐ x ∂P, Tendsto (fun n ↦ x n) atTop (𝓝 (limUnder atTop fun n ↦ x n)) := by
    filter_upwards [hcauchy] with x hx
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hx)
  obtain ⟨Z, hZ, hZg⟩ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hev n).aemeasurable) hgtendsto
  have hZtendsto : ∀ᵐ x ∂P, Tendsto (fun n ↦ x n) atTop (𝓝 (Z x)) := by
    filter_upwards [hgtendsto, hZg] with x hx hx' using hx' ▸ hx
  refine ⟨P.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance,
    fun n ↦ ?_⟩
  -- the limit is coupled to every `μ n` by the joint law of the `n`-th coordinate and `Z`
  have hcoupling : IsCoupling (P.map fun x ↦ (x n, Z x)) (μ n) (P.map Z) := by
    constructor
    · rw [Measure.fst, Measure.map_map measurable_fst ((hev n).prodMk hZ)]
      exact hcoord n
    · rw [Measure.snd, Measure.map_map measurable_snd ((hev n).prodMk hZ)]
      rfl
  -- the displacement to the limit is the limit of the displacements along the chain
  have hstep : ∀ N, eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + N))) p P
      ≤ ∑ k ∈ Finset.range N, b (n + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        calc eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + (N + 1)))) p P
            ≤ eLpNorm (fun x : ℕ → X ↦
                edist (x n) (x (n + N)) + edist (x (n + N)) (x (n + N + 1))) p P :=
              eLpNorm_mono_enorm fun x ↦ by
                simpa [← Nat.add_assoc] using edist_triangle (x n) (x (n + N)) (x (n + N + 1))
          _ ≤ eLpNorm (fun x : ℕ → X ↦ edist (x n) (x (n + N))) p P
                + eLpNorm (fun x : ℕ → X ↦ edist (x (n + N)) (x (n + N + 1))) p P :=
              eLpNorm_add_le (hd.comp ((hev n).prodMk (hev (n + N)))).aestronglyMeasurable
                (hjumpmeas (n + N)).aestronglyMeasurable hp
          _ ≤ (∑ k ∈ Finset.range N, b (n + k)) + b (n + N) := by
              gcongr
              exact (hjump (n + N)).le
          _ = ∑ k ∈ Finset.range (N + 1), b (n + k) := (Finset.sum_range_succ _ _).symm
  calc wassersteinEDist p (μ n) (P.map Z)
      ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (P.map fun x ↦ (x n, Z x)) :=
        wassersteinEDist_le hcoupling p
    _ = eLpNorm (fun x : ℕ → X ↦ edist (x n) (Z x)) p P := by
        rw [eLpNorm_map_measure hd.aestronglyMeasurable ((hev n).prodMk hZ).aemeasurable]
        rfl
    _ ≤ ∑' k, b (n + k) := by
        refine eLpNorm_le_of_ae_tendsto hp0 hp'
          (fun N ↦ (hd.comp ((hev n).prodMk (hev (n + N)))).aemeasurable) ?_
          fun N ↦ (hstep N).trans (ENNReal.sum_le_tsum _)
        filter_upwards [hZtendsto] with x hx
        exact tendsto_const_nhds.edist
          (hx.comp (tendsto_atTop_mono (fun N ↦ Nat.le_add_left N n) tendsto_id))

end Limit

section Complete

variable [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [StandardBorelSpace X]

/-- The geometric instance of `TauCeti.exists_isProbabilityMeasure_wassersteinEDist_le_tsum` that
the two completeness proofs consume: a chain whose consecutive distances are below `2⁻¹ ^ n`
converges, with the explicit geometric tail `2⁻¹ ^ n * 2`. -/
private theorem exists_isProbabilityMeasure_wassersteinEDist_le_geometric
    (hp : 1 ≤ p) (hp' : p ≠ ∞) {μ : ℕ → Measure X} [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, wassersteinEDist p (μ n) (μ (n + 1)) < 2⁻¹ ^ n) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∀ n, wassersteinEDist p (μ n) ν ≤ 2⁻¹ ^ n * 2 := by
  have hgeom : ∀ n : ℕ, ∑' k, (2 : ℝ≥0∞)⁻¹ ^ (n + k) = 2⁻¹ ^ n * 2 := fun n ↦ by
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  have hb : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
    simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
  obtain ⟨ν, hν, hνle⟩ := exists_isProbabilityMeasure_wassersteinEDist_le_tsum hp hp' hb hμ
  exact ⟨ν, hν, fun n ↦ (hνle n).trans (hgeom n).le⟩

/-- The geometric tails bounding the distances to the limit tend to `0`. -/
private theorem tendsto_geometric_mul_two :
    Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n * 2) atTop (𝓝 0) := by
  have h2 : (2 : ℝ≥0∞)⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]
    norm_num
  simpa using ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h2) (Or.inr (by simp))

variable [Fact (1 ≤ p)]

namespace WassersteinComponent

variable {μ₀ : ProbabilityMeasure X}

/-- **Every anchored finite-distance Wasserstein component over a Polish ground space is
complete**, for a finite exponent `1 ≤ p < ∞`. A Cauchy sequence of laws in the component of `μ₀`
has a limit law, and that limit is again at finite distance from `μ₀` because it is at finite
distance from the first term of the sequence. -/
theorem completeSpace (hp' : p ≠ ∞) : CompleteSpace (WassersteinComponent p μ₀) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun u hu ↦ ?_
  have hjump : ∀ n, wassersteinEDist p ((u n : ProbabilityMeasure X) : Measure X)
      ((u (n + 1) : ProbabilityMeasure X) : Measure X) < 2⁻¹ ^ n := fun n ↦ by
    have := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rwa [edist_def] at this
  obtain ⟨ν, hν, hνle⟩ :=
    exists_isProbabilityMeasure_wassersteinEDist_le_geometric Fact.out hp' hjump
  have hanchor : wassersteinEDist p (μ₀ : Measure X) ν ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨wassersteinEDist_anchor_ne_top (u 0), ?_⟩)
      (wassersteinEDist_triangle measurable_edist Fact.out _ _ _)
    exact ne_top_of_le_ne_top (by simp) (hνle 0)
  have hcoe : ((mk (⟨ν, hν⟩ : ProbabilityMeasure X) hanchor : WassersteinComponent p μ₀) :
      ProbabilityMeasure X) = ⟨ν, hν⟩ := coe_mk _ _
  refine ⟨mk ⟨ν, hν⟩ hanchor, tendsto_iff_edist_tendsto_0.2 ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_geometric_mul_two
    (fun _ ↦ zero_le) fun n ↦ ?_
  rw [edist_def, hcoe]
  exact hνle n

/-- Every anchored finite-distance Wasserstein component over a Polish ground space is complete,
read off the exponent facts. -/
instance instCompleteSpace [Fact (p ≠ ∞)] : CompleteSpace (WassersteinComponent p μ₀) :=
  completeSpace Fact.out

end WassersteinComponent

namespace WassersteinSpace

/-- **The finite-moment Wasserstein space over a Polish ground space is complete**, for a finite
exponent `1 ≤ p < ∞`. The limit law of a Cauchy sequence has a finite `p`-moment because it is at
finite distance from the first term of the sequence, which has one. -/
theorem completeSpace (hp' : p ≠ ∞) : CompleteSpace (WassersteinSpace p X) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun u hu ↦ ?_
  have hjump : ∀ n, wassersteinEDist p ((u n : ProbabilityMeasure X) : Measure X)
      ((u (n + 1) : ProbabilityMeasure X) : Measure X) < 2⁻¹ ^ n := fun n ↦ by
    have := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rwa [edist_def] at this
  obtain ⟨ν, hν, hνle⟩ :=
    exists_isProbabilityMeasure_wassersteinEDist_le_geometric Fact.out hp' hjump
  obtain ⟨x₀⟩ : Nonempty X :=
    Measure.nonempty_of_neZero ((u 0 : ProbabilityMeasure X) : Measure X)
  have hmoment : HasFiniteMoment p ν := by
    refine (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist x₀ ν).2 ?_
    have hdirac : wassersteinEDist p (Measure.dirac x₀)
        ((u 0 : ProbabilityMeasure X) : Measure X) ≠ ∞ :=
      (hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist x₀ _).1
        (hasFiniteMoment (u 0))
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨hdirac, ne_top_of_le_ne_top (by simp) (hνle 0)⟩)
      (wassersteinEDist_triangle measurable_edist Fact.out _ _ _)
  have hcoe : ((mk (⟨ν, hν⟩ : ProbabilityMeasure X) hmoment : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν, hν⟩ := coe_mk _ _
  refine ⟨mk ⟨ν, hν⟩ hmoment, tendsto_iff_edist_tendsto_0.2 ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_geometric_mul_two
    (fun _ ↦ zero_le) fun n ↦ ?_
  rw [edist_def, hcoe]
  exact hνle n

/-- The finite-moment Wasserstein space over a Polish ground space is complete, read off the
exponent facts. -/
instance instCompleteSpace [Fact (p ≠ ∞)] : CompleteSpace (WassersteinSpace p X) :=
  completeSpace Fact.out

end WassersteinSpace

end Complete

end TauCeti
