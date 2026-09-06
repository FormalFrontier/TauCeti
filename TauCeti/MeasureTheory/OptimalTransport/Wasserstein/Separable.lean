/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport

/-!
# Separability of the finite-moment Wasserstein space

For a finite exponent `1 ≤ p < ∞` the Wasserstein space `TauCeti.WassersteinSpace p X` of laws of
finite `p`-moment is separable as soon as the ground space is. The countable dense family is the
expected one: the laws carried by finitely many terms of a dense sequence of `X`, each term
receiving a rational share of the total mass. Concretely it is the range of a map defined on
`Finset (ℕ × ℕ)`, a pair `(i, k)` contributing the multiplicity `k` to the `i`-th term of the
sequence and the resulting weights being normalised to total mass `1`.

Three approximations take an arbitrary law to a member of that family, each costing a quarter of
the prescribed accuracy, and all three are supplied by the imported finite-support module: the
finite-support approximation `TauCeti.exists_ae_mem_finset_wassersteinEDist_le`, then
`TauCeti.exists_map_range_wassersteinEDist_le`, which pushes the resulting finitely supported law
onto terms of the dense sequence, and finally the rational-weight approximation
`TauCeti.exists_nat_weights_wassersteinEDist_le`.

The exponent must be finite. Finitely supported laws are not `W_∞`-dense on a general separable
metric space, and indeed `P_∞ (X)` need not be separable.

## Main statements

* `TauCeti.WassersteinSpace.separableSpace` — separability of `P_p (X)` for `1 ≤ p < ∞`, with
  `TauCeti.WassersteinSpace.instSeparableSpace` its instance form.

## Implementation notes

The imported approximation estimates take the measurability of the ground distance explicitly,
and the separability theorem reads it off the Borel structure. Finiteness of the exponent cannot
be an instance argument, so `TauCeti.WassersteinSpace.separableSpace` takes it explicitly and the
instance reads it off a `Fact`, exactly as the metric structure of `TauCeti.WassersteinSpace`
reads `1 ≤ p` off `Fact (1 ≤ p)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.18.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

namespace WassersteinSpace

section Separable

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **`P_p (X)` is separable.** For a finite exponent `1 ≤ p < ∞`, the finite-moment Wasserstein
space over a separable ground space is separable: the laws carried by finitely many terms of a
dense sequence and giving each of them a rational share of the mass form a countable dense set. -/
theorem separableSpace (hp_top : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have hempty : IsEmpty (WassersteinSpace p X) := by
      refine ⟨fun μ ↦ ?_⟩
      have h : ((μ : ProbabilityMeasure X) : Measure X) univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hX, measure_empty] at h
      exact zero_ne_one h
    exact ⟨∅, Set.countable_empty, fun μ ↦ (hempty.false μ).elim⟩
  set u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  -- the countable family of laws with natural multiplicities on terms of the dense sequence
  set G : Finset (ℕ × ℕ) → Measure X := fun t ↦
    (∑ q ∈ t, (q.2 : ℝ≥0∞))⁻¹ • ∑ q ∈ t, (q.2 : ℝ≥0∞) • Measure.dirac (u q.1) with hG_def
  refine ⟨(fun μ : WassersteinSpace p X ↦ ((μ : ProbabilityMeasure X) : Measure X)) ⁻¹'
    Set.range G, (Set.countable_range G).preimage fun _ _ h ↦ toProbabilityMeasure_injective
      (ProbabilityMeasure.toMeasure_injective h), ?_⟩
  refine Metric.dense_iff.2 fun μ r hr ↦ ?_
  have hquarter : (0 : ℝ) < r / 4 := by linarith
  have hquarter' : ENNReal.ofReal (r / 4) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hquarter
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  -- step one: approximate by a law carried by a finite set
  obtain ⟨s, ν₁, hν₁, hnull₁, -, hle₁⟩ :=
    exists_ae_mem_finset_wassersteinEDist_le
      (μ := ((μ : ProbabilityMeasure X) : Measure X)) hp1 hp_top μ.hasFiniteMoment hquarter'
  -- step two: move its atoms onto terms of the dense sequence
  have : IsProbabilityMeasure ν₁ := hν₁
  obtain ⟨T, hT, hTu, hle₂⟩ :=
    exists_map_range_wassersteinEDist_le measurable_edist hu hquarter ν₁ p
  set ν₂ : Measure X := ν₁.map T with hν₂_def
  have hν₂ : IsProbabilityMeasure ν₂ := inferInstanceAs (IsProbabilityMeasure (ν₁.map T))
  have hnull₂ : ν₂ ((↑(s.image T) : Set X)ᶜ) = 0 := by
    rw [hν₂_def, Measure.map_apply hT (s.image T).measurableSet.compl]
    refine measure_mono_null (fun x hx ↦ ?_) hnull₁
    simp only [Finset.coe_image, mem_preimage, mem_compl_iff, mem_image, Finset.mem_coe,
      not_exists, not_and] at hx ⊢
    exact fun hxs ↦ hx x hxs rfl
  -- step three: round the weights to a common denominator
  obtain ⟨m, hmpos, hle₃⟩ :=
    exists_nat_weights_wassersteinEDist_le (ν := ν₂) measurable_edist hp0 hp_top hnull₂ hquarter'
  set ν₃ : Measure X := (∑ x ∈ s.image T, (m x : ℝ≥0∞))⁻¹ •
    ∑ x ∈ s.image T, (m x : ℝ≥0∞) • Measure.dirac x with hν₃_def
  have hmsum : ∑ x ∈ s.image T, ((m x : ℕ) : ℝ≥0∞) = ((∑ x ∈ s.image T, m x : ℕ) : ℝ≥0∞) :=
    (Nat.cast_sum _ _).symm
  have hnull₃ : ν₃ ((↑(s.image T) : Set X)ᶜ) = 0 := by
    have hzero : (∑ x ∈ s.image T, (m x : ℝ≥0∞) • Measure.dirac x)
        ((↑(s.image T) : Set X)ᶜ) = 0 := by
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      rw [Measure.smul_apply, Measure.dirac_apply' _ (s.image T).measurableSet.compl,
        Set.indicator_of_notMem (by simpa using hx), smul_zero]
    rw [hν₃_def, Measure.smul_apply, hzero, smul_zero]
  have hprob₃ : IsProbabilityMeasure ν₃ := by
    refine ⟨?_⟩
    have hmass : (∑ x ∈ s.image T, (m x : ℝ≥0∞) • Measure.dirac x) univ
        = ((∑ x ∈ s.image T, m x : ℕ) : ℝ≥0∞) := by
      rw [Measure.coe_finsetSum, Finset.sum_apply, ← hmsum]
      exact Finset.sum_congr rfl fun x _ ↦ by simp
    rw [hν₃_def, Measure.smul_apply, hmass, smul_eq_mul, hmsum,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hmpos.ne') (ENNReal.natCast_ne_top _)]
  obtain ⟨x₁, hx₁⟩ : (s.image T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro he
    rw [he] at hmpos
    simp at hmpos
  have hmom₃ : HasFiniteMoment p ν₃ := hasFiniteMoment_of_ae_mem_finset x₁ (mem_ae_iff.2 hnull₃)
  -- the approximating law belongs to the countable family
  have hrange : ν₃ ∈ Set.range G := by
    have hexists : ∀ x ∈ s.image T, ∃ i, u i = x := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
      exact hTu y
    choose! i hi using hexists
    have hinj : ∀ x ∈ s.image T, ∀ y ∈ s.image T, (i x, m x) = (i y, m y) → x = y := by
      intro x hx y hy hxy
      have hix : i x = i y := congrArg Prod.fst hxy
      rw [← hi x hx, ← hi y hy, hix]
    refine ⟨(s.image T).image fun x ↦ (i x, m x), ?_⟩
    simp only [hG_def, hν₃_def]
    rw [Finset.sum_image hinj, Finset.sum_image hinj]
    exact congrArg₂ _ rfl (Finset.sum_congr rfl fun x hx ↦ by rw [hi x hx])
  have hcoe : ((mk (⟨ν₃, hprob₃⟩ : ProbabilityMeasure X) hmom₃ : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν₃, hprob₃⟩ := coe_mk _ _
  refine ⟨mk ⟨ν₃, hprob₃⟩ hmom₃, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, dist_def, hcoe]
    have htri : wassersteinEDist p ((μ : ProbabilityMeasure X) : Measure X) ν₃ ≤
        ENNReal.ofReal (3 * (r / 4)) := by
      have h₁₃ : wassersteinEDist p ν₁ ν₃ ≤
          ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) :=
        (wassersteinEDist_triangle measurable_edist hp1 ν₁ ν₂ ν₃).trans (add_le_add hle₂ hle₃)
      refine (wassersteinEDist_triangle measurable_edist hp1
        ((μ : ProbabilityMeasure X) : Measure X) ν₁ ν₃).trans ?_
      refine (add_le_add hle₁ h₁₃).trans_eq ?_
      rw [← ENNReal.ofReal_add hquarter.le (by positivity),
        ← ENNReal.ofReal_add hquarter.le (by positivity)]
      ring_nf
    refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) htri) ?_
    linarith
  · rw [Set.mem_preimage, hcoe]
    exact hrange

/-- The separability of `P_p (X)` as an instance, reading the finiteness of the exponent off a
`Fact`, as the metric structure reads off `Fact (1 ≤ p)`. -/
instance instSeparableSpace [Fact (p ≠ ∞)] :
    TopologicalSpace.SeparableSpace (WassersteinSpace p X) :=
  separableSpace Fact.out

end Separable

end WassersteinSpace

end TauCeti
