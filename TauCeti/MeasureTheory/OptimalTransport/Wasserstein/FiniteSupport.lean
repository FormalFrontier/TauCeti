/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# Approximation of a finite-moment law by a finitely supported one

On a separable ground space every probability measure with finite `p`-moment can be pushed within
any prescribed Wasserstein accuracy by a quantizer, for every finite exponent `1 ≤ p < ∞`. When
singletons are measurable, these pushforwards are measures carried by finite sets. This file also
records the two standard consequences: the finitely supported laws are dense in
`TauCeti.WassersteinSpace p X` under the compatible standard-Borel and second-countability
hypotheses, and the `N`-point quantization error of a fixed law tends to `0`.

The approximating measures are produced by a *quantizer*: a measurable map `T : X → X` with
finitely many values, approximating the identity. The displacement bound
`TauCeti.wassersteinEDist_map_le` — the graph plan of `T` is a coupling of `μ` with `μ.map T`, so
the Wasserstein distance between them is at most the `L^p (μ)` seminorm of `x ↦ edist x (T x)` —
turns an estimate on the displacement into an estimate on the distance. The map itself sends `x`
to `u i`, for the least index `i` of a dense sequence `u` with `dist x (u i) < δ` when that index
is smaller than a cutoff `n`, and to `u 0` otherwise. The displacement is then at most `δ` off the
tail set of points whose least index is at least `n`, and those tail sets decrease to the empty
set, so the finite `p`-moment about `u 0` makes their contribution vanish by dominated
convergence.

This file also provides the finite-support transport estimate and common-denominator weight
rounding used to approximate a finitely supported law by one with rational weights, together with
the companion quantization onto the terms of a prescribed dense sequence, which sends a point to
the first term of the sequence within the prescribed accuracy of it.

The construction uses a finite exponent: at `p = ∞` a displacement that is small off a set of
small measure is not small in `L^∞`, and finitely supported laws need not be `W_∞`-dense on a
general separable metric space (for example, on a countably infinite discrete metric space).
The ground space is separable, which is where the dense sequence comes from.

## Support conventions

A quantizer statement — the map `T` takes finitely many values — is available on a pseudometric
ground space, whereas the assertion that a measure gives mass `0` to the complement of a finite
set is not: in a pseudometric space that complement need not be measurable. On an infinite type
with the zero pseudometric and its Borel structure, no probability measure vanishes on the
complement of a finite set. The measure-level statements therefore ask for measurable singletons,
which a metric ground space with its Borel structure supplies for free. For the same reason the
finite carrier is recorded as a `Finset X` whose complement is null, rather than through
`MeasureTheory.Measure.support`: on a pseudometric space the topological support of a Dirac law is
the whole ball of radius `0` around its atom, so it is not finite.

## Main statements

* `TauCeti.wassersteinEDist_map_le` — the displacement bound: `W_p (μ, T_* μ)` is at most the
  `L^p (μ)` seminorm of `x ↦ edist x (T x)`;
* `TauCeti.hasFiniteMoment_of_ae_mem_finset` — a law carried by a finite set has finite
  `p`-moment for every exponent;
* `TauCeti.wassersteinEDist_sum_smul_dirac_le` — a transport bound for perturbing the weights of a
  finitely supported law;
* `TauCeti.exists_nat_weights_wassersteinEDist_le` — approximation by weights with a common
  natural denominator;
* `TauCeti.exists_map_range_wassersteinEDist_le` — quantization onto a dense sequence: some
  measurable map with values among the terms of a dense sequence pushes `ν` to within `δ` of
  itself;
* `TauCeti.exists_map_wassersteinEDist_le` — the approximation theorem in quantizer form: some
  measurable map with finitely many values pushes `μ` to within `ε` of itself;
* `TauCeti.exists_ae_mem_finset_wassersteinEDist_le` — its measure form, with the approximating
  law carried by a finite set and again of finite `p`-moment, assuming measurable singletons;
* `TauCeti.WassersteinSpace.dense_setOfPred_ae_mem_finset` — the finitely supported laws are dense
  in `P_p (X)` on a pseudometric ground space with `[StandardBorelSpace X]`, `[BorelSpace X]`,
  and `[SecondCountableTopology X]`;
* `TauCeti.wassersteinQuantizationError` and `TauCeti.tendsto_wassersteinQuantizationError` — the
  `N`-point quantization error and its convergence to `0`.

## Implementation notes

`TauCeti.wassersteinQuantizationError` is an infimum over competitors, so it is defined without
any hypothesis on the ground space and carries no attainment claim: a best `N`-point quantizer
need not exist at this generality, and the rate at which the error decays is a separate question
with its own hypotheses. Only `TauCeti.tendsto_wassersteinQuantizationError` uses the
approximation theorem.

`TauCeti.exists_map_range_wassersteinEDist_le` takes the measurability of the ground distance
explicitly, so that a caller with a Borel structure can supply it and one without can still use
the estimate.

The approximation theorem is stated with a target accuracy `ε : ℝ≥0∞` rather than as a limit
along a sequence of quantizers, because the sequence of cutoffs is chosen after the radius and
the two are not indexed by a single parameter.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  the density of finitely supported laws in `P_p (X)` is used to reduce statements about general
  laws to finite ones.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §5.1.
* S. Graf and H. Luschgy, *Foundations of Quantization for Probability Distributions*, Lecture
  Notes in Mathematics 1730, Springer 2000, Chapter I, for the quantization error.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p : ℝ≥0∞}

section Perturbation

variable [PseudoEMetricSpace X]

/-- **Perturbing the weights of a finitely supported law.** If the weights `b` are below the
weights `a` away from a distinguished point `x₀` of the carrier and the two total masses agree,
then all the excess mass travels to `x₀`, so the transport cost is at most the `L^p` seminorm of
the distance to `x₀` against the excess measure. -/
theorem wassersteinEDist_sum_smul_dirac_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞) {s : Finset X} {x₀ : X}
    (hx₀ : x₀ ∈ s) {a b : X → ℝ≥0∞} (hab : ∀ y ∈ s, y ≠ x₀ → b y ≤ a y)
    (hfin : ∀ y ∈ s, y ≠ x₀ → a y ≠ ∞) (hsum : ∑ x ∈ s, b x = ∑ x ∈ s, a x) :
    wassersteinEDist p (∑ x ∈ s, a x • Measure.dirac x) (∑ x ∈ s, b x • Measure.dirac x) ≤
      eLpNorm (fun x ↦ edist x x₀) p (∑ y ∈ s, (a y - b y) • Measure.dirac y) := by
  classical
  have hab' : ∀ y ∈ s.erase x₀, b y ≤ a y := fun y hy ↦
    hab y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
  have hsplit : ∀ c : X → ℝ≥0∞,
      ∑ x ∈ s, c x • Measure.dirac x =
        c x₀ • Measure.dirac x₀ + ∑ y ∈ s.erase x₀, c y • Measure.dirac y := fun c ↦
    (Finset.add_sum_erase _ (fun x ↦ c x • Measure.dirac x) hx₀).symm
  have hbx₀ : b x₀ = a x₀ + ∑ y ∈ s.erase x₀, (a y - b y) := by
    have hfin' : ∑ y ∈ s.erase x₀, b y ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun y hy ↦
        hfin y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
        (Finset.sum_le_sum hab')
    have hsplit' : ∑ y ∈ s.erase x₀, a y
        = ∑ y ∈ s.erase x₀, b y + ∑ y ∈ s.erase x₀, (a y - b y) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y hy ↦ (add_tsub_cancel_of_le (hab' y hy)).symm
    have hs' : ∑ y ∈ s.erase x₀, b y + b x₀
        = ∑ y ∈ s.erase x₀, b y + (a x₀ + ∑ y ∈ s.erase x₀, (a y - b y)) := by
      rw [← Finset.add_sum_erase _ b hx₀, ← Finset.add_sum_erase _ a hx₀] at hsum
      rw [hsplit'] at hsum
      calc ∑ y ∈ s.erase x₀, b y + b x₀ = b x₀ + ∑ x ∈ s.erase x₀, b x := by ring
        _ = a x₀ + (∑ y ∈ s.erase x₀, b y + ∑ y ∈ s.erase x₀, (a y - b y)) := hsum
        _ = ∑ y ∈ s.erase x₀, b y + (a x₀ + ∑ y ∈ s.erase x₀, (a y - b y)) := by ring
    exact (ENNReal.add_right_inj hfin').1 hs'
  have hzero : a x₀ - b x₀ = 0 := tsub_eq_zero_of_le (hbx₀ ▸ le_self_add)
  have hexcess : ∑ y ∈ s, (a y - b y) • Measure.dirac y
      = ∑ y ∈ s.erase x₀, (a y - b y) • Measure.dirac y := by
    rw [hsplit (fun y ↦ a y - b y), hzero, zero_smul, zero_add]
  set σ : Measure X :=
    a x₀ • Measure.dirac x₀ + ∑ y ∈ s.erase x₀, b y • Measure.dirac y with hσ_def
  set τ : Measure X := ∑ y ∈ s.erase x₀, (a y - b y) • Measure.dirac y with hτ_def
  have hτuniv : τ univ = ∑ y ∈ s.erase x₀, (a y - b y) := by simp [hτ_def]
  have hsrc : ∑ x ∈ s, a x • Measure.dirac x = σ + τ := by
    rw [hsplit a, hσ_def, hτ_def, add_assoc, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun y hy ↦ ?_)
    rw [← add_smul, add_tsub_cancel_of_le (hab' y hy)]
  have htgt : ∑ x ∈ s, b x • Measure.dirac x = σ + τ univ • Measure.dirac x₀ := by
    rw [hsplit b, hσ_def, hτuniv, hbx₀, add_smul]
    abel
  rw [hsrc, htgt, hexcess]
  exact wassersteinEDist_add_smul_dirac_le hd p σ τ x₀

end Perturbation

section NatWeights

variable [PseudoMetricSpace X] [MeasurableSingletonClass X]

/-- **Rounding the weights to a common denominator.** A probability measure carried by a finite
set is approximated, in `p`-Wasserstein distance and for a finite exponent `p ≠ 0`, by measures
whose weights are the multiples of a common unit: those of the shape
`(∑ m)⁻¹ • ∑ m x • δ_x` for natural multiplicities `m`. -/
theorem exists_nat_weights_wassersteinEDist_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {ν : Measure X} [IsProbabilityMeasure ν] {s : Finset X} (hν : ν ((s : Set X)ᶜ) = 0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ m : X → ℕ, 0 < ∑ x ∈ s, m x ∧
      wassersteinEDist p ν
        ((∑ x ∈ s, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ s, (m x : ℝ≥0∞) • Measure.dirac x) ≤ ε := by
  classical
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨x₀, hx₀⟩ : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.coe_empty, compl_empty] at hν
    exact absurd hν (by simp)
  set a : X → ℝ≥0∞ := fun x ↦ ν {x}
  have hν_eq : ν = ∑ x ∈ s, a x • Measure.dirac x :=
    Measure.ae_mem_finset_iff.1 (mem_ae_iff.2 hν)
  have ha_sum : ∑ x ∈ s, a x = 1 := by
    have h : (∑ x ∈ s, a x • Measure.dirac x) univ = 1 := by rw [← hν_eq]; simp
    simpa using h
  have ha_fin : ∀ x, a x ≠ ∞ := fun x ↦ measure_ne_top ν _
  -- the total `p`-th power of the distances to the base point of the carrier
  set C : ℝ≥0∞ := ∑ y ∈ s, edist y x₀ ^ p.toReal with hC_def
  have hC : C ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun y _ ↦ ENNReal.rpow_ne_top_of_nonneg ht.le (edist_ne_top y x₀)
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact ⟨fun x ↦ if x = x₀ then 1 else 0, by simp [Finset.sum_ite_eq' s x₀, hx₀], le_top⟩
  -- a denominator large enough that the rounding error is below `ε`
  have hεt : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) hεtop).ne'
  obtain ⟨M, hM⟩ : ∃ M : ℕ, C / ε ^ p.toReal < M :=
    ENNReal.exists_nat_gt (by simp [ENNReal.div_eq_top, hC, hεt])
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · simp at hM
    · exact h
  have hM0 : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hMpos.ne'
  have hMtop : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  have hCM : C ≤ M * ε ^ p.toReal := by
    rw [← ENNReal.div_le_iff hεt (by simp [hεtop])]
    exact hM.le
  -- the rounded multiplicities
  set m : X → ℕ := fun x ↦
    if x = x₀ then M - ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (a y).toReal⌋₊
    else ⌊(M : ℝ) * (a x).toReal⌋₊ with hm_def
  have hfloor_le : ∀ y : X, ((⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) : ℝ≥0∞) ≤ M * a y := by
    intro y
    calc ((⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (⌊(M : ℝ) * (a y).toReal⌋₊ : ℝ) := by
          rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((M : ℝ) * (a y).toReal) :=
          ENNReal.ofReal_le_ofReal (Nat.floor_le (by positivity))
      _ = M * a y := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_toReal (ha_fin y)]
  have hlt_floor : ∀ y : X, (M : ℝ≥0∞) * a y ≤ (⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) + 1 := by
    intro y
    calc (M : ℝ≥0∞) * a y = ENNReal.ofReal ((M : ℝ) * (a y).toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_toReal (ha_fin y)]
      _ ≤ ENNReal.ofReal ((⌊(M : ℝ) * (a y).toReal⌋₊ : ℝ) + 1) :=
          ENNReal.ofReal_le_ofReal (Nat.lt_floor_add_one _).le
      _ = (⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) + 1 := by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
  have herase : ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (a y).toReal⌋₊ ≤ M := by
    have hcast : ((∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
      push_cast
      calc ∑ y ∈ s.erase x₀, ((⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) : ℝ≥0∞)
          ≤ ∑ y ∈ s.erase x₀, (M : ℝ≥0∞) * a y := Finset.sum_le_sum fun y _ ↦ hfloor_le y
        _ = (M : ℝ≥0∞) * ∑ y ∈ s.erase x₀, a y := by rw [Finset.mul_sum]
        _ ≤ (M : ℝ≥0∞) * 1 := by
            gcongr
            rw [← ha_sum]
            exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        _ = M := mul_one _
    exact_mod_cast hcast
  have hm_sum : ∑ x ∈ s, m x = M := by
    rw [← Finset.add_sum_erase _ m hx₀]
    have h₁ : m x₀ = M - ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (a y).toReal⌋₊ := by simp [hm_def]
    have h₂ : ∑ y ∈ s.erase x₀, m y = ∑ y ∈ s.erase x₀, ⌊(M : ℝ) * (a y).toReal⌋₊ :=
      Finset.sum_congr rfl fun y hy ↦ by simp [hm_def, Finset.ne_of_mem_erase hy]
    rw [h₁, h₂]
    omega
  refine ⟨m, by rw [hm_sum]; exact hMpos, ?_⟩
  -- the rounded weights, and the comparison with the original ones
  set b : X → ℝ≥0∞ := fun x ↦ (M : ℝ≥0∞)⁻¹ * m x with hb_def
  have hb_sum : ∑ x ∈ s, b x = 1 := by
    have hcast : ∑ x ∈ s, ((m x : ℕ) : ℝ≥0∞) = (M : ℝ≥0∞) := by rw [← Nat.cast_sum, hm_sum]
    rw [hb_def, ← Finset.mul_sum, hcast, ENNReal.inv_mul_cancel hM0 hMtop]
  have hab : ∀ y ∈ s, y ≠ x₀ → b y ≤ a y := by
    intro y _ hy
    have hmy : ((m y : ℕ) : ℝ≥0∞) ≤ (M : ℝ≥0∞) * a y := by
      simpa [hm_def, hy] using hfloor_le y
    calc b y = (M : ℝ≥0∞)⁻¹ * m y := rfl
      _ ≤ (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * a y) := by gcongr
      _ = a y := by rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 hMtop, one_mul]
  have hexc : ∀ y ∈ s, y ≠ x₀ → a y - b y ≤ (M : ℝ≥0∞)⁻¹ := by
    intro y _ hy
    rw [tsub_le_iff_left]
    have hmy : ((m y : ℕ) : ℝ≥0∞) = (⌊(M : ℝ) * (a y).toReal⌋₊ : ℕ) := by simp [hm_def, hy]
    have h := hlt_floor y
    rw [← hmy] at h
    calc a y = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * a y) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 hMtop, one_mul]
      _ ≤ (M : ℝ≥0∞)⁻¹ * ((m y : ℕ) + 1) := by gcongr
      _ = b y + (M : ℝ≥0∞)⁻¹ := by rw [mul_add, mul_one]
  -- the target measure, rewritten with the normalised weights
  have htarget : (∑ x ∈ s, (m x : ℝ≥0∞))⁻¹ • ∑ x ∈ s, (m x : ℝ≥0∞) • Measure.dirac x
      = ∑ x ∈ s, b x • Measure.dirac x := by
    have hsm : ∑ x ∈ s, ((m x : ℕ) : ℝ≥0∞) = (M : ℝ≥0∞) := by rw [← Nat.cast_sum, hm_sum]
    rw [hsm, Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ (smul_smul _ _ _)
  rw [hν_eq, htarget]
  refine (wassersteinEDist_sum_smul_dirac_le hd p hx₀ hab (fun y _ _ ↦ ha_fin y)
    (hb_sum.trans ha_sum.symm)).trans ?_
  -- the excess mass is at most `1 / M` at each atom, so its `L^p` seminorm is below `ε`
  refine (ENNReal.rpow_le_rpow_iff ht).1 ?_
  rw [eLpNorm_rpow_eq_lintegral hp0 hp]
  have hint : ∫⁻ x, edist x x₀ ^ p.toReal ∂(∑ y ∈ s, (a y - b y) • Measure.dirac y)
      = ∑ y ∈ s, (a y - b y) * edist y x₀ ^ p.toReal := by
    simp [lintegral_smul_measure]
  rw [hint]
  calc ∑ y ∈ s, (a y - b y) * edist y x₀ ^ p.toReal
      ≤ ∑ y ∈ s, (M : ℝ≥0∞)⁻¹ * edist y x₀ ^ p.toReal := by
        refine Finset.sum_le_sum fun y hy ↦ ?_
        rcases eq_or_ne y x₀ with rfl | hyx
        · simp [ENNReal.zero_rpow_of_pos ht]
        · gcongr
          exact hexc y hy hyx
    _ = (M : ℝ≥0∞)⁻¹ * C := by rw [hC_def, Finset.mul_sum]
    _ ≤ (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * ε ^ p.toReal) := by gcongr
    _ = ε ^ p.toReal := by rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 hMtop, one_mul]

end NatWeights

section DenseRange

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] {u : ℕ → X}

/-- **Quantizing to a dense sequence.** A probability measure is within any prescribed accuracy
of its pushforward along a measurable map taking values in the range of a dense sequence: sending
a point to the first term of the sequence closer to it than the accuracy is such a map. -/
theorem exists_map_range_wassersteinEDist_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hu : DenseRange u) {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure X) [IsProbabilityMeasure ν] (p : ℝ≥0∞) :
    ∃ T : X → X, Measurable T ∧ (∀ x, T x ∈ Set.range u) ∧
      wassersteinEDist p ν (ν.map T) ≤ ENNReal.ofReal δ := by
  classical
  have hidx : ∀ x : X, ∃ i, dist x (u i) < δ := fun x ↦ Metric.denseRange_iff.1 hu x δ hδ
  have hidx_meas : Measurable fun x ↦ Nat.find (hidx x) :=
    measurable_find hidx fun _ ↦ measurableSet_ball
  have hT_meas : Measurable fun x ↦ u (Nat.find (hidx x)) :=
    Measurable.of_discrete.comp hidx_meas
  refine ⟨fun x ↦ u (Nat.find (hidx x)), hT_meas, fun x ↦ ⟨_, rfl⟩, ?_⟩
  refine (wassersteinEDist_map_le hd hT_meas.aemeasurable p).trans ?_
  refine le_trans (eLpNorm_mono_enorm (g := fun _ : X ↦ ENNReal.ofReal δ) fun x ↦ ?_) ?_
  · simpa [edist_dist] using ENNReal.ofReal_le_ofReal (Nat.find_spec (hidx x)).le
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · rw [eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero ν)]
      simp

end DenseRange

section Approximation

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  {μ : Measure X} {ε : ℝ≥0∞}

/-- **Approximation by a quantizer.** On a separable ground space, a probability measure with
finite `p`-moment and a finite exponent `1 ≤ p < ∞` is pushed to within any prescribed accuracy
of itself by a measurable map taking finitely many values. -/
theorem exists_map_wassersteinEDist_le (hp : 1 ≤ p) (hp_top : p ≠ ∞) [IsProbabilityMeasure μ]
    (hμ : HasFiniteMoment p μ) (hε : ε ≠ 0) :
    ∃ (s : Finset X) (T : X → X), Measurable T ∧ (∀ x, T x ∈ s) ∧
      wassersteinEDist p μ (μ.map T) ≤ ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  classical
  have : Nonempty X := ⟨(hasFiniteMoment_def.1 hμ).choose⟩
  -- the accuracy, halved and truncated to a finite nonzero value
  set c : ℝ≥0∞ := min ε 1 / 2 with hc_def
  have hmin_pos : 0 < min ε 1 := lt_min (pos_iff_ne_zero.2 hε) one_pos
  have hc_ne_top : c ≠ ∞ :=
    (ENNReal.div_lt_top (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)) two_ne_zero).ne
  have hc_ne_zero : c ≠ 0 := by
    simp only [hc_def, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hmin_pos.ne', ENNReal.ofNat_ne_top⟩
  set δ : ℝ := c.toReal with hδ_def
  have hδ : 0 < δ := ENNReal.toReal_pos hc_ne_zero hc_ne_top
  have hδc : ENNReal.ofReal δ = c := ENNReal.ofReal_toReal hc_ne_top
  -- the least index of a dense sequence within `δ` of a point
  set u : ℕ → X := TopologicalSpace.denseSeq X with hu_def
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  have hidx : ∀ x : X, ∃ i, dist x (u i) < δ := fun x ↦ Metric.denseRange_iff.1 hu x δ hδ
  set idx : X → ℕ := fun x ↦ Nat.find (hidx x) with hidx_def
  have hidx_spec : ∀ x, dist x (u (idx x)) < δ := fun x ↦ Nat.find_spec (hidx x)
  have hidx_meas : Measurable idx := measurable_find hidx fun k ↦ measurableSet_ball
  -- the ground distance to the basepoint `u 0`, and its `p`-th moment
  set f : X → ℝ≥0∞ := fun y ↦ edist (u 0) y with hf_def
  have hf_meas : Measurable f := measurable_edist.comp (measurable_const.prodMk measurable_id)
  have hmom : MemLp f p μ := hμ.memLp hf_meas.aestronglyMeasurable
  have hfin : ∫⁻ y, f y ^ p.toReal ∂μ ≠ ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_eq_self, lt_top_iff_ne_top] using
      (hmom.integrable_enorm_rpow hp0 hp_top).hasFiniteIntegral
  -- the tail sets decrease to the empty set, so their contribution vanishes
  set A : ℕ → Set X := fun n ↦ {x | n ≤ idx x} with hA_def
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n ↦ hidx_meas MeasurableSet.of_discrete
  have hA_tendsto : Tendsto (fun n ↦ ∫⁻ y, (A n).indicator (fun z ↦ f z ^ p.toReal) y ∂μ)
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ y ∂μ,
        Tendsto (fun n ↦ (A n).indicator (fun z ↦ f z ^ p.toReal) y) atTop (𝓝 0) := by
      refine .of_forall fun y ↦ Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (idx y)] with n hn
      exact (Set.indicator_of_notMem (by simpa [hA_def] using not_le.2 hn) _).symm
    have key := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun n y ↦ (A n).indicator (fun z ↦ f z ^ p.toReal) y) (f := fun _ ↦ (0 : ℝ≥0∞))
      (bound := fun z ↦ f z ^ p.toReal)
      (fun n ↦ (ENNReal.continuous_rpow_const.measurable.comp hf_meas).indicator (hA_meas n))
      (fun n ↦ .of_forall fun y ↦ Set.indicator_le_self _ _ y) hfin hlim
    simpa using key
  obtain ⟨n, hn⟩ : ∃ n, ∫⁻ y, (A n).indicator (fun z ↦ f z ^ p.toReal) y ∂μ ≤ c ^ p.toReal := by
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hA_tendsto _
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc_ne_zero) hc_ne_top)
    exact ⟨N, hN N le_rfl⟩
  -- the quantizer: the nearest listed point of index below the cutoff, and `u 0` beyond it
  set T : X → X := fun x ↦ if idx x < n then u (idx x) else u 0 with hT_def
  have hT_meas : Measurable T :=
    (Measurable.of_discrete (f := fun i : ℕ ↦ if i < n then u i else u 0)).comp hidx_meas
  refine ⟨(Finset.range (n + 1)).image u, T, hT_meas, fun x ↦ ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_range, hT_def]
    by_cases h : idx x < n
    · exact ⟨idx x, by omega, by simp [h]⟩
    · exact ⟨0, by omega, by simp [h]⟩
  -- the displacement is at most `δ` off the tail set, and at most the tail distance on it
  have hbound : ∀ x, edist x (T x) ≤ ENNReal.ofReal δ + (A n).indicator f x := by
    intro x
    by_cases h : idx x < n
    · refine le_trans ?_ (self_le_add_right _ _)
      have hTx : T x = u (idx x) := by simp [hT_def, h]
      rw [hTx, edist_dist]
      exact ENNReal.ofReal_le_ofReal (hidx_spec x).le
    · have hx : x ∈ A n := by simpa [hA_def] using not_lt.1 h
      have hTx : T x = u 0 := by simp [hT_def, h]
      rw [hTx, Set.indicator_of_mem hx, hf_def, edist_comm]
      exact self_le_add_left _ _
  have hind : eLpNorm ((A n).indicator f) p μ ≤ c := by
    refine (ENNReal.rpow_le_rpow_iff ht).1 ?_
    rw [eLpNorm_rpow_eq_lintegral hp0 hp_top]
    refine le_trans (le_of_eq (lintegral_congr fun y ↦ ?_)) hn
    by_cases hy : y ∈ A n
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos ht]
  calc wassersteinEDist p μ (μ.map T)
      ≤ eLpNorm (fun x ↦ edist x (T x)) p μ :=
        wassersteinEDist_map_le measurable_edist hT_meas.aemeasurable p
    _ ≤ eLpNorm ((fun _ : X ↦ ENNReal.ofReal δ) + (A n).indicator f) p μ :=
        eLpNorm_mono_enorm fun x ↦ by simpa using hbound x
    _ ≤ eLpNorm (fun _ : X ↦ ENNReal.ofReal δ) p μ + eLpNorm ((A n).indicator f) p μ :=
        eLpNorm_add_le aestronglyMeasurable_const
          (hf_meas.indicator (hA_meas n)).aestronglyMeasurable hp
    _ ≤ c + c := by
        refine add_le_add (le_of_eq ?_) hind
        rw [eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero μ)]
        simp [hδc]
    _ ≤ ε := by rw [hc_def, ENNReal.add_halves]; exact min_le_left _ _

variable [MeasurableSingletonClass X]

/-- **Approximation by a finitely supported law.** On a separable ground space with measurable
singletons, a probability measure with finite `p`-moment and a finite exponent `1 ≤ p < ∞` is
within any prescribed accuracy of a probability measure carried by a finite set, which again has
finite `p`-moment. -/
theorem exists_ae_mem_finset_wassersteinEDist_le (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [IsProbabilityMeasure μ] (hμ : HasFiniteMoment p μ) (hε : ε ≠ 0) :
    ∃ (s : Finset X) (ν : Measure X), IsProbabilityMeasure ν ∧ ν ((s : Set X)ᶜ) = 0 ∧
      HasFiniteMoment p ν ∧ wassersteinEDist p μ ν ≤ ε := by
  obtain ⟨s, T, hT, hTs, hle⟩ := exists_map_wassersteinEDist_le hp hp_top hμ hε
  have hnull : (μ.map T) ((s : Set X)ᶜ) = 0 := by
    rw [Measure.map_apply hT (s.measurableSet.compl)]
    convert measure_empty (μ := μ)
    exact eq_empty_of_forall_notMem fun x hx ↦ hx (hTs x)
  refine ⟨s, μ.map T, inferInstance, hnull, ?_, hle⟩
  refine hasFiniteMoment_of_ae_mem_finset (s := s) (hasFiniteMoment_def.1 hμ).choose ?_
  exact mem_ae_iff.2 hnull

end Approximation

namespace WassersteinSpace

variable [PseudoMetricSpace X] [StandardBorelSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **The finitely supported laws are dense in `P_p (X)`.** On a pseudometric ground space with
`[StandardBorelSpace X]`, a compatible `[BorelSpace X]`, and `[SecondCountableTopology X]`, and
for a finite exponent `1 ≤ p < ∞`, every finite-moment law is a Wasserstein limit of laws carried
by finite sets. -/
theorem dense_setOfPred_ae_mem_finset (hp_top : p ≠ ∞) :
    Dense {μ : WassersteinSpace p X |
      ∃ s : Finset X, ((μ : ProbabilityMeasure X) : Measure X) ((s : Set X)ᶜ) = 0} := by
  refine Metric.dense_iff.2 fun μ r hr ↦ ?_
  obtain ⟨s, ν, hν, hnull, hmom, hle⟩ :=
    exists_ae_mem_finset_wassersteinEDist_le (μ := ((μ : ProbabilityMeasure X) : Measure X))
      Fact.out hp_top μ.hasFiniteMoment
      (ε := ENNReal.ofReal (r / 2)) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
  have hcoe : ((mk (⟨ν, hν⟩ : ProbabilityMeasure X) hmom : WassersteinSpace p X) :
      ProbabilityMeasure X) = ⟨ν, hν⟩ := coe_mk _ _
  refine ⟨mk ⟨ν, hν⟩ hmom, ?_, s, by rw [hcoe]; exact hnull⟩
  rw [Metric.mem_ball, dist_comm, dist_def, hcoe]
  refine lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal (by positivity) hle) ?_
  linarith

end WassersteinSpace

section Quantization

variable [EDist X]

/-- The **`N`-point quantization error** of `μ` at exponent `p`: the infimum of the Wasserstein
distances from `μ` to the probability measures carried by a set of at most `N` points.

This is an infimum, not a minimum: a best `N`-point quantizer need not exist at this
generality. -/
def wassersteinQuantizationError (p : ℝ≥0∞) (N : ℕ) (μ : Measure X) : ℝ≥0∞ :=
  ⨅ (ν : Measure X) (_ : IsProbabilityMeasure ν)
    (_ : ∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0), wassersteinEDist p μ ν

variable {μ ν : Measure X} {N : ℕ}

/-- Every competitor bounds the quantization error from above. -/
theorem wassersteinQuantizationError_le (hν : IsProbabilityMeasure ν)
    (hs : ∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) :
    wassersteinQuantizationError p N μ ≤ wassersteinEDist p μ ν :=
  iInf_le_of_le ν (iInf_le_of_le hν (iInf_le _ hs))

/-- A bound valid for every admissible competitor bounds the quantization error from below. -/
theorem le_wassersteinQuantizationError {a : ℝ≥0∞}
    (h : ∀ (ν : Measure X) (_ : IsProbabilityMeasure ν),
      (∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) →
        a ≤ wassersteinEDist p μ ν) :
    a ≤ wassersteinQuantizationError p N μ :=
  le_iInf₂ fun ν hν ↦ le_iInf fun hs ↦ h ν hν hs

/-- The quantization error is below a strict threshold exactly when an admissible competitor is
below that threshold. -/
theorem wassersteinQuantizationError_lt_iff {a : ℝ≥0∞} :
    wassersteinQuantizationError p N μ < a ↔
      ∃ ν : Measure X, IsProbabilityMeasure ν ∧
        (∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) ∧
          wassersteinEDist p μ ν < a := by
  simp only [wassersteinQuantizationError, iInf_lt_iff, exists_prop]

/-- The quantization error decreases as more points are allowed. -/
theorem wassersteinQuantizationError_antitone :
    Antitone fun N ↦ wassersteinQuantizationError p N μ := by
  refine fun N M hNM ↦ le_iInf₂ fun ν hν ↦ le_iInf fun hs ↦ ?_
  obtain ⟨s, hcard, hnull⟩ := hs
  exact wassersteinQuantizationError_le hν ⟨s, hcard.trans hNM, hnull⟩

end Quantization

section QuantizationTendsto

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSingletonClass X] {μ : Measure X}

/-- **The quantization error vanishes.** On a separable ground space with measurable singletons
and for a finite exponent `1 ≤ p < ∞`, the `N`-point quantization error of a law with finite
`p`-moment tends to `0`. No rate is claimed: a quantitative bound needs further hypotheses on the
law. -/
theorem tendsto_wassersteinQuantizationError (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    [IsProbabilityMeasure μ] (hμ : HasFiniteMoment p μ) :
    Tendsto (fun N ↦ wassersteinQuantizationError p N μ) atTop (𝓝 0) := by
  refine (ENNReal.tendsto_atTop_zero_iff_le_of_antitone
    wassersteinQuantizationError_antitone).2 fun ε hε ↦ ?_
  obtain ⟨s, ν, hν, hnull, -, hle⟩ :=
    exists_ae_mem_finset_wassersteinEDist_le hp hp_top hμ hε.ne'
  exact ⟨s.card, (wassersteinQuantizationError_le hν ⟨s, le_rfl, hnull⟩).trans hle⟩

end QuantizationTendsto

end TauCeti
