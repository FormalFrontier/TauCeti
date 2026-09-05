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
the prescribed accuracy. The first is
`TauCeti.exists_ae_mem_finset_wassersteinEDist_le`, already available: a finite-moment law is
close to a law carried by a finite set. The second, `TauCeti.exists_map_range_wassersteinEDist_le`,
pushes that law onto terms of the dense sequence, by the measurable map sending a point to the
first term of the sequence within the accuracy of it. The third,
`TauCeti.exists_nat_weights_wassersteinEDist_le`, rounds the finitely many weights to multiples of
a common unit `1 / M`.

The rounding rests on an elementary transport estimate of independent interest,
`TauCeti.wassersteinEDist_add_smul_dirac_le`: keeping the part `σ` of a measure `σ + τ` in place
and collapsing the rest onto a single point `x₀` is a coupling, so it costs at most the `L^p (τ)`
seminorm of the distance to `x₀`. Rounding each weight of a finitely supported law *down* to a
multiple of `1 / M`, except at one atom `x₀` of its carrier which absorbs everything the others
give up, is exactly of that shape, and the mass moved is below `1 / M` at each of the finitely
many atoms.

The exponent must be finite. Finitely supported laws are not `W_∞`-dense on a general separable
metric space, and indeed `P_∞ (X)` need not be separable.

## Main statements

* `TauCeti.wassersteinEDist_add_smul_dirac_le` — collapsing a part of a measure onto one point;
* `TauCeti.wassersteinEDist_sum_smul_dirac_le` — its reading for the weights of a finitely
  supported law;
* `TauCeti.exists_map_range_wassersteinEDist_le` — quantization onto a dense sequence;
* `TauCeti.exists_nat_weights_wassersteinEDist_le` — rounding the weights to a common denominator;
* `TauCeti.WassersteinSpace.separableSpace` — separability of `P_p (X)` for `1 ≤ p < ∞`, with
  `TauCeti.WassersteinSpace.instSeparableSpace` its instance form.

## Implementation notes

The ground distance enters as an explicit `Measurable fun z : X × X ↦ edist z.1 z.2` hypothesis
wherever the coupling estimates are stated, as elsewhere in this directory, and the separability
theorem reads it off the Borel structure. Finiteness of the exponent cannot be an instance
argument, so `TauCeti.WassersteinSpace.separableSpace` takes it explicitly and the instance reads
it off a `Fact`, exactly as the metric structure of `TauCeti.WassersteinSpace` reads `1 ≤ p` off
`Fact (1 ≤ p)`.

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

section Perturbation

variable [PseudoEMetricSpace X]

/-- **Moving a piece of mass to a single point.** Replacing the part `τ` of the measure `σ + τ`
by the Dirac mass at `x₀` carrying the same total mass costs at most the `L^p (τ)` seminorm of
the distance to `x₀`: the plan that leaves `σ` where it is and sends every point of `τ` to `x₀`
is a coupling of the two measures, and its objective is exactly that seminorm. -/
theorem wassersteinEDist_add_smul_dirac_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞) (σ τ : Measure X) (x₀ : X) :
    wassersteinEDist p (σ + τ) (σ + τ univ • Measure.dirac x₀) ≤
      eLpNorm (fun x ↦ edist x x₀) p τ := by
  set f : X × X → ℝ≥0∞ := fun z ↦ edist z.1 z.2 with hf_def
  have hdiag : Measurable fun x : X ↦ (x, x) := measurable_id.prodMk measurable_id
  have hpair : Measurable fun x : X ↦ (x, x₀) := measurable_id.prodMk measurable_const
  have hcoupling : IsCoupling (σ.map (fun x ↦ (x, x)) + τ.map (fun x ↦ (x, x₀)))
      (σ + τ) (σ + τ univ • Measure.dirac x₀) := by
    constructor
    · rw [Measure.fst_add, Measure.fst, Measure.fst, Measure.map_map measurable_fst hdiag,
        Measure.map_map measurable_fst hpair]
      simp [Function.comp_def]
    · rw [Measure.snd_add, Measure.snd, Measure.snd, Measure.map_map measurable_snd hdiag,
        Measure.map_map measurable_snd hpair]
      simp [Function.comp_def, Measure.map_const]
  refine (wassersteinEDist_le hcoupling p).trans_eq ?_
  set E : Set (X × X) := {z | f z ≠ 0} with hE_def
  have hE : MeasurableSet E := hd (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have hAE : σ.map (fun x ↦ (x, x)) E = 0 := by
    have hpre : (fun x : X ↦ (x, x)) ⁻¹' E = ∅ := by
      ext x
      simp [hE_def, hf_def]
    rw [Measure.map_apply hdiag hE, hpre, measure_empty]
  have hind : E.indicator f = f := by
    funext z
    by_cases hz : f z = 0
    · rw [Set.indicator_of_notMem (by simpa [hE_def] using hz), hz]
    · exact Set.indicator_of_mem hz f
  calc eLpNorm f p (σ.map (fun x ↦ (x, x)) + τ.map (fun x ↦ (x, x₀)))
      = eLpNorm (E.indicator f) p (σ.map (fun x ↦ (x, x)) + τ.map (fun x ↦ (x, x₀))) := by
        rw [hind]
    _ = eLpNorm f p ((σ.map (fun x ↦ (x, x)) + τ.map (fun x ↦ (x, x₀))).restrict E) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hE
    _ = eLpNorm f p ((τ.map (fun x ↦ (x, x₀))).restrict E) := by
        rw [Measure.restrict_add, Measure.restrict_eq_zero.2 hAE, zero_add]
    _ = eLpNorm (E.indicator f) p (τ.map (fun x ↦ (x, x₀))) :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hE).symm
    _ = eLpNorm f p (τ.map (fun x ↦ (x, x₀))) := by rw [hind]
    _ = eLpNorm (fun x ↦ edist x x₀) p τ :=
        eLpNorm_map_measure hd.aestronglyMeasurable hpair.aemeasurable

/-- **Perturbing the weights of a finitely supported law.** If the weights `b` are below the
weights `a` away from a distinguished point `x₀` of the carrier and the two total masses agree,
then all the excess mass travels to `x₀`, so the transport cost is at most the `L^p` seminorm of
the distance to `x₀` against the excess measure. -/
theorem wassersteinEDist_sum_smul_dirac_le
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (p : ℝ≥0∞) {s : Finset X} {x₀ : X}
    (hx₀ : x₀ ∈ s) {a b : X → ℝ≥0∞} (hab : ∀ y ∈ s, y ≠ x₀ → b y ≤ a y)
    (hfin : ∀ y ∈ s, a y ≠ ∞) (hsum : ∑ x ∈ s, b x = ∑ x ∈ s, a x) :
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
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun y hy ↦ hfin y (Finset.mem_of_mem_erase hy))
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
  refine (wassersteinEDist_sum_smul_dirac_le hd p hx₀ hab (fun y _ ↦ ha_fin y)
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
