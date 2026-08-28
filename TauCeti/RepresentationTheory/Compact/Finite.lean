/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Invariants
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite groups: normalized Haar measure is the uniform measure

A finite group carrying the discrete topology is a compact topological group, so the whole
compact-group development applies to it. This file identifies the objects it produces with the
elementary finite-group ones: normalized Haar measure is `|G|⁻¹ • Measure.count`, the Haar integral
is the group average `|G|⁻¹ ∑ g, F g`, and the Haar average of the action operators of a
representation is the finite group average `|G|⁻¹ ∑ g, π g`, the Reynolds operator. (Mathlib's
algebraic counterpart of that operator is `Representation.averageMap`; this file does not connect
to it, only to the explicit sum.)

The measure statement is proved without appealing to the Haar property of the counting measure, and
in fact without any topology: left invariance alone forces all singletons of a finite group to have
the same measure `c`, so a left-invariant probability measure is `c • Measure.count` by
`MeasureTheory.Measure.ext_of_singleton`, and evaluating both sides on `Set.univ` computes
`c = |G|⁻¹` from the total mass being `1`.

Everything downstream then follows by rewriting: `MeasureTheory.integral_fintype` turns a Bochner
integral against a measure on a finite space into the sum of its singleton weights, which the
measure computation has just identified.

## Main results

* `TauCeti.eq_smul_count_of_isMulLeftInvariant`: **a left-invariant probability measure on a finite
  group is the normalized counting measure** `|G|⁻¹ • Measure.count`. Since normalized Haar measure
  is one, `TauCeti.haarProb_eq_smul_count` is the special case that identifies it, and it also says
  that no other Haar probability measure exists; `TauCeti.haarProb_singleton` and
  `TauCeti.haarProb_apply` read off the measure of a singleton and of an arbitrary set.
* `TauCeti.haarProb_eq_uniformOn_univ`: it is Mathlib's uniform probability measure
  `ProbabilityTheory.uniformOn Set.univ`.
* `TauCeti.integral_haarProb`: **the Haar integral is the group average** `|G|⁻¹ • ∑ g, F g`, with
  `TauCeti.integral_haarProb_eq_inv_mul_sum` its `𝕜`-scalar form; `TauCeti.haarAverage_eq_smul_sum`
  says the same for the bundled averaging operator.
* `ContRepresentation.haarAverageMap_eq_smul_sum`: the Haar average of the action operators is the
  finite average `|G|⁻¹ • ∑ g, π g v`.

The counting identity `|G|⁻¹ ∑ g, χ_π g = dim V^G` that the compact-group character integral
generalizes then costs one rewrite. It is not given a name: Mathlib already proves it, as
`Representation.card_inv_mul_sum_char_eq_finrank`, and that lemma closes the `ContRepresentation`
statement outright, so only the route through the compact theory is new. The route is exhibited by
the anonymous `example` closing the file.

## Implementation notes

Finiteness is spelled `[Finite G]` for the measure-theoretic statements and `[Fintype G]` only from
`TauCeti.integral_haarProb` on, where a sum over `Finset.univ` appears in the statement itself and a
`Fintype` instance recovered from `Finite` inside a proof would not be the one indexing that sum.
Cardinalities are written `Nat.card G` throughout, matching the rest of the roadmap;
`Nat.card_eq_fintype_card` converts.

`IsTopologicalGroup G`, `CompactSpace G`, `T2Space G` and `MeasurableSingletonClass G` are all
found by instance search from `[DiscreteTopology G]`, `[Finite G]` and `[BorelSpace G]`, so no
extra hypotheses are carried.

The scalar in the averaged sums is real, not `𝕜`: the Bochner integral being specialized is an
`ℝ`-integral, and `V` is not assumed to be an `ℝ`-`𝕜`-scalar tower. The conversion is confined to
`TauCeti.integral_haarProb_eq_inv_mul_sum`, whose integrand is `𝕜`-valued and which uses
`RCLike.real_smul_eq_coe_mul`; the character count then goes through that lemma.

## References

This is the measure-identification and character-count part of the worked example "finite groups
recover the character theory" of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md):
`haarProb G` is the normalized counting measure `|G|⁻¹ • count`, and the counting identity
`dim V^G = |G|⁻¹ ∑ g, χ_π g` is the finite shadow of
`ContRepresentation.integral_character_eq_finrank_invariants`, matching Mathlib's
`FDRep.average_char_eq_finrank_invariants` for the purely algebraic theory. The remaining
specializations the roadmap item asks for — the `L²` theory, Maschke, Schur and character
orthonormality, and Peter-Weyl — are not treated here.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section LeftInvariant

variable {G : Type*} [Group G] [Finite G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **A left-invariant probability measure on a finite group is the normalized counting measure.**

Left translation by `g` carries `{1}` to `{g}`, so left invariance forces all singletons to have
the same mass `c` and hence `μ = c • Measure.count` by `MeasureTheory.Measure.ext_of_singleton`;
evaluating both sides on `Set.univ` computes `c = |G|⁻¹` from the total mass being `1`. Neither a
topology nor the Haar property of the counting measure is needed. -/
theorem eq_smul_count_of_isMulLeftInvariant (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsProbabilityMeasure μ] : μ = (Nat.card G : ℝ≥0∞)⁻¹ • Measure.count := by
  have hone : ∀ g : G, μ {g} = μ {(1 : G)} := fun g ↦ by
    have h : (fun x ↦ g * x) ⁻¹' {g} = {(1 : G)} := by
      ext x
      simp
    rw [← measure_preimage_mul μ g {g}, h]
  have hsmul : μ = μ {(1 : G)} • Measure.count := by
    refine Measure.ext_of_singleton fun a ↦ ?_
    rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one, hone a]
  have hmass : μ {(1 : G)} * (Nat.card G : ℝ≥0∞) = 1 := by
    have h := congrArg (fun ν : Measure G ↦ ν univ) hsmul
    simpa [Measure.count_univ, ENat.card_eq_coe_natCard] using h.symm
  rw [hsmul, ENNReal.eq_inv_of_mul_eq_one_left hmass]

end LeftInvariant

section FiniteGroup

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Normalized Haar measure on a finite discrete group is the normalized counting measure.**
Because `TauCeti.eq_smul_count_of_isMulLeftInvariant` needs only left invariance and total mass
one, this also says that no other Haar probability measure on `G` exists. -/
theorem haarProb_eq_smul_count :
    haarProb G = (Nat.card G : ℝ≥0∞)⁻¹ • Measure.count :=
  eq_smul_count_of_isMulLeftInvariant (haarProb G)

/-- **The normalized Haar measure of a singleton in a finite discrete group is `|G|⁻¹`.** -/
@[simp]
theorem haarProb_singleton (g : G) : haarProb G {g} = (Nat.card G : ℝ≥0∞)⁻¹ := by
  rw [haarProb_eq_smul_count G, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

/-- The normalized Haar measure of a set in a finite discrete group is the fraction of the group it
occupies. -/
theorem haarProb_apply (s : Set G) : haarProb G s = (s.ncard : ℝ≥0∞) / Nat.card G := by
  rw [haarProb_eq_smul_count G, Measure.smul_apply,
    Measure.count_apply_finite s s.toFinite, smul_eq_mul, ENNReal.div_eq_inv_mul,
    Set.ncard_eq_toFinset_card s s.toFinite]

/-- The real-valued normalized Haar measure of a singleton, in the form
`MeasureTheory.integral_fintype` consumes. -/
@[simp]
theorem haarProb_real_singleton (g : G) : (haarProb G).real {g} = (Nat.card G : ℝ)⁻¹ := by
  rw [measureReal_def, haarProb_singleton G g]
  simp

/-- The real-valued normalized Haar measure of a set in a finite discrete group. -/
theorem haarProb_real_apply (s : Set G) : (haarProb G).real s = s.ncard / Nat.card G := by
  rw [measureReal_def, haarProb_apply G s, ENNReal.toReal_div]
  simp

/-- Normalized Haar measure on a finite discrete group is Mathlib's uniform probability measure
`ProbabilityTheory.uniformOn Set.univ`. -/
theorem haarProb_eq_uniformOn_univ : haarProb G = ProbabilityTheory.uniformOn Set.univ := by
  obtain ⟨_⟩ := nonempty_fintype G
  refine Measure.ext_of_singleton fun a ↦ ?_
  rw [haarProb_singleton G a, ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
    Nat.card_eq_fintype_card, one_div]

end FiniteGroup

section FintypeGroup

variable (G : Type*) [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **The Haar integral over a finite discrete group is the group average.** This is what makes
every averaging statement of the compact theory specialize to its finite-group counterpart. -/
theorem integral_haarProb (F : G → V) :
    ∫ g, F g ∂haarProb G = (Nat.card G : ℝ)⁻¹ • ∑ g, F g := by
  rw [integral_fintype Integrable.of_finite, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [haarProb_real_singleton G g]

/-- **The Haar integral of a `𝕜`-valued function over a finite discrete group is the group
average**, in the `𝕜`-scalar form the character theory consumes: `TauCeti.integral_haarProb` states
the same identity with the real scalar `(|G| : ℝ)⁻¹` acting on a general normed space. -/
theorem integral_haarProb_eq_inv_mul_sum {𝕜 : Type*} [RCLike 𝕜] (F : G → 𝕜) :
    ∫ g, F g ∂haarProb G = (Nat.card G : 𝕜)⁻¹ * ∑ g, F g := by
  rw [integral_haarProb G F, RCLike.real_smul_eq_coe_mul]
  simp

/-- The bundled Haar averaging operator of a finite discrete group is the group average. -/
theorem haarAverage_eq_smul_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V]
    [SMulCommClass ℝ 𝕜 V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = (Nat.card G : ℝ)⁻¹ • ∑ g, f g := by
  rw [haarAverage_apply, integral_haarProb]

end FintypeGroup

end TauCeti

open MeasureTheory TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Average

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

/-- **The Haar average of the action operators of a finite discrete group is the finite group
average** `|G|⁻¹ ∑ g, π g`, the Reynolds operator whose role normalized Haar measure plays in
`ContRepresentation.haarAverageMap`. Mathlib's algebraic counterpart of that operator is
`Representation.averageMap`; this lemma relates the Haar average to the explicit sum only. -/
theorem haarAverageMap_eq_smul_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v : V) :
    haarAverageMap π hπ v = (Nat.card G : ℝ)⁻¹ • ∑ g, π g v := by
  rw [haarAverageMap_apply, integral_haarProb]

end Average

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis: a finite-dimensional normed space over an
`RCLike` field is already complete. As in
`TauCeti/RepresentationTheory/Compact/Invariants.lean`, Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance. -/
local instance instCompleteSpaceFinite : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

/- **The finite-group counting identity** `|G|⁻¹ ∑ g, χ_π g = dim V^G`, the specialization of
`ContRepresentation.integral_character_eq_finrank_invariants` to a finite discrete group, and the
statement Mathlib proves algebraically as `Representation.card_inv_mul_sum_char_eq_finrank` (see
also `FDRep.average_char_eq_finrank_invariants`).

Mathlib's lemma, applied to `π.toRepresentation`, already closes this goal, so no name is claimed
for it here; what the compact theory contributes is the derivation below, in which the count is the
Haar integral of the character read off by `TauCeti.integral_haarProb_eq_inv_mul_sum`. -/
example (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g = (Module.finrank 𝕜 π.invariants : 𝕜) := by
  rw [← integral_character_eq_finrank_invariants π hπ, integral_haarProb_eq_inv_mul_sum]

end Trace

end ContRepresentation
