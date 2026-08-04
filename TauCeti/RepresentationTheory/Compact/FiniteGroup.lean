/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Compact.Character
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The compact theory over a finite group

A finite group with the discrete topology is a compact group, so the whole compact-group
development applies to it. This file identifies what it says there: normalized Haar measure is
**normalized counting measure**, the Haar integral is `|G|⁻¹` times a finite sum, and the `L²`
orthogonality relations for characters become the classical orthogonality relations for the
characters of a finite group.

Nothing here is a new theorem about compact groups; it is the calibration that keeps the
normalizations honest, the acceptance criterion "finite groups recover character theory" of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
`TauCeti.ContRepresentation.card_inv_mul_sum_character_mul_character_inv_self` and
`TauCeti.ContRepresentation.card_inv_mul_sum_character_mul_character_inv` are literally the two
halves of Mathlib's `Representation.char_orthonormal`, obtained from the compact-group proof rather
than from the averaging idempotent of the finite-group proof.

## Main results

* `TauCeti.haarProb_apply_singleton`: every point of a finite group has normalized Haar measure
  `|G|⁻¹`.
* `TauCeti.haarProb_eq_smul_count`: `haarProb G = |G|⁻¹ • MeasureTheory.Measure.count`.
* `TauCeti.integral_haarProb_eq_inv_card_smul_sum` and
  `TauCeti.haarAverage_eq_inv_card_smul_sum`: the Haar integral and the Haar average of a function
  on a finite group are its arithmetic mean.
* `TauCeti.ContRepresentation.card_inv_mul_sum_matrixCoeff_mul_conj_matrixCoeff`: the first Schur
  orthogonality relation as a finite sum.
* `TauCeti.ContRepresentation.card_inv_mul_sum_character_mul_character_inv_self` and
  `TauCeti.ContRepresentation.card_inv_mul_sum_character_mul_character_inv`: the two character
  orthogonality relations as finite sums.

## Implementation notes

The hypotheses are `[DiscreteTopology G]` and `[Finite G]`; compactness and the topological group
structure are then instances, and `[MeasurableSpace G] [BorelSpace G]` is carried exactly as in
`TauCeti.haarProb`. Discreteness is what makes points measurable — it supplies the
`MeasurableSingletonClass G` instance every statement below rests on — so it is a genuine
hypothesis and not a normalization of the topology on a finite group.

Sums over `G` are indexed by `Finset.univ`, so the finite-sum results ask for `[Fintype G]` where
`[Finite G]` suffices for the measure-level ones.
-/

public section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

namespace TauCeti

section Measure

variable (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Normalized Haar measure of a point of a finite group is `|G|⁻¹`.** Left invariance makes all
the singleton measures equal, and there are `|G|` of them summing to the total mass `1`. -/
theorem haarProb_apply_singleton (g : G) : haarProb G {g} = (Nat.card G : ℝ≥0∞)⁻¹ := by
  classical
  have hone : ∀ x : G, haarProb G {x} = haarProb G {1} := by
    intro x
    have hpre : (fun h ↦ x * h) ⁻¹' ({x} : Set G) = {1} := by
      ext y
      simp
    have := measure_preimage_mul (haarProb G) x ({x} : Set G)
    rwa [hpre, eq_comm] at this
  have hdisj : Pairwise (Function.onFun Disjoint fun x : G ↦ ({x} : Set G)) := fun x y hxy ↦
    Set.disjoint_singleton.2 hxy
  have htsum : ∑' x : G, haarProb G {x} = 1 := by
    rw [← measure_iUnion hdisj fun x ↦ measurableSet_singleton x, Set.iUnion_of_singleton,
      haarProb_apply_univ]
  have hfin : Fintype G := Fintype.ofFinite G
  have hcard : haarProb G {1} * (Nat.card G : ℝ≥0∞) = 1 := by
    rw [mul_comm]
    calc (Nat.card G : ℝ≥0∞) * haarProb G {1}
        = ∑ _x : G, haarProb G {1} := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ = ∑' x : G, haarProb G {x} := by rw [tsum_fintype]; exact (Finset.sum_congr rfl
          fun x _ ↦ (hone x).symm)
      _ = 1 := htsum
  rw [hone g, ENNReal.eq_inv_of_mul_eq_one_left hcard]

/-- **Normalized Haar measure on a finite group is normalized counting measure.** -/
theorem haarProb_eq_smul_count :
    haarProb G = (Nat.card G : ℝ≥0∞)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun g ↦ ?_
  rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one,
    haarProb_apply_singleton]

/-- The real-valued measure of a point, the form the Bochner integral consumes. -/
theorem measureReal_haarProb_singleton (g : G) :
    (haarProb G).real {g} = (Nat.card G : ℝ)⁻¹ := by
  rw [measureReal_def, haarProb_apply_singleton, ENNReal.toReal_inv, ENNReal.toReal_natCast]

end Measure

section Integral

variable (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Fintype G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **The Haar integral over a finite group is the arithmetic mean.** -/
theorem integral_haarProb_eq_inv_card_smul_sum (F : G → V) :
    ∫ g, F g ∂(haarProb G) = (Nat.card G : ℝ)⁻¹ • ∑ g, F g := by
  rw [integral_fintype (Integrable.of_finite (μ := haarProb G) (f := F)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [measureReal_haarProb_singleton]

/-- **Haar averaging over a finite group is the arithmetic mean.** -/
theorem haarAverage_eq_inv_card_smul_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = (Nat.card G : ℝ)⁻¹ • ∑ g, f g := by
  rw [haarAverage_apply, integral_haarProb_eq_inv_card_smul_sum]

end Integral

section Inner

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Fintype G]
  [MeasurableSpace G] [BorelSpace G]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `L²` inner product of two continuous functions on a finite group is the normalized sum of
their pointwise products. Mathlib's inner product is conjugate linear in its first argument, which
is where the conjugation sits. -/
theorem inner_toLp_eq_inv_card_mul_sum (F H : C(G, 𝕜)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ * ∑ g, H g * (starRingEnd 𝕜) (F g) := by
  rw [ContinuousMap.inner_toLp, integral_haarProb_eq_inv_card_smul_sum, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

end Inner

namespace ContRepresentation

section MatrixCoefficient

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Fintype G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 W] in
/-- **The `L²` inner product of two matrix coefficients of a finite group is a sum over the
group.** -/
theorem inner_matrixCoeffLp_eq_inv_card_mul_sum (ρ : ContRepresentation 𝕜 G W)
    (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ *
        ∑ g, matrixCoeff ρ hρ v' w' g * (starRingEnd 𝕜) (matrixCoeff π hπ v w g) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, inner_toLp_eq_inv_card_mul_sum]

/-- **The first Schur orthogonality relation for a finite group.** Averaging a matrix coefficient
of a unitary irreducible representation against the conjugate of another over `G` gives `d⁻¹` times
the product of the corresponding inner products, `d` the dimension.

This is the classical relation obtained from the compact-group
`TauCeti.ContRepresentation.schur_orthogonality_self` rather than from the finite-group averaging
idempotent. -/
theorem card_inv_mul_sum_matrixCoeff_mul_conj_matrixCoeff [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) (v₁ w₁ v₂ w₂ : V) :
    (Nat.card G : 𝕜)⁻¹ *
        ∑ g, matrixCoeff π hπ v₂ w₂ g * (starRingEnd 𝕜) (matrixCoeff π hπ v₁ w₁ g)
      = (Module.finrank 𝕜 V : 𝕜)⁻¹ * ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [← inner_matrixCoeffLp_eq_inv_card_mul_sum π hπ π hπ]
  exact schur_orthogonality_self π hπ hunitary hirr v₁ w₁ v₂ w₂

end MatrixCoefficient

section Character

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Fintype G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **The `L²` inner product of two characters of a finite group is the classical character
pairing.** Unitarity of `π` turns the conjugation supplied by the inner product into the inversion
`g ↦ g⁻¹` of Mathlib's `Representation.char_orthonormal`. -/
theorem inner_characterLp_eq_inv_card_mul_sum (hunitary : IsUnitary π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ * ∑ g, character ρ hρ g * character π hπ g⁻¹ := by
  rw [characterLp_def, characterLp_def, inner_toLp_eq_inv_card_mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ by
    rw [character_apply_inv π hπ hunitary g])

/-- **First orthogonality relation for the character of a finite group**, obtained by specializing
the compact-group relation `TauCeti.ContRepresentation.character_orthonormal_self`. This is the
diagonal half of Mathlib's `Representation.char_orthonormal`. -/
theorem card_inv_mul_sum_character_mul_character_inv_self [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g * character π hπ g⁻¹ = 1 := by
  rw [← inner_characterLp_eq_inv_card_mul_sum π hπ hunitary π hπ]
  exact character_orthonormal_self π hπ hunitary hirr

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **Second orthogonality relation for the characters of a finite group**, obtained by
specializing `TauCeti.ContRepresentation.character_orthonormal_distinct`. This is the off-diagonal
half of Mathlib's `Representation.char_orthonormal`; the hypothesis is the vanishing of the
intertwiners that Schur's lemma supplies for a pair of inequivalent irreducibles. -/
theorem card_inv_mul_sum_character_mul_character_inv (hunitary : IsUnitary π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    (hdistinct : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character ρ hρ g * character π hπ g⁻¹ = 0 := by
  rw [← inner_characterLp_eq_inv_card_mul_sum π hπ hunitary ρ hρ]
  exact character_orthonormal_distinct π hπ ρ hρ hunitary hdistinct

end Character

end ContRepresentation

end TauCeti
