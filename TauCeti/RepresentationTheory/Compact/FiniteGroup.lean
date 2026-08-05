/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Character
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The compact theory over a finite group

A finite topological group is compact, so the whole compact-group development applies to it. This
file identifies what it says there, for a finite group whose points are measurable: normalized Haar
measure is **normalized counting measure**, `L²(G)` is the space `G → 𝕜` of all functions on the
group, the Haar integral is `|G|⁻¹` times a finite sum, and the `L²` orthogonality relations for
characters become the classical orthogonality relations for the characters of a finite group.

Nothing here is a new theorem about compact groups; it is the calibration that keeps the
normalizations honest, the acceptance criterion "finite groups recover character theory" of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
`TauCeti.ContRepresentation.inner_characterLp_eq_card_inv_mul_sum` identifies the `L²` pairing of
two characters with the sum `|G|⁻¹ * ∑ g, χ_ρ g * χ_π g⁻¹` that Mathlib's
`Representation.char_orthonormal` evaluates, so the compact-group relations
`TauCeti.ContRepresentation.character_orthonormal_self` and
`TauCeti.ContRepresentation.character_orthonormal_distinct` land on Mathlib's statement on the
nose, with the compact-group proof in place of the averaging idempotent of the finite-group one.
Mathlib already proves those two relations for a finite group, so they are not restated here.

## Main definitions

* `TauCeti.haarProbLpEquivFun`: the identification `L²(G) ≃ₗ[𝕜] (G → 𝕜)` of the `L²` space of a
  finite group with the space of all functions on the group.

## Main results

* `TauCeti.haarProb_apply_singleton`: every point of a finite group has normalized Haar measure
  `|G|⁻¹`.
* `TauCeti.haarProb_eq_smul_count`: `haarProb G = |G|⁻¹ • MeasureTheory.Measure.count`.
* `TauCeti.integral_haarProb_eq_card_inv_smul_sum` and
  `TauCeti.haarAverage_eq_card_inv_smul_sum`: the Haar integral and the Haar average of a function
  on a finite group are its arithmetic mean.
* `TauCeti.inner_eq_card_inv_mul_sum`: the `L²` inner product of a finite group is the Hermitian
  pairing `|G|⁻¹ * ∑ g, H g * conj (F g)`.
* `TauCeti.ContRepresentation.card_inv_mul_sum_matrixCoeff_mul_star_matrixCoeff`: the first Schur
  orthogonality relation as a finite sum.
* `TauCeti.ContRepresentation.inner_characterLp_eq_card_inv_mul_sum`: the `L²` pairing of two
  characters as the finite sum of Mathlib's `Representation.char_orthonormal`.

## Implementation notes

The hypotheses are `[Finite G]` (or `[Fintype G]`, where a sum over `G` is written) together with
`[MeasurableSingletonClass G]`, on top of the `[IsTopologicalGroup G] [MeasurableSpace G]
[BorelSpace G]` that `TauCeti.haarProb` carries; compactness is then an instance. Measurability of
points is a genuine hypothesis, not a normalization: every statement below rests on it, and a
finite topological group need not have it — the Borel σ-algebra of an indiscrete group is trivial.
For the motivating case of the discrete topology it costs nothing, since Mathlib's
`OpensMeasurableSpace.toMeasurableSingletonClass` supplies it.
-/

public section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

namespace TauCeti

section Measure

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]

/-- **Normalized Haar measure of a point of a finite group is `|G|⁻¹`.** Left invariance makes all
the singleton measures equal, and there are `|G|` of them summing to the total mass `1`. -/
theorem haarProb_apply_singleton (g : G) : haarProb G {g} = (Nat.card G : ℝ≥0∞)⁻¹ := by
  classical
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
          fun x _ ↦ (Measure.haar_singleton (haarProb G) x).symm)
      _ = 1 := htsum
  rw [Measure.haar_singleton (haarProb G) g, ENNReal.eq_inv_of_mul_eq_one_left hcard]

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

/-- **No point of a finite group is null for normalized Haar measure**, so its almost-everywhere
filter is the whole of `⊤`: an almost-everywhere statement is a statement about every point. -/
theorem ae_haarProb_eq_top : ae (haarProb G) = ⊤ :=
  ae_eq_top.2 fun g ↦ by
    rw [haarProb_apply_singleton]
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

end Measure

section Integral

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **The Haar integral over a finite group is the arithmetic mean.** -/
theorem integral_haarProb_eq_card_inv_smul_sum (F : G → V) :
    ∫ g, F g ∂(haarProb G) = (Nat.card G : ℝ)⁻¹ • ∑ g, F g := by
  rw [integral_fintype (Integrable.of_finite (μ := haarProb G) (f := F)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [measureReal_haarProb_singleton]

/-- **Haar averaging over a finite group is the arithmetic mean.** -/
theorem haarAverage_eq_card_inv_smul_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V] (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = (Nat.card G : ℝ)⁻¹ • ∑ g, f g := by
  rw [haarAverage_apply, integral_haarProb_eq_card_inv_smul_sum]

end Integral

section Lp

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Almost-everywhere equality for normalized Haar measure on a finite group is equality. -/
theorem eq_of_ae_eq_haarProb {α : Type*} {F H : G → α} (h : F =ᵐ[haarProb G] H) : F = H := by
  rw [Filter.EventuallyEq, ae_haarProb_eq_top, Filter.eventually_top] at h
  exact funext h

/-- **The `L²` space of a finite group is the space of all functions on the group.** A class in
`Lp 𝕜 2 (haarProb G)` is represented by an honest function, since no point is null, and every
function on a finite group is square integrable.

The definition is exposed so that the two lemmas reading off the values of the equivalence and of
its inverse hold definitionally. -/
@[expose]
noncomputable def haarProbLpEquivFun (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Finite G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSingletonClass G] (𝕜 : Type*) [RCLike 𝕜] :
    Lp 𝕜 2 (haarProb G) ≃ₗ[𝕜] (G → 𝕜) where
  toFun F := ⇑F
  map_add' F H := eq_of_ae_eq_haarProb (Lp.coeFn_add F H)
  map_smul' c F := eq_of_ae_eq_haarProb (Lp.coeFn_smul c F)
  invFun F := MemLp.toLp F MemLp.of_discrete
  left_inv F := Lp.toLp_coeFn F _
  right_inv _ := eq_of_ae_eq_haarProb (MemLp.coeFn_toLp _)

@[simp]
theorem haarProbLpEquivFun_apply (F : Lp 𝕜 2 (haarProb G)) : haarProbLpEquivFun G 𝕜 F = ⇑F :=
  rfl

@[simp]
theorem haarProbLpEquivFun_symm_apply (F : G → 𝕜) :
    ⇑((haarProbLpEquivFun G 𝕜).symm F) = F :=
  (haarProbLpEquivFun G 𝕜).apply_symm_apply F

/-- On a finite group the almost-everywhere class of a continuous function is represented by that
function at every point, not merely almost everywhere. Together with
`ContinuousMap.coe_toLp` this evaluates the `L²` class `ContinuousMap.toLp 2 (haarProb G) 𝕜 F`,
which is why it is stated for `ContinuousMap.toAEEqFun`: that is the simp normal form of the
underlying function. -/
@[simp]
theorem coeFn_toAEEqFun_haarProb (F : C(G, 𝕜)) :
    ⇑(F.toAEEqFun (haarProb G)) = F :=
  eq_of_ae_eq_haarProb (F.coeFn_toAEEqFun (haarProb G))

end Lp

section InnerProduct

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The `L²` inner product of a finite group is the normalized Hermitian pairing of functions on
the group.** Under `TauCeti.haarProbLpEquivFun`, which sends a class to its values, `L²(G)` is
`G → 𝕜` with this pairing. Mathlib's inner product is conjugate linear in its first argument, which
is where the conjugation sits. -/
theorem inner_eq_card_inv_mul_sum (F H : Lp 𝕜 2 (haarProb G)) :
    ⟪F, H⟫_𝕜 = (Nat.card G : 𝕜)⁻¹ * ∑ g, H g * (starRingEnd 𝕜) (F g) := by
  rw [L2.inner_def]
  simp_rw [RCLike.inner_apply]
  rw [integral_haarProb_eq_card_inv_smul_sum, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

/-- The `L²` inner product of two continuous functions on a finite group is the normalized sum of
their pointwise products. -/
theorem inner_toLp_eq_card_inv_mul_sum (F H : C(G, 𝕜)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ * ∑ g, H g * (starRingEnd 𝕜) (F g) := by
  rw [inner_eq_card_inv_mul_sum]
  simp only [ContinuousMap.coe_toLp, coeFn_toAEEqFun_haarProb]

end InnerProduct

namespace ContRepresentation

section MatrixCoefficient

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype G] [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 W] in
/-- **The `L²` inner product of two matrix coefficients of a finite group is a sum over the
group.** -/
theorem inner_matrixCoeffLp_eq_card_inv_mul_sum (ρ : ContRepresentation 𝕜 G W)
    (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ *
        ∑ g, matrixCoeff ρ hρ v' w' g * (starRingEnd 𝕜) (matrixCoeff π hπ v w g) := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, inner_toLp_eq_card_inv_mul_sum]

/-- **The first Schur orthogonality relation for a finite group.** Averaging a matrix coefficient
of a unitary irreducible representation against the conjugate of another over `G` gives `d⁻¹` times
the product of the corresponding inner products, `d` the dimension.

This is the classical relation obtained from the compact-group
`TauCeti.ContRepresentation.schur_orthogonality_self` rather than from the finite-group averaging
idempotent. -/
theorem card_inv_mul_sum_matrixCoeff_mul_star_matrixCoeff [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) (v₁ w₁ v₂ w₂ : V) :
    (Nat.card G : 𝕜)⁻¹ *
        ∑ g, matrixCoeff π hπ v₂ w₂ g * (starRingEnd 𝕜) (matrixCoeff π hπ v₁ w₁ g)
      = (Module.finrank 𝕜 V : 𝕜)⁻¹ * ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [← inner_matrixCoeffLp_eq_card_inv_mul_sum π hπ π hπ]
  exact schur_orthogonality_self π hπ hunitary hirr v₁ w₁ v₂ w₂

end MatrixCoefficient

section Character

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype G] [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The `L²` inner product of two characters of a finite group is the classical character
pairing.** Unitarity of `π` turns the conjugation supplied by the inner product into the inversion
`g ↦ g⁻¹` of Mathlib's `Representation.char_orthonormal`; combining this with
`TauCeti.ContRepresentation.character_orthonormal_self` and
`TauCeti.ContRepresentation.character_orthonormal_distinct` is what specializes the compact-group
orthogonality relations to the classical ones. -/
theorem inner_characterLp_eq_card_inv_mul_sum (hunitary : IsUnitary π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜
      = (Nat.card G : 𝕜)⁻¹ * ∑ g, character ρ hρ g * character π hπ g⁻¹ := by
  rw [characterLp_def, characterLp_def, inner_toLp_eq_card_inv_mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ by
    rw [character_apply_inv π hπ hunitary g])

end Character

end ContRepresentation

end TauCeti
