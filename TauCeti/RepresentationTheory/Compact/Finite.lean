/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Intertwiner.Dimension
public import TauCeti.RepresentationTheory.Compact.Invariants
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite groups: normalized Haar, the `L²` pairing, and orthogonality

A finite group carrying the discrete topology is a compact topological group, so the whole
compact-group development applies to it. This file identifies the objects it produces with the
elementary finite-group ones: normalized Haar measure is `|G|⁻¹ • Measure.count`, the Haar integral
is the group average `|G|⁻¹ ∑ g, F g`, and the Haar average of the action operators of a
representation is the finite group average `|G|⁻¹ ∑ g, π g`, the Reynolds operator. (Mathlib's
algebraic counterpart of that operator is `Representation.averageMap`; this file does not connect
to it, only to the explicit sum.)

Everything the compact theory phrases as an `L²(G)` inner product then becomes a finite Hermitian
sum. Normalized Haar measure has full support on a discrete space, so a class in `L²(G)` *is* a
function on `G` and the inner product is `|G|⁻¹ ∑ x, conj (f x) · g x`. Rewriting the compact
statements along that identity turns the two Schur orthogonality relations and the two character
orthogonality relations into their classical finite-group forms, and turns the intertwiner count
`⟪χ_π, χ_ρ⟫ = dim Hom_G(V, W)` into `|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)`, which is the
shape Mathlib proves algebraically as `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`.
Each such specialization carries the name of the compact statement it specializes, with the suffix
`_sum` recording that the Haar integral has become a group average.

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
* `TauCeti.eq_of_ae_eq_haarProb`: **normalized Haar measure on a finite discrete group has full
  support**, so two functions agreeing almost everywhere agree everywhere. This is what makes an
  `L²` class on a finite group a genuine function.
* `TauCeti.inner_Lp_eq_inv_mul_sum`: **the `L²(G)` inner product is the normalized Hermitian
  pairing** `|G|⁻¹ ∑ x, conj (f x) · g x`, with `TauCeti.inner_toLp_eq_inv_mul_sum` the form for
  two continuous functions.
* `ContRepresentation.schur_orthogonality_self_sum` and
  `ContRepresentation.schur_orthogonality_sum`: **the two Schur orthogonality relations as finite
  averages** of matrix coefficients.
* `ContRepresentation.character_orthonormal_self_sum` and
  `ContRepresentation.character_orthonormal_distinct_sum`: **the two character orthogonality
  relations as finite averages**.

The counting identity `|G|⁻¹ ∑ g, χ_π g = dim V^G` that the compact-group character integral
generalizes then costs one rewrite. It is not given a name: Mathlib already proves it, as
`Representation.card_inv_mul_sum_char_eq_finrank`, and that lemma closes the `ContRepresentation`
statement outright, so only the route through the compact theory is new. The intertwiner count
`|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)` is unnamed for the same reason: Mathlib proves it
as `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, for the algebraic intertwiner space
`Representation.IntertwiningMap`, which in finite dimensions is the continuous one because every
linear map out of a finite-dimensional normed space is continuous. Both routes are exhibited by
anonymous `example`s, as is the agreement of `character_orthonormal_self_sum` with the diagonal
half of Mathlib's `Representation.char_orthonormal`.

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
`FDRep.average_char_eq_finrank_invariants` for the purely algebraic theory. It is also the `L²`,
Schur and character-orthonormality part of that item: `⟪·, ·⟫_{L²(G)}` becomes the finite Hermitian
pairing, `schur_orthogonality_self` and `schur_orthogonality` become the classical orthogonality
relations for matrix coefficients, and `character_orthonormal_self` and
`character_orthonormal_distinct` become Mathlib's `Representation.char_orthonormal`, exhibited by
the second anonymous `example` closing the file. The two specializations the roadmap item asks for
that are still missing are Maschke (the finite shadow of complete reducibility) and Peter-Weyl
(that `peterWeylBasis` is the matrix-coefficient basis of `k[G]`); neither is proved here.
-/

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

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

/-! ### The `L²` space of a finite group -/

section FullSupport

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Normalized Haar measure on a finite discrete group has full support**, so functions agreeing
almost everywhere agree everywhere.

Haar measure is positive on nonempty open sets, and on a discrete space every function is
continuous, so `Continuous.ae_eq_iff_eq` applies with no measurability side condition. In
particular an element of `Lp 𝕜 2 (haarProb G)`, which is only an almost-everywhere class, is
pinned down by its values: this is the sense in which `L²(G)` "is" `G → 𝕜`. -/
theorem eq_of_ae_eq_haarProb {α : Type*} [TopologicalSpace α] [T2Space α] {f g : G → α}
    (h : f =ᵐ[haarProb G] g) : f = g :=
  (continuous_of_discreteTopology.ae_eq_iff_eq (haarProb G) continuous_of_discreteTopology).mp h

end FullSupport

section InnerProduct

variable (G : Type*) [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] {𝕜 : Type*} [RCLike 𝕜]

/-- **The `L²` inner product of a finite discrete group is the normalized Hermitian pairing**
`|G|⁻¹ ∑ x, conj (f x) * g x`.

This is the identification `L²(G) = (G → 𝕜)` that the roadmap's finite-group acceptance criterion
asks for: the Haar integral defining the `L²` inner product is the group average, by
`TauCeti.integral_haarProb_eq_inv_mul_sum`. The conjugation sits on the *first* argument, matching
Mathlib's convention that the inner product is conjugate-linear there. -/
theorem inner_Lp_eq_inv_mul_sum (f g : Lp 𝕜 2 (haarProb G)) :
    ⟪f, g⟫_𝕜 = (Nat.card G : 𝕜)⁻¹ * ∑ x, (starRingEnd 𝕜) (f x) * g x := by
  rw [L2.inner_def,
    ← integral_haarProb_eq_inv_mul_sum (𝕜 := 𝕜) G fun x ↦ (starRingEnd 𝕜) (f x) * g x]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    simp only [RCLike.inner_apply, mul_comm])

/-- The `L²` inner product of two *continuous* functions on a finite discrete group, the form in
which the matrix coefficients and the characters present themselves. -/
theorem inner_toLp_eq_inv_mul_sum (f g : C(G, 𝕜)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 f, ContinuousMap.toLp 2 (haarProb G) 𝕜 g⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ x, (starRingEnd 𝕜) (f x) * g x := by
  rw [inner_Lp_eq_inv_mul_sum,
    eq_of_ae_eq_haarProb G (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G) f),
    eq_of_ae_eq_haarProb G (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G) g)]

end InnerProduct

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

/-! ### Matrix coefficients and the Schur orthogonality relations -/

section MatrixCoefficient

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The `L²` pairing of two matrix coefficients of a finite group is a group average.** This is
the identity along which the Schur orthogonality relations become finite sums. -/
theorem inner_matrixCoeffLp_eq_inv_mul_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 * ⟪ρ g v', w'⟫_𝕜 := by
  rw [matrixCoeffLp_def, matrixCoeffLp_def, inner_toLp_eq_inv_mul_sum]
  simp only [matrixCoeff_apply]

end MatrixCoefficient

section SchurSelf

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **The first Schur orthogonality relation for a finite group.** For a unitary irreducible
representation of dimension `d`,
`|G|⁻¹ ∑ g, conj ⟪π g v₁, w₁⟫ * ⟪π g v₂, w₂⟫ = d⁻¹ * (conj ⟪v₁, v₂⟫ * ⟪w₁, w₂⟫)`.

This is `TauCeti.ContRepresentation.schur_orthogonality_self` with the Haar integral of the
compact theory replaced by the group average; the normalization `|G|⁻¹` is exactly the one that
makes normalized Haar measure a probability measure. -/
theorem schur_orthogonality_self_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation)
    (v₁ w₁ v₂ w₂ : V) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v₁, w₁⟫_𝕜 * ⟪π g v₂, w₂⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ * ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π hπ π hπ,
    schur_orthogonality_self π hπ hunitary hirr]

end SchurSelf

section SchurDistinct

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceSchurDistinct : CompleteSpace W :=
  FiniteDimensional.complete 𝕜 W

/-- **The second Schur orthogonality relation for a finite group.** Matrix coefficients of
inequivalent irreducible representations have vanishing group average, this being
`TauCeti.ContRepresentation.schur_orthogonality` read through the finite Hermitian pairing. -/
theorem schur_orthogonality_sum (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (hunitary : IsUnitary ρ)
    (hirrπ : Representation.IsIrreducible π.toRepresentation)
    (hirrρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (v w : V) (v' w' : W) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) ⟪π g v, w⟫_𝕜 * ⟪ρ g v', w'⟫_𝕜 = 0 := by
  rw [← inner_matrixCoeffLp_eq_inv_mul_sum π hπ ρ hρ,
    schur_orthogonality π hπ ρ hρ hunitary hirrπ hirrρ hne]

end SchurDistinct

/-! ### Characters -/

section Character

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ hρ

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **The `L²` pairing of two characters of a finite group is a group average.** -/
theorem inner_characterLp_eq_inv_mul_sum :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 =
      (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) (character π hπ g) * character ρ hρ g := by
  rw [characterLp_def, characterLp_def, inner_toLp_eq_inv_mul_sum]

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/- **The finite character sum counts the intertwiners**:
`|G|⁻¹ ∑ g, χ_π(g⁻¹) · χ_ρ(g) = dim Hom_G(V, W)`, the specialization of
`ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap` to a finite discrete
group. No unitarity is needed: the inverse in the first factor is what the compact statement
carries, and only for a unitary representation does it become a complex conjugate.

No name is claimed, for the same reason as in the counting identity above: Mathlib proves this
identity as `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, stated for the algebraic
intertwiner space `Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation`, which in
finite dimensions is the continuous one. What the compact theory contributes is the derivation
below, in which the count is the Haar integral read off by
`TauCeti.integral_haarProb_eq_inv_mul_sum`. -/
example :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g⁻¹ * character ρ hρ g
      = (Module.finrank 𝕜 (ContIntertwiningMap π ρ) : 𝕜) := by
  rw [← integral_character_mul_eq_finrank_contIntertwiningMap π ρ hπ hρ,
    integral_haarProb_eq_inv_mul_sum]

end Character

section CharacterOrthogonality

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- **First character orthogonality for a finite group**:
`|G|⁻¹ ∑ g, conj (χ_π g) · χ_π g = 1` for an irreducible unitary representation. -/
theorem character_orthonormal_self_sum [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) (character π hπ g) * character π hπ g = 1 := by
  rw [← inner_characterLp_eq_inv_mul_sum π hπ π hπ,
    character_orthonormal_self π hπ hunitary hirr]

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- **Second character orthogonality for a finite group**: the group average of `conj χ_π · χ_ρ`
vanishes when no nonzero continuous intertwiner `ρ → π` exists, which for a pair of irreducibles is
Schur's lemma. -/
theorem character_orthonormal_distinct_sum (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)
    (hunitary : IsUnitary π)
    (hdistinct : ∀ f : ContIntertwiningMap ρ π, f.toContinuousLinearMap = 0) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, (starRingEnd 𝕜) (character π hπ g) * character ρ hρ g = 0 := by
  rw [← inner_characterLp_eq_inv_mul_sum π hπ ρ hρ,
    character_orthonormal_distinct π hπ ρ hρ hunitary hdistinct]

/- **The diagonal half of Mathlib's `Representation.char_orthonormal`**, in its `χ_π(g) · χ_π(g⁻¹)`
spelling, obtained through the compact theory: unitarity turns the inverse into a conjugate by
`ContRepresentation.character_apply_inv`, and `character_orthonormal_self_sum` is then the
statement. No name is claimed, since Mathlib's lemma is the general form; what is exhibited is that
the compact-group normalization agrees with the finite-group one. -/
example [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Nat.card G : 𝕜)⁻¹ * ∑ g, character π hπ g * character π hπ g⁻¹ = 1 := by
  rw [← character_orthonormal_self_sum π hπ hunitary hirr]
  exact congrArg _ (Finset.sum_congr rfl fun g _ ↦ by
    rw [character_apply_inv π hπ hunitary, mul_comm])

end CharacterOrthogonality

end ContRepresentation
