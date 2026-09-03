/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Integrated

/-!
# Haar averaging projects onto the invariants, and the character integral counts them

For a finite group `G` whose order is invertible in the scalars, Mathlib averages the action
operators of a representation over the group and gets a projection onto the invariant subspace
(`Representation.averageMap`, `Representation.isProj_averageMap`). This file is the compact-group
form of that construction: the finite average is replaced by the Haar integral

`haarAverageMap π hπ = ∫ g, π g ∂(haarProb G)`,

the integrated operator of the constant function `1`, and normalized Haar measure plays the role of
the factor `1/|G|` — it is what makes the average of a constant that constant, so that the operator
restricts to the identity on the invariants.

The two invariance properties of the average are the two translation invariances of Haar measure:
left invariance gives `π h ∘ P = P`, and right invariance — unimodularity, automatic on a compact
group — gives `P ∘ π h = P`. Together they make `P` a self-intertwiner whose image is exactly the
invariant subspace `ContRepresentation.invariants`, and `P` is idempotent because it fixes that
image pointwise.

In finite dimension the trace of a projection is the dimension of its image, and the trace of the
integrated operator is the Haar integral of the character
(`TauCeti.ContRepresentation.trace_integratedOperator`). The two readings of the same trace give the
counting theorem

`dim V^G = ∫ g, χ_π g ∂(haarProb G)`,

the compact form of the finite-group identity `dim V^G = |G|⁻¹ ∑ χ_π g`. It is the tool that turns
character integrals into dimensions: applied to the symmetric and exterior squares it computes the
Frobenius-Schur indicator, and applied to `Hom(V, W)` it computes the dimension of the space of
intertwiners `V → W` (which for complex scalars and irreducible `V` is the multiplicity of `V` in
`W`, but over `ℝ` counts each copy with the dimension of its endomorphism division algebra).

## Main definitions

* `ContRepresentation.haarAverageMap`: the Haar average `∫ g, π g` of the action operators.

## Main results

* `ContRepresentation.isProj_haarAverageMap`: the Haar average is a projection onto the
  invariant subspace, with `ContRepresentation.range_haarAverageMap` identifying its range
  and `ContRepresentation.haarAverageMap_comp_self` its idempotence.
* `ContRepresentation.trace_haarAverageMap`: its trace is `∫ g, χ_π g`.
* `ContRepresentation.integral_character_eq_finrank_invariants`: **the Haar integral of the
  character is the dimension of the invariants.**
* `ContRepresentation.integral_character_eq_zero_iff`: that integral vanishes exactly when
  there is no nonzero invariant vector.

## Implementation notes

`haarAverageMap` is defined as `integratedOperator π hπ 1` rather than as a fresh Haar average, so
that the trace computation is the one already proved for the integrated operator and no second
Bochner-integral bookkeeping is needed. Its two invariance lemmas are proved vectorwise from
`TauCeti.haarAverage_comp_mulLeft` and `TauCeti.haarAverage_comp_mulRight`, applied to the orbit
map `g ↦ π g v`, and not from the class-function machinery of
`TauCeti/RepresentationTheory/Compact/Integrated.lean`: the constant function `1` is a class
function, but that route yields only conjugation invariance, which is strictly weaker than the
one-sided invariance used here.

The invariant subspace is Mathlib's `ContRepresentation.invariants`, not a new definition, and the
projection is packaged through Mathlib's `LinearMap.IsProj` so that `LinearMap.IsProj.trace`
applies verbatim.

The declarations here live in the root `ContRepresentation` namespace, so that `π.haarAverageMap hπ`
elaborates, rather than in `TauCeti.ContRepresentation` alongside the integrated operator they are
built from; the older namespace is opened to reach that operator and the character.

## References

This is the projection promised, and left unbuilt, by
`TauCeti/RepresentationTheory/Compact/Character/Projection.lean`, specialized to the trivial
isotypic component. It supplies the multiplicity counting that Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
needs for the Frobenius-Schur indicator `∫ g, χ_π (g * g)`, whose trichotomy reads that integral as
the difference of the dimensions of the invariants of the symmetric and exterior squares. The
mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and
T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
Chapter II.
-/

public section

open MeasureTheory TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Projection

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- The orbit map `g ↦ π g v` of a vector, as a continuous map on the group. It is the integrand of
the Haar average below, in the bundled form that `TauCeti.haarAverage` and its translation
invariance lemmas take. -/
private noncomputable def orbitMap (v : V) : C(G, V) :=
  ⟨fun g ↦ π g v, (ContinuousLinearMap.apply 𝕜 V v).continuous.comp hπ⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- The orbit map, unfolded. -/
@[simp]
private theorem orbitMap_apply (v : V) (g : G) : orbitMap π hπ v g = π g v :=
  (rfl)

/-- **The Haar average of the action operators** `∫ g, π g ∂(haarProb G)`, the integrated operator
of the constant function `1`.

This is the compact-group form of Mathlib's `Representation.averageMap`: normalized Haar measure
replaces the factor `1/|G|`, and the results below show that it is again a projection onto the
invariant subspace. -/
noncomputable def haarAverageMap : V →L[𝕜] V :=
  integratedOperator π hπ 1

/-- The Haar average of the action operators, evaluated at a vector. -/
theorem haarAverageMap_apply (v : V) :
    haarAverageMap π hπ v = ∫ g, π g v ∂haarProb G := by
  rw [haarAverageMap, integratedOperator_apply]
  simp

/-- The Haar average, evaluated at a vector, is `TauCeti.haarAverage` of that vector's orbit map.
This is the form in which the translation invariance of Haar averaging applies below. -/
private theorem haarAverageMap_apply_eq_haarAverage (v : V) :
    haarAverageMap π hπ v = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := by
  rw [haarAverageMap_apply, haarAverage_apply]
  simp

/-! ### The two invariances

Left invariance of Haar measure makes the average absorb the action on the left, right invariance
— unimodularity, which a compact group has — makes it absorb the action on the right. Both are read
off `TauCeti.haarAverage_comp_mulLeft` and `TauCeti.haarAverage_comp_mulRight`, once the two
translates of the orbit map are identified. -/

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- Precomposing the orbit map with left translation is postcomposing it with the action:
`g ↦ π (h * g) v` is `g ↦ π h (π g v)`. -/
private theorem orbitMap_comp_mulLeft (h : G) (v : V) :
    (orbitMap π hπ v).comp (ContinuousMap.mulLeft h)
      = (π h : C(V, V)).comp (orbitMap π hπ v) := by
  ext g
  simp [map_mul, mul_apply_eq_comp]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- Precomposing the orbit map with right translation is the orbit map of the translated vector:
`g ↦ π (g * h) v` is `g ↦ π g (π h v)`. -/
private theorem orbitMap_comp_mulRight (h : G) (v : V) :
    (orbitMap π hπ v).comp (ContinuousMap.mulRight h) = orbitMap π hπ (π h v) := by
  ext g
  simp [map_mul, mul_apply_eq_comp]

/-- **The Haar average absorbs the action on the left**: `π h ∘ P = P`. This is left invariance of
normalized Haar measure. -/
@[simp]
theorem comp_haarAverageMap (h : G) :
    (π h).comp (haarAverageMap π hπ) = haarAverageMap π hπ := by
  ext v
  calc π h (haarAverageMap π hπ v)
      = haarAverage G (𝕜 := 𝕜) ((π h : C(V, V)).comp (orbitMap π hπ v)) := by
        rw [haarAverageMap_apply_eq_haarAverage, ContinuousLinearMap.haarAverage_comp_comm]
    _ = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := by
        rw [← orbitMap_comp_mulLeft, haarAverage_comp_mulLeft]
    _ = haarAverageMap π hπ v := (haarAverageMap_apply_eq_haarAverage π hπ v).symm

/-- The Haar average absorbs the action on the left, applied to a vector: `π h (P v) = P v`. -/
@[simp]
theorem comp_haarAverageMap_apply (h : G) (v : V) :
    π h (haarAverageMap π hπ v) = haarAverageMap π hπ v :=
  DFunLike.congr_fun (comp_haarAverageMap π hπ h) v

/-- **The Haar average absorbs the action on the right**: `P ∘ π h = P`. This is right invariance of
normalized Haar measure, which holds because a compact group is unimodular. -/
@[simp]
theorem haarAverageMap_comp (h : G) :
    (haarAverageMap π hπ).comp (π h) = haarAverageMap π hπ := by
  ext v
  calc haarAverageMap π hπ (π h v)
      = haarAverage G (𝕜 := 𝕜) ((orbitMap π hπ v).comp (ContinuousMap.mulRight h)) := by
        rw [orbitMap_comp_mulRight, haarAverageMap_apply_eq_haarAverage]
    _ = haarAverage G (𝕜 := 𝕜) (orbitMap π hπ v) := haarAverage_comp_mulRight G _ _
    _ = haarAverageMap π hπ v := (haarAverageMap_apply_eq_haarAverage π hπ v).symm

/-- The Haar average absorbs the action on the right, applied to a vector: `P (π h v) = P v`. -/
@[simp]
theorem haarAverageMap_comp_apply (h : G) (v : V) :
    haarAverageMap π hπ (π h v) = haarAverageMap π hπ v :=
  DFunLike.congr_fun (haarAverageMap_comp π hπ h) v

/-! ### The projection onto the invariants -/

/-- The Haar average lands in the invariant subspace. This is not itself a `simp` lemma — its
statement is not in simp normal form, since `ContRepresentation.mem_invariants` unfolds the
membership — but `simp` proves it from `ContRepresentation.comp_haarAverageMap_apply`. -/
theorem haarAverageMap_invariant (v : V) : haarAverageMap π hπ v ∈ π.invariants :=
  fun h ↦ comp_haarAverageMap_apply π hπ h v

/-- The Haar average is the identity on the invariant subspace: the integrand is then constant, and
normalized Haar measure has total mass one. -/
@[simp]
theorem haarAverageMap_id {v : V} (hv : v ∈ π.invariants) :
    haarAverageMap π hπ v = v := by
  have hconst : ∀ g : G, π g v = v := hv
  rw [haarAverageMap_apply]
  simp [hconst]

/-- **Haar averaging is a projection onto the invariants.** -/
theorem isProj_haarAverageMap :
    LinearMap.IsProj π.invariants (haarAverageMap π hπ : V →ₗ[𝕜] V) where
  map_mem := haarAverageMap_invariant π hπ
  map_id _ hv := haarAverageMap_id π hπ hv

/-- The Haar average is idempotent. -/
@[simp]
theorem haarAverageMap_comp_self :
    (haarAverageMap π hπ).comp (haarAverageMap π hπ) = haarAverageMap π hπ :=
  ContinuousLinearMap.coe_injective (isProj_haarAverageMap π hπ).isIdempotentElem

/-- The range of the Haar average is exactly the invariant subspace. -/
@[simp]
theorem range_haarAverageMap :
    LinearMap.range (haarAverageMap π hπ : V →ₗ[𝕜] V) = π.invariants :=
  (isProj_haarAverageMap π hπ).range

end Projection

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis on the results below: a finite-dimensional
normed space over an `RCLike` field is already complete. Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance instead, exactly as in
`TauCeti/RepresentationTheory/Compact/Integrated.lean`. -/
local instance instCompleteSpaceInvariants : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- The trace of the Haar average of the action operators is the Haar integral of the character. -/
theorem trace_haarAverageMap :
    LinearMap.trace 𝕜 V (haarAverageMap π hπ : V →ₗ[𝕜] V)
      = ∫ g, character π hπ g ∂haarProb G := by
  rw [haarAverageMap, trace_integratedOperator]
  simp

/-- **The Haar integral of the character is the dimension of the invariants**,
`∫ g, χ_π g ∂(haarProb G) = dim V^G`.

Both sides are the trace of the Haar average `∫ g, π g`: on the left because the trace of an
integrated operator is the integral of the traces, on the right because that average is a
projection onto the invariants. This is the compact-group form of the finite-group count
`dim V^G = |G|⁻¹ ∑ g, χ_π g`, and the tool that turns character integrals into dimensions. -/
theorem integral_character_eq_finrank_invariants :
    ∫ g, character π hπ g ∂haarProb G = (Module.finrank 𝕜 π.invariants : 𝕜) := by
  rw [← trace_haarAverageMap π hπ, (isProj_haarAverageMap π hπ).trace]

/-- **The character integral vanishes exactly when there is no nonzero invariant vector.** -/
theorem integral_character_eq_zero_iff :
    ∫ g, character π hπ g ∂haarProb G = 0 ↔ π.invariants = ⊥ := by
  rw [integral_character_eq_finrank_invariants π hπ, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]

end Trace

end ContRepresentation
