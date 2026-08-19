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

the compact form of the finite-group identity `dim V^G = |G|⁻¹ ∑ χ_π g`. It is the multiplicity tool
that turns character integrals into dimensions: applied to the symmetric and exterior squares it
computes the Frobenius-Schur indicator, and applied to `Hom(V, W)` it computes the multiplicity of
one irreducible in another representation.

## Main definitions

* `ContRepresentation.haarAverageMap`: the Haar average `∫ g, π g` of the action operators.
* `ContRepresentation.haarAverageIntertwiner`: that average as a continuous
  self-intertwiner.

## Main results

* `ContRepresentation.isProj_haarAverageMap`: the Haar average is a projection onto the
  invariant subspace, with `ContRepresentation.range_haarAverageMap` identifying its range
  and `ContRepresentation.haarAverageMap_comp_self` its idempotence.
* `ContRepresentation.trace_haarAverageMap`: its trace is `∫ g, χ_π g`.
* `ContRepresentation.finrank_invariants`: **the dimension of the invariants is the Haar
  integral of the character.**
* `ContRepresentation.integral_character_eq_zero_iff`: that integral vanishes exactly when
  there is no nonzero invariant vector.

## Implementation notes

`haarAverageMap` is defined as `integratedOperator π hπ 1` rather than as a fresh Haar average, so
that the trace computation is the one already proved for the integrated operator and no second
Bochner-integral bookkeeping is needed. Its two invariance lemmas are proved vectorwise from
`MeasureTheory.integral_mul_left_eq_self` and `MeasureTheory.integral_mul_right_eq_self`, not from
the class-function machinery of `TauCeti/RepresentationTheory/Compact/Integrated.lean`: the constant
function `1` is a class function, but that route yields only conjugation invariance, which is
strictly weaker than the one-sided invariance used here.

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
the Haar average below, and the only thing the proofs need from it is its integrability. -/
private noncomputable def orbitMap (v : V) : C(G, V) :=
  ⟨fun g ↦ π g v, (ContinuousLinearMap.apply 𝕜 V v).continuous.comp hπ⟩

omit [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
private theorem integrable_orbitMap (v : V) :
    Integrable (fun g : G ↦ π g v) (haarProb G) :=
  integrable_continuousMap G (orbitMap π hπ v)

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

/-! ### The two invariances

Left invariance of Haar measure makes the average absorb the action on the left, right invariance
— unimodularity, which a compact group has — makes it absorb the action on the right. -/

/-- **The Haar average absorbs the action on the left**: `π h ∘ P = P`. This is left invariance of
normalized Haar measure. -/
theorem comp_haarAverageMap (h : G) :
    (π h).comp (haarAverageMap π hπ) = haarAverageMap π hπ := by
  ext v
  calc π h (haarAverageMap π hπ v)
      = ∫ g, π h (π g v) ∂haarProb G := by
        rw [haarAverageMap_apply, ← (π h).integral_comp_comm (integrable_orbitMap π hπ v)]
    _ = ∫ g, π (h * g) v ∂haarProb G := by
        simp only [map_mul, mul_apply_eq_comp]
    _ = ∫ g, π g v ∂haarProb G := integral_mul_left_eq_self (fun g : G ↦ π g v) h
    _ = haarAverageMap π hπ v := (haarAverageMap_apply π hπ v).symm

/-- **The Haar average absorbs the action on the right**: `P ∘ π h = P`. This is right invariance of
normalized Haar measure, which holds because a compact group is unimodular. -/
theorem haarAverageMap_comp (h : G) :
    (haarAverageMap π hπ).comp (π h) = haarAverageMap π hπ := by
  ext v
  calc haarAverageMap π hπ (π h v)
      = ∫ g, π (g * h) v ∂haarProb G := by
        rw [haarAverageMap_apply]
        simp only [map_mul, mul_apply_eq_comp]
    _ = ∫ g, π g v ∂haarProb G := integral_mul_right_eq_self (fun g : G ↦ π g v) h
    _ = haarAverageMap π hπ v := (haarAverageMap_apply π hπ v).symm

/-- The Haar average of the action operators, as a continuous self-intertwiner. -/
noncomputable def haarAverageIntertwiner : ContIntertwiningMap π π where
  __ := haarAverageMap π hπ
  isIntertwining' h := by
    rw [haarAverageMap_comp π hπ h, comp_haarAverageMap π hπ h]

@[simp]
theorem toContinuousLinearMap_haarAverageIntertwiner :
    (haarAverageIntertwiner π hπ).toContinuousLinearMap = haarAverageMap π hπ :=
  (rfl)

/-! ### The projection onto the invariants -/

/-- The Haar average lands in the invariant subspace. -/
theorem haarAverageMap_mem_invariants (v : V) : haarAverageMap π hπ v ∈ π.invariants :=
  fun h ↦ DFunLike.congr_fun (comp_haarAverageMap π hπ h) v

/-- The Haar average is the identity on the invariant subspace: the integrand is then constant, and
normalized Haar measure has total mass one. -/
theorem haarAverageMap_apply_of_mem_invariants {v : V} (hv : v ∈ π.invariants) :
    haarAverageMap π hπ v = v := by
  have hconst : ∀ g : G, π g v = v := hv
  rw [haarAverageMap_apply]
  simp [hconst]

/-- **Haar averaging is a projection onto the invariants.** -/
theorem isProj_haarAverageMap :
    LinearMap.IsProj π.invariants (haarAverageMap π hπ : V →ₗ[𝕜] V) where
  map_mem := haarAverageMap_mem_invariants π hπ
  map_id _ hv := haarAverageMap_apply_of_mem_invariants π hπ hv

/-- The Haar average is idempotent. -/
theorem haarAverageMap_comp_self :
    (haarAverageMap π hπ).comp (haarAverageMap π hπ) = haarAverageMap π hπ := by
  ext v
  exact haarAverageMap_apply_of_mem_invariants π hπ (haarAverageMap_mem_invariants π hπ v)

/-- The range of the Haar average is exactly the invariant subspace. -/
theorem range_haarAverageMap :
    LinearMap.range (haarAverageMap π hπ : V →ₗ[𝕜] V) = π.invariants := by
  refine le_antisymm (LinearMap.range_le_iff_comap.2 (Submodule.eq_top_iff'.2 fun v ↦ ?_)) ?_
  · exact haarAverageMap_mem_invariants π hπ v
  · exact fun v hv ↦ ⟨v, haarAverageMap_apply_of_mem_invariants π hπ hv⟩

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

/-- **The dimension of the invariants is the Haar integral of the character**,
`dim V^G = ∫ g, χ_π g ∂(haarProb G)`.

Both sides are the trace of the Haar average `∫ g, π g`: on the left because that average is a
projection onto the invariants, on the right because the trace of an integrated operator is the
integral of the traces. This is the compact-group form of the finite-group count
`dim V^G = |G|⁻¹ ∑ g, χ_π g`, and the tool that turns character integrals into dimensions. -/
theorem finrank_invariants :
    (Module.finrank 𝕜 π.invariants : 𝕜) = ∫ g, character π hπ g ∂haarProb G := by
  rw [← trace_haarAverageMap π hπ, (isProj_haarAverageMap π hπ).trace]

/-- **The character integral vanishes exactly when there is no nonzero invariant vector.** -/
theorem integral_character_eq_zero_iff :
    ∫ g, character π hπ g ∂haarProb G = 0 ↔ π.invariants = ⊥ := by
  rw [← finrank_invariants π hπ, Nat.cast_eq_zero, Submodule.finrank_eq_zero]

end Trace

end ContRepresentation
