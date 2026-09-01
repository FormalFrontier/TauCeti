/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import TauCeti.Algebra.Lie.Weights.Diagonalizable
public import TauCeti.Algebra.Lie.Weights.Killing

public section

/-!
# The projections attached to the weight-space decomposition

A finite-dimensional triangularizable module `M` over a nilpotent Lie algebra `L` is the internal
direct sum of its generalized weight spaces (`TauCeti.isInternal_genWeightSpace`). This file names
the associated family of projections `TauCeti.genWeightSpaceProjection`, one for each weight, and
records the three facts that characterise it: each projection lands in its weight space, it is the
identity there and kills the other weight spaces, and the whole family sums to the identity.

The last section specialises to the root-space decomposition of a Lie algebra `L` with
non-degenerate Killing form over its Cartan subalgebra `H`, where the projections acquire two
further properties that the decomposition alone does not give. Root spaces are Killing-orthogonal
unless the two weights are opposite, so the Killing-adjoint of the projection onto the `χ`-root
space is the projection onto the `-χ` one; and each projection has trace the dimension of its root
space, which for a root is `1`.

## Main definitions

* `TauCeti.genWeightSpaceProjection`: the projection of `M` onto the generalized weight space of a
  weight, along the sum of the other weight spaces.

## Main results

* `TauCeti.sum_genWeightSpaceProjection_apply`: the projections sum to the identity.
* `TauCeti.killingForm_genWeightSpaceProjection`: `κ (π_χ x) y = κ x (π_{-χ} y)`, so `π_χ` and
  `π_{-χ}` are Killing-adjoint; `TauCeti.isAdjointPair_genWeightSpaceProjection` says the same in
  the `LinearMap.IsAdjointPair` form.
* `TauCeti.trace_genWeightSpaceProjection`: the trace of a projection is the dimension of the
  weight space it projects onto.

## Implementation notes

The projection is built from `DirectSum.coeLinearMap`, whose bijectivity is exactly
`DirectSum.IsInternal`, rather than from a choice of complement: that way
`DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem` computes it on each summand directly, and
the trace computation can go through `LinearMap.trace_eq_sum_trace_restrict`.

`DirectSum` needs a `DecidableEq (Weight K L M)`. The projection is noncomputable in any case, so
that choice is made classically inside the definition instead of being carried as a hypothesis:
the API is stated without any decidability assumption.

## References

The projections are the working form of the "generalized weight-space decomposition" item of Layer
2 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`; the Killing-adjointness and
the trace are what the Casimir eigenvalue computation of Layer 5 consumes.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.1 (the
  root-space decomposition) and §8.2 (the Killing form pairs `Lα` with `L_{-α}` alone).
-/

namespace TauCeti

open Finset LieAlgebra LieModule Module

universe u v w

/-! ### The projections of the weight-space decomposition -/

section Triangularizable

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] [LieModule.IsTriangularizable K L M]

open scoped Classical in
/-- **The projection onto a generalized weight space** along the sum of the other weight spaces,
for a finite-dimensional triangularizable module. -/
noncomputable def genWeightSpaceProjection (χ : Weight K L M) : M →ₗ[K] M :=
  (genWeightSpace M (χ : L → K)).toSubmodule.subtype ∘ₗ
    DirectSum.component K (Weight K L M)
      (fun ψ : Weight K L M ↦ (genWeightSpace M (ψ : L → K)).toSubmodule) χ ∘ₗ
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun ψ : Weight K L M ↦ (genWeightSpace M (ψ : L → K)).toSubmodule)
      (isInternal_genWeightSpace K L M)).symm.toLinearMap

variable {K L M}

/-- A projection lands in the weight space it is attached to. -/
theorem genWeightSpaceProjection_apply_mem (χ : Weight K L M) (m : M) :
    genWeightSpaceProjection K L M χ m ∈ genWeightSpace M (χ : L → K) :=
  Submodule.coe_mem _

/-- A projection is the identity on its own weight space. -/
@[simp]
theorem genWeightSpaceProjection_apply_of_mem {χ : Weight K L M} {m : M}
    (hm : m ∈ genWeightSpace M (χ : L → K)) : genWeightSpaceProjection K L M χ m = m := by
  classical
  have := DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem
    (isInternal_genWeightSpace K L M) (i := χ) (x := m) hm
  simpa [genWeightSpaceProjection, ← DirectSum.apply_eq_component] using congrArg Subtype.val this

/-- A projection kills every other weight space.

Not `@[simp]`: the weight `ψ` occurs only in the hypotheses, so `simp` could not instantiate it.
The `simp`-usable consequence is `TauCeti.genWeightSpaceProjection_apply_apply_of_ne`. -/
theorem genWeightSpaceProjection_apply_of_mem_of_ne {χ ψ : Weight K L M} (h : ψ ≠ χ) {m : M}
    (hm : m ∈ genWeightSpace M (ψ : L → K)) : genWeightSpaceProjection K L M χ m = 0 := by
  classical
  have := DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne
    (isInternal_genWeightSpace K L M) h hm
  simpa [genWeightSpaceProjection, ← DirectSum.apply_eq_component] using congrArg Subtype.val this

/-- The projections are idempotent. -/
@[simp]
theorem genWeightSpaceProjection_apply_apply (χ : Weight K L M) (m : M) :
    genWeightSpaceProjection K L M χ (genWeightSpaceProjection K L M χ m) =
      genWeightSpaceProjection K L M χ m :=
  genWeightSpaceProjection_apply_of_mem (genWeightSpaceProjection_apply_mem χ m)

/-- Projections attached to distinct weights annihilate one another. -/
@[simp]
theorem genWeightSpaceProjection_apply_apply_of_ne {χ ψ : Weight K L M} (h : ψ ≠ χ) (m : M) :
    genWeightSpaceProjection K L M χ (genWeightSpaceProjection K L M ψ m) = 0 :=
  genWeightSpaceProjection_apply_of_mem_of_ne h (genWeightSpaceProjection_apply_mem ψ m)

/-- **The projections sum to the identity**: this is the weight-space decomposition, read on a
single vector. -/
theorem sum_genWeightSpaceProjection_apply (m : M) :
    ∑ χ : Weight K L M, genWeightSpaceProjection K L M χ m = m := by
  classical
  let A : Weight K L M → Submodule K M := fun ψ ↦ (genWeightSpace M (ψ : L → K)).toSubmodule
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) (isInternal_genWeightSpace K L M)
  have hproj : ∀ χ : Weight K L M,
      genWeightSpaceProjection K L M χ m = ((e.symm m χ : A χ) : M) := fun _ ↦ rfl
  calc ∑ χ : Weight K L M, genWeightSpaceProjection K L M χ m
      = ∑ χ : Weight K L M, ((e.symm m χ : A χ) : M) := by simp_rw [hproj]
    _ = DirectSum.coeLinearMap A (e.symm m) := by
        conv_rhs => rw [← DirectSum.sum_univ_of (e.symm m)]
        rw [map_sum]
        exact Finset.sum_congr rfl fun χ _ ↦ (DirectSum.coeLinearMap_of A χ _).symm
    _ = m := e.apply_symm_apply m

/-- A projection maps each weight space into itself: its own weight space identically, the others
to zero. -/
theorem mapsTo_genWeightSpaceProjection (χ ψ : Weight K L M) :
    Set.MapsTo (genWeightSpaceProjection K L M χ) (genWeightSpace M (ψ : L → K))
      (genWeightSpace M (ψ : L → K)) := by
  intro m hm
  rcases eq_or_ne ψ χ with rfl | h
  · simpa [genWeightSpaceProjection_apply_of_mem hm] using hm
  · simp [genWeightSpaceProjection_apply_of_mem_of_ne h hm]

/-- **The trace of a projection is the dimension of the weight space it projects onto.** -/
theorem trace_genWeightSpaceProjection (χ : Weight K L M) :
    LinearMap.trace K M (genWeightSpaceProjection K L M χ) =
      finrank K (genWeightSpace M (χ : L → K)) := by
  classical
  have hmaps : ∀ ψ : Weight K L M, ∀ x ∈ (genWeightSpace M (ψ : L → K)).toSubmodule,
      genWeightSpaceProjection K L M χ x ∈ (genWeightSpace M (ψ : L → K)).toSubmodule :=
    fun ψ _ hx ↦ mapsTo_genWeightSpaceProjection χ ψ hx
  have hid : (genWeightSpaceProjection K L M χ).restrict (hmaps χ) = LinearMap.id := by
    refine LinearMap.ext fun m ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply]
    exact genWeightSpaceProjection_apply_of_mem m.2
  have hzero : ∀ ψ : Weight K L M, ψ ≠ χ →
      (genWeightSpaceProjection K L M χ).restrict (hmaps ψ) = 0 := by
    intro ψ h
    refine LinearMap.ext fun m ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    exact genWeightSpaceProjection_apply_of_mem_of_ne h m.2
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_genWeightSpace K L M) hmaps,
    Finset.sum_eq_single χ (fun ψ _ h ↦ by rw [hzero ψ h, map_zero]) (by simp), hid,
    LinearMap.trace_id]
  rfl

end Triangularizable

/-! ### The root-space projections of a Killing Lie algebra -/

section Killing

open LieAlgebra.IsKilling

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Two weights whose weight spaces are not Killing-orthogonal are opposite. -/
private theorem weight_add_ne_zero {χ ψ : Weight K H L} (h : χ ≠ -ψ) :
    (χ : H → K) + (ψ : H → K) ≠ 0 := fun hc ↦
  h <| Weight.ext fun u ↦ by
    have := congrFun hc u
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simpa using eq_neg_of_add_eq_zero_left this

/-- **The root-space projections are Killing-adjoint in opposite pairs.** Root spaces pair to zero
under the Killing form unless their weights are opposite, so pushing the projection onto the
`χ`-root space across the form turns it into the projection onto the `-χ`-root space. -/
theorem killingForm_genWeightSpaceProjection (χ : Weight K H L) (x y : L) :
    killingForm K L (genWeightSpaceProjection K H L χ x) y =
      killingForm K L x (genWeightSpaceProjection K H L (-χ) y) := by
  have key : ∀ z w : L, killingForm K L (genWeightSpaceProjection K H L χ z) w =
      killingForm K L (genWeightSpaceProjection K H L χ z)
        (genWeightSpaceProjection K H L (-χ) w) := by
    intro z w
    conv_lhs => rw [← sum_genWeightSpaceProjection_apply (K := K) (L := H) w]
    rw [map_sum, Finset.sum_eq_single (-χ) _ (by simp)]
    intro ψ _ h
    exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H
      (genWeightSpaceProjection_apply_mem χ z) (genWeightSpaceProjection_apply_mem ψ w)
      (weight_add_ne_zero H fun hc ↦ h (by rw [hc, neg_neg]))
  rw [key]
  conv_rhs => rw [← sum_genWeightSpaceProjection_apply (K := K) (L := H) x]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single χ _ (by simp)]
  intro ψ _ h
  exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H
    (genWeightSpaceProjection_apply_mem ψ x) (genWeightSpaceProjection_apply_mem (-χ) y)
    (weight_add_ne_zero H fun hc ↦ h (by rwa [neg_neg] at hc))

/-- **Opposite root-space projections are a Killing-adjoint pair.** This is the
`LinearMap.IsAdjointPair` form of `TauCeti.killingForm_genWeightSpaceProjection`, which is what
the Killing-dual-basis lemmas consume. -/
theorem isAdjointPair_genWeightSpaceProjection (χ : Weight K H L) :
    LinearMap.IsAdjointPair (killingForm K L) (killingForm K L)
      (genWeightSpaceProjection K H L (-χ)) (genWeightSpaceProjection K H L χ) := fun x y ↦ by
  rw [killingForm_genWeightSpaceProjection H (-χ) x y, neg_neg]

/-- **A root-space projection has trace one.** The root spaces at nonzero weights are lines
(`LieAlgebra.IsKilling.finrank_rootSpace_eq_one`). -/
theorem trace_genWeightSpaceProjection_eq_one [CharZero K] {χ : Weight K H L}
    (hχ : χ.IsNonZero) : LinearMap.trace K L (genWeightSpaceProjection K H L χ) = 1 := by
  rw [trace_genWeightSpaceProjection, finrank_rootSpace_eq_one χ hχ, Nat.cast_one]

end Killing

end TauCeti
