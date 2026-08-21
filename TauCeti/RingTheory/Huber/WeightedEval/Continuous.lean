/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Hom

/-!
# The evaluation of `A⟨X⟩_T` is continuous

`WeightedEval/Hom.lean` packages Wedhorn's evaluation as a ring homomorphism `A⟨X⟩_T →+* B`. This
file proves it continuous for the topology of `A⟨X⟩_T`, which is the last property Proposition
5.50 asks of the extension apart from its uniqueness.

The argument is the one that made the terms summable, run at a fixed series rather than along the
cofinite filter, and it shares its estimate: a basic neighbourhood `U⟨X⟩` of zero bounds *every*
coefficient of `f` by `Tν · U`, so `TauCeti.Huber.weightedEvalTerm_mem_of_mem_weightMul` — applied
at every `ν` rather than at cofinitely many — puts *every* term of the evaluation in a prescribed
open subgroup `G` of `B`. The partial sums then lie in `G` because it is a subgroup, and the sum
lies in `G` because an open subgroup is closed.

## Main results

* `TauCeti.Huber.continuous_weightedEvalHom`: the evaluation homomorphism is continuous.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **The evaluation homomorphism `A⟨X⟩_T →+* B` is continuous**, under the hypotheses that make
it exist: `φ` continuous at zero and the weighted monomials `φ(Tν) · bν` bounded.

With `weightedEvalHom_weightedC` and `weightedEvalHom_weightedX`, this gives every property
Proposition 5.50 asks of the extension except the uniqueness, which is
`TauCeti.Huber.weightedRestrictedSubring_ringHom_ext_of_continuous`;
`WeightedEval/UniversalProperty.lean` assembles the two into 5.50. -/
theorem continuous_weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : Continuous (weightedEvalHom hT hφ hb) := by
  have _ : IsTopologicalRing (weightedRestrictedSubring T hT) :=
    isTopologicalRing_weightedTopology
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  refine Filter.tendsto_def.mpr fun W hW ↦ ?_
  obtain ⟨G, hGW⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
  obtain ⟨V, hV, hVG⟩ := isBounded_iff.mp ((isWeightBounded_iff φ T b).mp hb) (G : Set B)
    (G.isOpen.mem_nhds G.zero_mem)
  obtain ⟨U, hUV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (hφ.preimage_mem_nhds (by simpa only [map_zero] using hV))
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_weightedTopology hT).mem_of_mem (i := U) trivial) fun f hf ↦ ?_
  refine hGW ?_
  rw [coe_weightedEvalHom]
  refine G.isClosed.mem_of_tendsto
    (hasSum_weightedEval hφ hb (mem_weightedRestrictedSubring.mp f.property)) ?_
  filter_upwards with s
  exact G.toAddSubgroup.sum_mem fun ν _ ↦
    weightedEvalTerm_mem_of_mem_weightMul (fun _ ⟨u, hu, hval⟩ ↦ hval ▸ hUV hu)
      ((Set.mul_subset_mul_left (Set.subset_iUnion _ ν)).trans hVG) (mem_weightedNhd.mp hf ν)

end TauCeti.Huber

end
