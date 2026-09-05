/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Opposition

/-!
# The lowest weight of an irreducible highest weight module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a splitting Cartan subalgebra, let `b` be a base of
its root system, and let `M` be an irreducible `L`-module carrying a highest weight vector of
dominant integral weight `lam`. This file identifies `w₀ • lam` as the **lowest** weight of `M`,
`w₀` being the longest element of the Weyl group.

The weights of `M` are stable under the Weyl group and lie below `lam`
(`TauCeti.sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector`),
so applying `w₀` — which carries the positive root cone to its negative
(`TauCeti.neg_smul_mem_posRootCone_longestElement`) — shows that every weight of `M` lies *above*
`w₀ • lam`. Since the positive root cone is pointed, nothing at all sits below `w₀ • lam`:
subtracting a positive root from it leaves the weight support.

`M` is not assumed finite-dimensional here; the statements are about the weight support alone.

The dominance of the opposite weight `-(w₀ • lam)` is proved alongside, since it is the same
computation with the opposition involution of the base and no module is involved.

## Main results

* `TauCeti.IsDominantIntegral.neg_longestElement_smul`: `-(w₀ • lam)` is dominant integral when
  `lam` is, by the opposition involution of the base.
* `TauCeti.sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot`: **`w₀ • lam` is the
  lowest weight**, and `TauCeti.genWeightSpace_longestElement_smul_sub_root_eq_bot` is the form a
  construction below the lowest weight space consumes.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.6.
-/

public section

namespace TauCeti

open LieAlgebra Module _root_.LieModule

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H}

/-! ### Dominance of the opposite weight -/

/-- **The opposite of a dominant integral weight is dominant integral.** The opposition involution
`i ↦ -w₀ i` permutes the simple roots (`TauCeti.opposition_mem_support`), and the value of
`-(w₀ • lam)` on the coroot of `αᵢ` is the value of `lam` on the coroot of the opposite simple
root. -/
theorem IsDominantIntegral.neg_longestElement_smul (hlam : IsDominantIntegral b lam) :
    IsDominantIntegral b (-(longestElement (IsKilling.rootSystem H) b • lam)) := by
  refine isDominantIntegral_iff.mpr fun i hi => ?_
  obtain ⟨n, hn⟩ :=
    isDominantIntegral_iff.mp hlam _ (opposition_mem_support (IsKilling.rootSystem H) b hi)
  refine ⟨n, ?_⟩
  have h := coroot'_opposition (IsKilling.rootSystem H) b i lam
  rw [rootSystem_coroot'_apply, rootSystem_coroot'_apply, hn] at h
  rw [LinearMap.neg_apply, h]

/-! ### The lowest weight -/

variable [IsAlgClosed K]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {v : M}
  [_root_.LieModule.IsIrreducible K L M]

/-- **`w₀ • lam` is the lowest weight of an irreducible highest weight module.** Every weight lies
above it, in the sense that their difference is a nonnegative combination of the simple roots.

The weights of `M` are stable under the Weyl group and lie below `lam`; applying `w₀`, which
negates the positive root cone, reverses the inequality. -/
theorem sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {chi : Dual K H}
    (hchi : genWeightSpace M ⇑chi ≠ ⊥) :
    chi - longestElement (IsKilling.rootSystem H) b • lam
      ∈ posRootCone (IsKilling.rootSystem H) b := by
  have h := sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector
    hv hlam (longestElement (IsKilling.rootSystem H) b) hchi
  have h2 := neg_smul_mem_posRootCone_longestElement h
  rwa [smul_sub, smul_smul_longestElement, neg_sub] at h2

omit [IsAlgClosed K] [_root_.LieModule.IsIrreducible K L M] in
/-- The weight underlying the difference of a weight and a root is the pointwise difference. -/
private theorem coe_sub_root_rootSystem (x : Dual K H) (i : H.root) :
    ⇑(x - (IsKilling.rootSystem H).root i) = ⇑x - (i : H → K) :=
  rfl

/-- **Nothing lies below the lowest weight.** Subtracting a positive root from `w₀ • lam` leaves
the weight support of `M`: the positive root cone is pointed, so a weight below the lowest one
would give a positive root whose negative is again in the cone. -/
theorem genWeightSpace_longestElement_smul_sub_root_eq_bot
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) :
    genWeightSpace M (⇑(longestElement (IsKilling.rootSystem H) b • lam) - (i : H → K)) = ⊥ := by
  by_contra hne
  rw [← coe_sub_root_rootSystem] at hne
  have h := sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot hv hlam hne
  rw [sub_sub_cancel_left] at h
  exact root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone (IsKilling.rootSystem H) b hi h
    (add_neg_cancel _)

end TauCeti
