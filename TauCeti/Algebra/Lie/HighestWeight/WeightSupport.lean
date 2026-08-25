/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Reflection
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.LinearAlgebra.RootSystem.DominantCone

public section

/-!
# The weight support of an irreducible highest weight module of dominant integral weight is finite

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a splitting Cartan subalgebra, let `b` be a base of
its root system, and let `M` be an irreducible `L`-module carrying a highest weight vector of
dominant integral weight `lam`. This file proves that `M` has only **finitely many** weights.

`M` is not assumed finite-dimensional, and that is the whole point: for the modules `L(lam)` of
Layer 4 of the highest weight roadmap, finite-dimensionality is the conclusion. Together with
finite-dimensionality of the individual weight spaces it is what makes `L(lam)` finite-dimensional.

## Main results

* `TauCeti.finite_setOf_genWeightSpace_ne_bot_of_isHighestWeightVector`: **an irreducible highest
  weight module of dominant integral weight has finitely many weights.**

## The argument

Three facts about the weights of `M` are already available, none of them needing
finite-dimensionality:

* they lie in the cone `lam - Q⁺`, by the weight-cone theorem of
  `TauCeti/Algebra/Lie/HighestWeight/Module.lean`;
* they take integer values on the simple coroots
  (`TauCeti.exists_int_apply_coroot_of_genWeightSpace_ne_bot_of_isHighestWeightVector`);
* they are stable under the simple reflections
  (`TauCeti.genWeightSpace_rootSystem_reflection_ne_bot`).

`TauCeti.finite_of_forall_reflection_mem_of_sub_mem_posRootCone` turns exactly that combination
into finiteness, so the work here is to feed the three facts to it and then to remove the linearity
restriction: a weight of `M` is a priori only a function `H → K`, but every weight of a highest
weight module is of the form `lam - ν`, hence linear, by
`TauCeti.exists_sub_eq_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top`.

## References

This is the "weight-cone bound" milestone of Layer 4, "the classification of finite-dimensional
irreducibles", of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H} {v : M}

/-- **An irreducible highest weight module of dominant integral weight has finitely many
weights.** Let `M` be irreducible with a highest weight vector of dominant integral weight `lam`.
Then only finitely many functions on the Cartan subalgebra have a nonzero weight space in `M`.

`M` is not assumed finite-dimensional. The three inputs — the weight cone `lam - Q⁺`, integrality
on the simple coroots, and stability under the simple reflections — are exactly the hypotheses of
`TauCeti.finite_of_forall_reflection_mem_of_sub_mem_posRootCone`, and each of them follows from
`hv`, from dominance integrality of `lam`, and from irreducibility of `M` (used only through the
resulting fact that `v` generates `M`). -/
theorem finite_setOf_genWeightSpace_ne_bot_of_isHighestWeightVector
    [LieModule.IsIrreducible K L M] (hv : IsHighestWeightVector b lam v)
    (hlam : IsDominantIntegral b lam) :
    {chi : H → K | genWeightSpace M chi ≠ ⊥}.Finite := by
  have hgen : LieSubmodule.lieSpan K L {v} = ⊤ := lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero
  -- The root system of `H` pairs a weight with a coroot by evaluation, so its `coroot'` is
  -- evaluation at `IsKilling.coroot`; this is the boundary between the two coroot interfaces.
  have hcoroot' : ∀ (i : H.root) (chi : Dual K H),
      (IsKilling.rootSystem H).coroot' i chi = chi (IsKilling.coroot (i : Weight K H L)) := by
    intro i chi
    rw [LinearMap.flip_apply, IsKilling.rootSystem_toLinearMap_apply,
      IsKilling.rootSystem_coroot_apply]
  have hS : {chi : Dual K H | genWeightSpace M ((chi : Dual K H) : H → K) ≠ ⊥}.Finite := by
    refine finite_of_forall_reflection_mem_of_sub_mem_posRootCone (lam := lam) b
      (fun chi hchi ↦ ?_) (fun chi hchi i hi ↦ ?_) fun chi hchi i hi ↦ ?_
    · exact sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen hchi
    · obtain ⟨m, hm⟩ := exists_int_apply_coroot_of_genWeightSpace_ne_bot_of_isHighestWeightVector
        hv hlam hi hchi
      exact ⟨m, by rw [hcoroot' i chi, hm]⟩
    · exact genWeightSpace_rootSystem_reflection_ne_bot hv hlam hi hchi
  refine Set.Finite.subset (hS.image fun psi : Dual K H ↦ (psi : H → K)) fun chi hchi ↦ ?_
  obtain ⟨nu, -, heq⟩ :=
    exists_sub_eq_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen hchi
  exact ⟨lam - nu, by rw [Set.mem_ofPred_eq, heq]; exact hchi, heq⟩

end TauCeti
