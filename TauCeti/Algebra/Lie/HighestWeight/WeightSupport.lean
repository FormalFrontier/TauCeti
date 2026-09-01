/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Reflection
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.Algebra.Lie.Weights.FormalCharacter
import TauCeti.LinearAlgebra.RootSystem.DominantCone

public section

/-!
# The weight support of a highest weight module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a splitting Cartan subalgebra, let `b` be a base of
its root system, and let `M` be an `L`-module carrying a highest weight vector of weight `lam`.
This file describes the weights of `M` in two ways.

If `M` is irreducible and `lam` is dominant integral, `M` has only **finitely many** weights. `M`
is not assumed finite-dimensional, and that is the whole point: for the modules `L(lam)` of
Layer 4 of the highest weight roadmap, finite-dimensionality is the conclusion. Together with
finite-dimensionality of the individual weight spaces it is what makes `L(lam)` finite-dimensional.

If instead `M` is finite-dimensional, every weight of `M` has a **dominant integral Weyl
conjugate** which is again a weight of `M`. That is the form in which a weight of `M` is compared
with `lam`, for example by the Casimir scalar in
`TauCeti/Algebra/Lie/HighestWeight/Separation.lean`; dominance is what makes the invariant form
available with a sign.

## Main results

* `TauCeti.finite_setOf_genWeightSpace_ne_bot_of_isHighestWeightVector`: **an irreducible highest
  weight module of dominant integral weight has finitely many weights.**
* `TauCeti.exists_weylGroup_smul_isDominantIntegral_of_genWeightSpace_ne_bot`: **every weight of a
  finite-dimensional highest weight module has a dominant integral Weyl conjugate, again a weight
  of the module.**

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

The dominant conjugate comes from the same cone induction, used one step earlier: the raising step
`TauCeti.exists_weylGroup_smul_dominant_of_forall_reflection_mem_of_sub_mem_posRootCone` records
which Weyl translate reaches a dominant member, and finiteness is its corollary. There the three
facts are read off a finite-dimensional module instead, which needs neither irreducibility nor
dominance of `lam`: the weights of such a module are Weyl stable
(`TauCeti.formalCharacter_coeff_weylGroup_smul`) and integral
(`TauCeti.isIntegralWeight_of_formalCharacter_coeff_ne_zero`).

## References

This is the "weight-cone bound" milestone of Layer 4, "the classification of finite-dimensional
irreducibles", of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, together with
the dominant-conjugate step that Layer 7's "Freudenthal's multiplicity formula" needs.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2, and
  §13.2 for the dominant conjugate.
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
  have hS : {chi : Dual K H | genWeightSpace M ((chi : Dual K H) : H → K) ≠ ⊥}.Finite := by
    refine finite_of_forall_reflection_mem_of_sub_mem_posRootCone (lam := lam) b
      (fun chi hchi ↦ ?_) (fun chi hchi i hi ↦ ?_) fun chi hchi i hi ↦ ?_
    · exact sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen hchi
    · obtain ⟨m, hm⟩ := exists_int_apply_coroot_of_genWeightSpace_ne_bot_of_isHighestWeightVector
        hv hlam hi hchi
      exact ⟨m, by rw [rootSystem_coroot'_apply, IsKilling.rootSystem_coroot_apply, hm]⟩
    · exact genWeightSpace_rootSystem_reflection_ne_bot hv hlam hi hchi
  refine Set.Finite.subset (hS.image fun psi : Dual K H ↦ (psi : H → K)) fun chi hchi ↦ ?_
  obtain ⟨nu, -, heq⟩ :=
    exists_sub_eq_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen hchi
  exact ⟨lam - nu, by rw [Set.mem_ofPred_eq, heq]; exact hchi, heq⟩

section FiniteDimensional

variable [IsTriangularizable K H L] [FiniteDimensional K M]

/-- **Every weight of a finite-dimensional highest weight module has a dominant integral Weyl
conjugate, again a weight of the module.** Here `M` is a module over an algebraically closed field
of characteristic zero, generated by a highest weight vector of weight `lam`, and `M` is not
assumed irreducible.

The weights of a finite-dimensional module form a Weyl-stable set
(`TauCeti.formalCharacter_coeff_weylGroup_smul`) of integral weights
(`TauCeti.isIntegralWeight_of_formalCharacter_coeff_ne_zero`), and for a highest weight module they
lie below the highest weight; that is exactly the input of
`TauCeti.exists_weylGroup_smul_dominant_of_forall_reflection_mem_of_sub_mem_posRootCone`. -/
theorem exists_weylGroup_smul_isDominantIntegral_of_genWeightSpace_ne_bot
    (hv : IsHighestWeightVector b lam v) (hgen : LieSubmodule.lieSpan K L {v} = ⊤)
    {mu : Dual K H} (hmu : genWeightSpace M (mu : H → K) ≠ ⊥) :
    ∃ w : (IsKilling.rootSystem H).weylGroup,
      genWeightSpace M ((w • mu : Dual K H) : H → K) ≠ ⊥ ∧
        IsDominantIntegral b (w • mu) := by
  classical
  -- The root system of `H` pairs a weight with a coroot by evaluation, so its `coroot'` is
  -- evaluation at the coroot; this is the boundary between the two coroot interfaces.
  have hcoroot' : ∀ (i : H.root) (chi : Dual K H),
      (IsKilling.rootSystem H).coroot' i chi = chi ((IsKilling.rootSystem H).coroot i) :=
    fun i chi ↦ by rw [LinearMap.flip_apply, IsKilling.rootSystem_toLinearMap_apply]
  have hweyl : ∀ (w : (IsKilling.rootSystem H).weylGroup) (chi : Dual K H),
      genWeightSpace M ((w • chi : Dual K H) : H → K) = ⊥ ↔
        genWeightSpace M (chi : H → K) = ⊥ := fun w chi ↦ by
    rw [← formalCharacter_coeff_eq_zero_iff, ← formalCharacter_coeff_eq_zero_iff,
      formalCharacter_coeff_weylGroup_smul]
  set S : Set (Dual K H) := {chi : Dual K H | genWeightSpace M (chi : H → K) ≠ ⊥}
  have hcone : ∀ chi ∈ S, lam - chi ∈ posRootCone (IsKilling.rootSystem H) b :=
    fun chi hchi ↦
      sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen hchi
  have hint : ∀ chi ∈ S, ∀ i ∈ b.support,
      ∃ z : ℤ, (IsKilling.rootSystem H).coroot' i chi = (z : K) := by
    intro chi hchi i _
    obtain ⟨z, hz⟩ := (isIntegralWeight_of_formalCharacter_coeff_ne_zero
      ((not_congr formalCharacter_coeff_eq_zero_iff).mpr hchi)).exists_int_apply_coroot
      (i : Weight K H L)
    exact ⟨z, by rw [hcoroot', IsKilling.rootSystem_coroot_apply, hz]⟩
  have hrefl : ∀ chi ∈ S, ∀ i ∈ b.support,
      (IsKilling.rootSystem H).reflection i chi ∈ S := by
    intro chi hchi i _
    have hsmul : (IsKilling.rootSystem H).reflection i chi =
        (RootPairing.weylGroup.ofIdx (IsKilling.rootSystem H) i) • chi := by
      rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul]
    exact fun h ↦ hchi ((hweyl _ chi).mp (hsmul ▸ h))
  obtain ⟨w, hwS, hwdom⟩ :=
    exists_weylGroup_smul_dominant_of_forall_reflection_mem_of_sub_mem_posRootCone b hcone hint
      hrefl hmu
  refine ⟨w, hwS, isDominantIntegral_iff.mpr fun i hi ↦ ?_⟩
  obtain ⟨n, hn⟩ := hwdom i hi
  exact ⟨n, by rw [← hcoroot', hn]⟩

end FiniteDimensional

end TauCeti
