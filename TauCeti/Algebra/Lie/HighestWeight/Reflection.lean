/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Integrable
public import TauCeti.Algebra.Lie.Weights.Integrable
public import TauCeti.Algebra.Lie.Weights.Reflection
import TauCeti.Algebra.Lie.Submodule.Atom
import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

public section

/-!
# The weights of an irreducible highest weight module are stable under the Weyl group

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a splitting Cartan subalgebra, let `b` be a base of
its root system, and let `M` be an irreducible `L`-module carrying a highest weight vector of
dominant integral weight `lam`. This file records that the weights of `M` are stable under the
reflection in each simple root, hence under the whole Weyl group, and that they are integral on the
simple coroots.

`M` is not assumed finite-dimensional: for the modules of Layer 4 of the highest weight roadmap
finite-dimensionality is the conclusion, not a hypothesis. What is available instead is
integrability along each simple root, proved in
`TauCeti/Algebra/Lie/HighestWeight/Integrable.lean`, and reflection stability is what
`TauCeti/Algebra/Lie/Weights/Integrable.lean` extracts from it. Combined with the weight cone
`lam - Q⁺` of `TauCeti/Algebra/Lie/HighestWeight/Module.lean`, stability under the reflections is
what will confine the weights of `M` to a finite set.

## Main results

* `TauCeti.genWeightSpace_rootSystem_reflection_ne_bot`: **the weights of an irreducible highest
  weight module of dominant integral weight are stable under the reflection in a simple root.**
* `TauCeti.genWeightSpace_weylGroup_smul_ne_bot`: **the weights are stable under the whole Weyl
  group.**
* `TauCeti.genWeightSpace_weylGroup_smul_eq_bot_iff`: a linear form is a nonweight exactly when
  each Weyl translate is a nonweight.
* `TauCeti.sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector`:
  every point of the Weyl orbit of a weight remains below the highest weight in the positive
  root-cone order.
* `TauCeti.exists_int_apply_coroot_of_genWeightSpace_ne_bot_of_isHighestWeightVector`: those
  weights take integer values on the simple coroots.

## References

This is the weight-stability half of the "weight-cone bound" milestone of Layer 4, "the
classification of finite-dimensional irreducibles", of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

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

/-- Integrability along a simple root of an irreducible highest weight module of dominant integral
weight, packaged with the `sl₂` triple it is stated for. -/
private theorem exists_isSl2Triple_locallyFiniteSubmodule_eq_top [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ b.support) :
    ∃ (h₀ e₀ f₀ : L) (t : IsSl2Triple h₀ e₀ f₀), e₀ ∈ rootSpace H (i : Weight K H L) ∧
      f₀ ∈ rootSpace H (-(i : Weight K H L)) ∧
      locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤ := by
  obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hlam i hi
  obtain ⟨h₀, e₀, f₀, t, he₀, hf₀⟩ :=
    IsKilling.exists_isSl2Triple_of_weight_isNonZero (H.isNonZero_coe_root i)
  exact ⟨h₀, e₀, f₀, t, he₀, hf₀, locallyFiniteSubmodule_eq_top_of_isSl2Triple hv hi hn t he₀ hf₀⟩

/-- **The weights of an irreducible highest weight module are integral on the simple coroots.**
Let `M` be irreducible with a highest weight vector of dominant integral weight `lam`. Then every
weight `χ` of `M` takes an integer value on the coroot of a simple root.

`M` is not assumed finite-dimensional; integrability along the simple root replaces that
hypothesis. -/
theorem exists_int_apply_coroot_of_genWeightSpace_ne_bot_of_isHighestWeightVector
    [LieModule.IsIrreducible K L M] (hv : IsHighestWeightVector b lam v)
    (hlam : IsDominantIntegral b lam) {i : H.root} (hi : i ∈ b.support) {χ : H → K}
    (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ m : ℤ, χ (IsKilling.coroot (i : Weight K H L)) = (m : K) := by
  obtain ⟨h₀, e₀, f₀, t, he₀, hf₀, hlf⟩ :=
    exists_isSl2Triple_locallyFiniteSubmodule_eq_top hv hlam hi
  exact exists_int_apply_coroot_of_genWeightSpace_ne_bot (H.isNonZero_coe_root i) t he₀ hf₀ hlf hχ

/-- **The weights of an irreducible highest weight module are stable under the simple
reflections.** Let `M` be irreducible with a highest weight vector of dominant integral weight
`lam`, and let `i` be a simple root of the base `b`. Then the reflection `s_i χ` of a weight `χ` of
`M` is again a weight of `M`.

`M` is not assumed finite-dimensional: it is integrable along `i`
(`TauCeti.locallyFiniteSubmodule_eq_top_of_isSl2Triple`), which is what
`TauCeti.genWeightSpace_sub_apply_coroot_smul_ne_bot` consumes. For a finite-dimensional module
`TauCeti.finrank_weightSpace_rootSystem_reflection` gives the stronger conclusion that the
reflection preserves the multiplicity, for every root and with no highest weight vector in
sight. -/
theorem genWeightSpace_rootSystem_reflection_ne_bot [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ b.support) {χ : Dual K H} (hχ : genWeightSpace M ⇑χ ≠ ⊥) :
    genWeightSpace M ⇑((IsKilling.rootSystem H).reflection i χ) ≠ ⊥ := by
  obtain ⟨h₀, e₀, f₀, t, he₀, hf₀, hlf⟩ :=
    exists_isSl2Triple_locallyFiniteSubmodule_eq_top hv hlam hi
  rw [coe_rootSystem_reflection_apply]
  exact genWeightSpace_sub_apply_coroot_smul_ne_bot (H.isNonZero_coe_root i) t he₀ hf₀ hlf hχ

/-- **The weights of an irreducible highest weight module are stable under the Weyl group.** Let
`M` be irreducible with a highest weight vector of dominant integral weight `lam`. If `χ` is a
weight of `M`, then `w • χ` is a weight of `M` for every element `w` of the Weyl group.

The module is not assumed finite-dimensional. -/
theorem genWeightSpace_weylGroup_smul_ne_bot [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam)
    (w : (IsKilling.rootSystem H).weylGroup) {χ : Dual K H} (hχ : genWeightSpace M ⇑χ ≠ ⊥) :
    genWeightSpace M ⇑(w • χ) ≠ ⊥ := by
  obtain ⟨l, rfl⟩ := exists_wordProd_eq (IsKilling.rootSystem H) b w
  induction l with
  | nil => simpa
  | cons i l ih =>
    rw [wordProd_cons, mul_smul, RootPairing.weylGroup.ofIdx_smul,
      RootPairing.Equiv.reflection_smul]
    exact genWeightSpace_rootSystem_reflection_ne_bot hv hlam i.2 ih

-- Not `@[simp]`: `b`, `lam`, and `v` cannot be inferred from the rewrite target, so `simpNF`
-- rejects the rule as one that will never apply.
/-- A linear form is not a weight of an irreducible highest weight module of dominant integral
weight exactly when any Weyl translate is not a weight. -/
theorem genWeightSpace_weylGroup_smul_eq_bot_iff [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam)
    (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H) :
    genWeightSpace M ⇑(w • χ) = ⊥ ↔ genWeightSpace M ⇑χ = ⊥ := by
  constructor
  · intro hwχ
    by_contra hχ
    exact genWeightSpace_weylGroup_smul_ne_bot hv hlam w hχ hwχ
  · intro hχ
    by_contra hwχ
    have h := genWeightSpace_weylGroup_smul_ne_bot hv hlam w⁻¹ hwχ
    rw [inv_smul_smul] at h
    exact h hχ

/-- **The Weyl orbit of every weight remains below the highest weight.** If `M` is irreducible
with a highest weight vector of dominant integral weight `lam`, then for every weight `χ` and
every Weyl-group element `w`, the difference `lam - w • χ` belongs to the positive root cone.

This combines Weyl stability with the weight-cone theorem for highest weight modules. -/
theorem sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector
    [LieModule.IsIrreducible K L M] (hv : IsHighestWeightVector b lam v)
    (hlam : IsDominantIntegral b lam) (w : (IsKilling.rootSystem H).weylGroup)
    {χ : Dual K H} (hχ : genWeightSpace M ⇑χ ≠ ⊥) :
    lam - w • χ ∈ posRootCone (IsKilling.rootSystem H) b :=
  sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top hv
    (lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero)
    (genWeightSpace_weylGroup_smul_ne_bot hv hlam w hχ)

end TauCeti
