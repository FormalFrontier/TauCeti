/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.LongestElement

public section

/-!
# The opposition involution of a base

The longest element `w₀` of a finite Weyl group exchanges the positive and the negative roots, so
`α ↦ -w₀ α` permutes the positive roots. This file proves that it permutes the **simple** roots: it
is an involution of the base, the **opposition involution** `TauCeti.opposition`.

The proof is the classical one. A simple root is exactly a positive root that is not the sum of two
positive roots — that is `TauCeti.mem_support_iff_isPos_and_forall_ne_add`, proved in
`TauCeti/LinearAlgebra/RootSystem/Positive.lean` — and `α ↦ -w₀ α` is an additive bijection of the
positive roots, so it preserves that description.

## Main definitions

* `TauCeti.opposition` is the opposition involution `i ↦ -w₀ i` on root indices.
* `TauCeti.oppositionPerm` is the permutation of the base that it induces.

## Main results

* `TauCeti.root_opposition`, `TauCeti.coroot'_opposition` and `TauCeti.opposition_involutive`: the
  opposition map is an involution of the root indices realising `α ↦ -w₀ α` on roots, and negating
  the longest-element translate on the coroot functionals.
* `TauCeti.opposition_mem_support`: **the opposition involution permutes the simple roots.**

## Implementation notes

`TauCeti.opposition` is defined on all of `ι`, not on the subtype `↥b.support`, so that it composes
with the permutation action of the Weyl group without coercions; `TauCeti.oppositionPerm` is its
restriction to the base. The definition spells root negation as `P.reflectionPerm i i` rather than
through Mathlib's `RootPairing.indexNeg`, since the latter is not a global instance and would have
to be introduced by a `let` at every use site. `TauCeti.oppositionPerm` is the
`Equiv.Perm.subtypePerm` of the ambient `Function.Involutive.toPerm`; its membership hypothesis is
rewritten along `Function.Involutive.coe_toPerm` instead of being supplied directly, because
`TauCeti.opposition` is not `@[expose]` and the term is then not type-correct at reducible
transparency, which blocks `rw` and `simp` on `TauCeti.coe_oppositionPerm`.

## References

This file belongs to the "longest element" item, last in Layer 4 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` — the stage implemented by its sole
import `TauCeti/LinearAlgebra/RootSystem/LongestElement.lean`. That item pins `w₀` by
`w₀ • posRoots b = negRoots b` and `w₀ ^ 2 = 1`, which say exactly that `-w₀` is an involutive
permutation of the positive roots; proved here is *which* permutation it is, namely one that
restricts to the base. Every stage the argument stands on is on `main`: the positivity and height
API of Layer 1 (`TauCeti/LinearAlgebra/RootSystem/Positive.lean`, where the indecomposability
characterisation it consumes lives), and the chamber, fundamental-domain and longest-element
results of Layer 4.

Restricting `-w₀` to the base is what lets a condition imposed on the values of the *simple* coroot
functionals be transported along it. Its companion `LongestElement.lean` already transports one
such condition: `TauCeti.neg_smul_mem_dominantChamber_longestElement` says `-(w₀ • x)` is dominant
whenever `x` is, and that argument needs only that `-w₀` carries positive roots to positive roots.
Integrality is the condition that needs the restriction to the base itself.
`TauCeti.IsDominantIntegral` in `TauCeti/Algebra/Lie/HighestWeight/Basic.lean` is such a condition
— `∀ i ∈ b.support, ∃ n : ℕ, lam (coroot i) = (n : K)` — and transporting it along `-w₀` asks for
the natural value of `lam` at the *simple* index `opposition i`, so it needs exactly
`TauCeti.opposition_mem_support` and `TauCeti.coroot'_opposition`. That transport is one conjunct
of `exists_invariantForm_iff_neg_longest_smul_eq` in
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/Suggested.lean`; the conjunct mentions no Lie
algebra and no Verma module, and nothing here depends on the enveloping-algebra layers on which the
rest of that target rests. The argument is the one in J. E. Humphreys, *Introduction to Lie
Algebras and Representation Theory*, GTM 9, Ch. III, §10.3 and §13.1, and in N. Bourbaki, *Groupes
et algèbres de Lie*, Ch. VI, §1.6.
-/

namespace TauCeti

open Function

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-! ### The opposition involution -/

section Opposition

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] (b : P.Base)

/-- **The opposition involution** of a base: the map `i ↦ -w₀ i` on root indices, where `w₀` is the
longest element of the Weyl group. On root vectors it is `α ↦ -w₀ α`, so it permutes the positive
roots; `TauCeti.opposition_mem_support` says that it permutes the simple roots. -/
noncomputable def opposition (i : ι) : ι :=
  P.reflectionPerm (P.weylGroupToPerm (longestElement P b) i)
    (P.weylGroupToPerm (longestElement P b) i)

/-- **The opposition involution negates the longest-element translate of a root.** -/
@[simp]
theorem root_opposition (i : ι) :
    P.root (opposition P b i) = -(longestElement P b • P.root i) := by
  rw [opposition, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, RootPairing.weylGroup_apply_root]

/-- **The opposition involution negates the coroot functional along the longest element.** This is
the coroot-side companion of `TauCeti.root_opposition`: dominance is a condition on the values of
the simple coroot functionals, so this is the form in which the involution is applied to weights.
Like its siblings `TauCeti.RootPairing.coroot'_smul` and
`TauCeti.RootPairing.coroot'_weylGroupToPerm_smul` it is stated pointwise and tagged `@[grind =]`
rather than `@[simp]`, since `P.coroot' j x` is not in simp-normal form: `simp` rewrites it to
`P.toLinearMap x (P.coroot j)` by `LinearMap.flip_apply`. -/
@[grind =]
theorem coroot'_opposition (i : ι) (x : M) :
    P.coroot' (opposition P b i) x = -P.coroot' i (longestElement P b • x) := by
  rw [opposition, RootPairing.coroot'_reflectionPerm_self, coroot'_smul_longestElement,
    LinearMap.neg_apply]

variable {P b} in
/-- **The opposition involution preserves positivity.** -/
theorem isPos_opposition {i : ι} (hi : b.IsPos i) : b.IsPos (opposition P b i) := by
  -- The longest element sends a positive root to a negative root, and negating a negative root
  -- gives a positive one.
  let := P.indexNeg
  rw [opposition, ← RootPairing.indexNeg_neg,
    RootPairing.Base.IsPos.neg_iff_not, ← mem_negRoots]
  exact mapsTo_posRoots_negRoots_longestElement P b ((mem_posRoots P b i).mpr hi)

/-- **The opposition involution is an involution.** -/
@[simp]
theorem opposition_opposition (i : ι) : opposition P b (opposition P b i) = i := by
  -- Root negation commutes with the Weyl-group action on indices, and the longest element is an
  -- involution.
  let := P.indexNeg
  rw [opposition, opposition, ← RootPairing.indexNeg_neg,
    ← RootPairing.indexNeg_neg, RootPairing.weylGroupToPerm_neg, neg_neg]
  exact weylGroupToPerm_longestElement_involutive P b i

/-- **The opposition involution is an involution**, in bundled form. -/
theorem opposition_involutive : Involutive (opposition P b) := opposition_opposition P b

/-- **The opposition involution permutes the simple roots.** -/
theorem opposition_mem_support {i : ι} (hi : i ∈ b.support) : opposition P b i ∈ b.support := by
  -- A simple root is an indecomposable positive root; `-w₀` is additive, preserves positivity and
  -- is its own inverse, so applying it to a decomposition of `-w₀ αᵢ` decomposes `αᵢ` itself.
  rw [mem_support_iff_isPos_and_forall_ne_add]
  refine ⟨isPos_opposition (RootPairing.Base.isPos_of_mem_support hi), fun j k hj hk hjk ↦ ?_⟩
  refine root_ne_add_of_mem_support hi (isPos_opposition hj) (isPos_opposition hk) ?_
  -- Additivity: `-w₀` carries a decomposition of a root to one of its opposite.
  have hadd : ∀ a c d : ι, P.root a = P.root c + P.root d →
      P.root (opposition P b a) = P.root (opposition P b c) + P.root (opposition P b d) :=
    fun _ _ _ h ↦ by simp only [root_opposition, h, smul_add, neg_add]
  simpa only [opposition_opposition] using hadd _ _ _ hjk

variable {P b} in
/-- Membership of the base is invariant under the opposition involution. -/
@[simp]
theorem opposition_mem_support_iff {i : ι} : opposition P b i ∈ b.support ↔ i ∈ b.support := by
  refine ⟨fun h ↦ ?_, opposition_mem_support P b⟩
  simpa only [opposition_opposition] using opposition_mem_support P b h

/-- **The permutation of the base induced by the opposition involution**: the restriction of
`TauCeti.opposition` to the simple roots, which it permutes by `TauCeti.opposition_mem_support`. -/
noncomputable def oppositionPerm : Equiv.Perm b.support :=
  -- The membership hypothesis is rewritten along `Involutive.coe_toPerm` rather than supplied
  -- directly, so that the resulting term stays type-correct at reducible transparency and
  -- `TauCeti.coe_oppositionPerm` is a `simp` consequence of the two constructors.
  ((opposition_involutive P b).toPerm _).subtypePerm fun _ ↦ by
    rw [Involutive.coe_toPerm]; exact opposition_mem_support_iff

@[simp]
theorem coe_oppositionPerm (i : b.support) :
    (oppositionPerm P b i : ι) = opposition P b i := by
  simp [oppositionPerm]

/-- **The induced permutation of the base is an involution.** -/
@[simp]
theorem oppositionPerm_oppositionPerm (i : b.support) :
    oppositionPerm P b (oppositionPerm P b i) = i :=
  Subtype.ext (by simp)

end Opposition

end TauCeti
