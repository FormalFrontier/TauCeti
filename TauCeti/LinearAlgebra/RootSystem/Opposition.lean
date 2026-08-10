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

* `TauCeti.root_opposition` and `TauCeti.opposition_involutive`: the opposition map is an
  involution of the root indices realising `α ↦ -w₀ α` on roots.
* `TauCeti.opposition_mem_support` and `TauCeti.bijOn_opposition_support`: **the opposition
  involution permutes the simple roots.**

## Implementation notes

`TauCeti.opposition` is defined on all of `ι`, not on the subtype `↥b.support`, so that it composes
with the permutation action of the Weyl group without coercions; `TauCeti.oppositionPerm` is its
restriction to the base, and `TauCeti.bijOn_opposition_support` the unbundled form of that
restriction. The definition spells root negation as `P.reflectionPerm i i` rather than through
Mathlib's `RootPairing.indexNeg`, since the latter is not a global instance and would have to be
introduced by a `let` at every use site. `TauCeti.oppositionPerm` is built directly as an
equivalence of `↥b.support` rather than as the `Equiv.Perm.subtypePerm` of an ambient permutation,
so that `TauCeti.coe_oppositionPerm` is a `simp` consequence of the construction rather than a
definitional unfolding of two stacked wrappers.

## References

The longest element `w₀` is the last item of Layer 4 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, where it is pinned by
`w₀ • posRoots b = negRoots b` and `w₀ ^ 2 = 1` — which say exactly that `-w₀` permutes the
positive roots. That this permutation restricts to the base is the prerequisite consumed by
`exists_invariantForm_iff_neg_longest_smul_eq` in
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/Suggested.lean`, whose statement asks for a
Weyl element carrying the dominant cone to its negative: dominance is a condition at the simple
coroot indices, so transporting it along `-w₀` is exactly
`TauCeti.opposition_mem_support`. The argument is the one in J. E. Humphreys, *Introduction to Lie
Algebras and Representation Theory*, GTM 9, Ch. III, §10.3 and §13.1, and in N. Bourbaki, *Groupes
et algèbres de Lie*, Ch. VI, §1.6.
-/

namespace TauCeti

open Function Set

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

/-- **The opposition involution restricts to a bijection of the simple roots.** -/
theorem bijOn_opposition_support :
    BijOn (opposition P b) (b.support : Set ι) (b.support : Set ι) :=
  ⟨fun _ hi ↦ opposition_mem_support P b hi, (opposition_involutive P b).injective.injOn,
    fun i hi ↦ ⟨opposition P b i, opposition_mem_support P b hi, opposition_involutive P b i⟩⟩

/-- **The permutation of the base induced by the opposition involution**, the bundled form of
`TauCeti.bijOn_opposition_support`. -/
noncomputable def oppositionPerm : Equiv.Perm b.support where
  toFun i := ⟨opposition P b i, opposition_mem_support P b i.2⟩
  invFun i := ⟨opposition P b i, opposition_mem_support P b i.2⟩
  left_inv i := Subtype.ext (opposition_opposition P b i)
  right_inv i := Subtype.ext (opposition_opposition P b i)

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
