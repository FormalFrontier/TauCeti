/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.LongestElement

public section

/-!
# The opposition involution of a base

The longest element `w₀` of a finite Weyl group exchanges the positive and the negative roots, so
`α ↦ -w₀ α` permutes the positive roots. This file proves that it permutes the **simple** roots: it
is an involution of the base, the **opposition involution** `TauCeti.opposition`, and it preserves
the Cartan pairing, so the permutation it induces on the base is an automorphism of the Dynkin
diagram.

The proof is the classical one. A simple root is exactly a positive root that is not the sum of two
positive roots — that is `TauCeti.mem_support_iff_forall_ne_add`, proved in
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
* `TauCeti.pairing_opposition`, `TauCeti.pairingIn_opposition` and
  `TauCeti.cartanMatrix_oppositionPerm`: it preserves the Cartan pairing and hence the Cartan
  matrix, so `TauCeti.oppositionPerm` is an automorphism of the Dynkin diagram.

## Implementation notes

`TauCeti.opposition` is defined on all of `ι`, not on the subtype `↥b.support`, so that it composes
with the permutation action of the Weyl group without coercions; `TauCeti.oppositionPerm` is its
restriction to the base, and `TauCeti.bijOn_opposition_support` the unbundled form of that
restriction. The definition spells root negation as `P.reflectionPerm i i` rather than through
Mathlib's `RootPairing.indexNeg`, since the latter is not a global instance and would have to be
introduced by a `let` at every use site.

## References

This completes the API of the longest element, the last item of Layer 4 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, where `w₀` is pinned by
`w₀ • posRoots b = negRoots b` and `w₀ ^ 2 = 1` — which say exactly that `-w₀` permutes the
positive roots — and the statements here say that this permutation restricts to the base. The
argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
GTM 9, Ch. III, §10.3 and §13.1, and in N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1.6.
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

/-- The opposition involution, unfolded: root negation applied to the longest-element image. -/
private theorem opposition_def (i : ι) :
    opposition P b i =
      P.reflectionPerm (P.weylGroupToPerm (longestElement P b) i)
        (P.weylGroupToPerm (longestElement P b) i) :=
  (rfl)

/-- **The opposition involution negates the longest-element translate of a root.** -/
@[simp]
theorem root_opposition (i : ι) :
    P.root (opposition P b i) = -(longestElement P b • P.root i) := by
  rw [opposition_def, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, RootPairing.weylGroup_apply_root]

variable {P b} in
/-- **The opposition involution preserves positivity.** -/
theorem isPos_opposition {i : ι} (hi : b.IsPos i) : b.IsPos (opposition P b i) := by
  -- The longest element sends a positive root to a negative root, and negating a negative root
  -- gives a positive one.
  let := P.indexNeg
  rw [opposition_def, ← RootPairing.indexNeg_neg,
    RootPairing.Base.IsPos.neg_iff_not, ← mem_negRoots]
  exact mapsTo_posRoots_negRoots_longestElement P b ((mem_posRoots P b i).mpr hi)

/-- **The opposition involution is an involution.** -/
theorem opposition_involutive : Involutive (opposition P b) := fun i ↦ by
  -- Root negation commutes with the Weyl-group action on indices, and the longest element is an
  -- involution.
  let := P.indexNeg
  rw [opposition_def, opposition_def, ← RootPairing.indexNeg_neg,
    ← RootPairing.indexNeg_neg, RootPairing.weylGroupToPerm_neg, neg_neg]
  exact weylGroupToPerm_longestElement_involutive P b i

/-- The opposition involution is a bijection of the root indices. -/
theorem opposition_bijective : Bijective (opposition P b) :=
  (opposition_involutive P b).bijective

/-- **The opposition involution permutes the simple roots.** -/
theorem opposition_mem_support {i : ι} (hi : i ∈ b.support) : opposition P b i ∈ b.support := by
  -- A simple root is an indecomposable positive root; `-w₀` is additive, preserves positivity and
  -- is its own inverse, so applying it to a decomposition of `-w₀ αᵢ` decomposes `αᵢ` itself.
  rw [mem_support_iff_forall_ne_add]
  refine ⟨isPos_opposition (RootPairing.Base.isPos_of_mem_support hi), fun j k hj hk hjk ↦ ?_⟩
  refine root_ne_add_of_mem_support hi (isPos_opposition hj) (isPos_opposition hk) ?_
  rw [root_opposition, root_opposition, ← neg_add, ← smul_add, ← hjk, root_opposition, smul_neg,
    neg_neg, smul_smul_longestElement]

variable {P b} in
/-- Membership of the base is invariant under the opposition involution. -/
@[simp]
theorem opposition_mem_support_iff {i : ι} : opposition P b i ∈ b.support ↔ i ∈ b.support := by
  refine ⟨fun h ↦ ?_, opposition_mem_support P b⟩
  simpa only [opposition_involutive P b i] using opposition_mem_support P b h

/-- **The opposition involution restricts to a bijection of the simple roots.** -/
theorem bijOn_opposition_support :
    BijOn (opposition P b) (b.support : Set ι) (b.support : Set ι) :=
  ⟨fun _ hi ↦ opposition_mem_support P b hi, (opposition_involutive P b).injective.injOn,
    fun i hi ↦ ⟨opposition P b i, opposition_mem_support P b hi, opposition_involutive P b i⟩⟩

/-- **The opposition involution fixes the base setwise.** -/
theorem image_opposition_support :
    opposition P b '' (b.support : Set ι) = (b.support : Set ι) :=
  (bijOn_opposition_support P b).image_eq

/-- **The permutation of the base induced by the opposition involution**, the bundled form of
`TauCeti.bijOn_opposition_support`. -/
noncomputable def oppositionPerm : Equiv.Perm b.support :=
  ((opposition_involutive P b).toPerm _).subtypePerm fun _ ↦ opposition_mem_support_iff

@[simp]
theorem coe_oppositionPerm (i : b.support) :
    (oppositionPerm P b i : ι) = opposition P b i :=
  (rfl)

/-! ### The opposition involution is a diagram automorphism -/

variable {P b} in
/-- **The opposition involution preserves the Cartan pairing.** -/
@[simp]
theorem pairing_opposition (i j : ι) :
    P.pairing (opposition P b i) (opposition P b j) = P.pairing i j := by
  -- Negating both arguments preserves the pairing, and so does the Weyl group.
  rw [opposition_def, opposition_def,
    RootPairing.pairing_reflectionPerm_self_left, RootPairing.pairing_reflectionPerm_self_right,
    neg_neg, ← RootPairing.root_coroot'_eq_pairing, ← RootPairing.root_coroot'_eq_pairing,
    ← RootPairing.weylGroup_apply_root]
  exact RootPairing.coroot'_weylGroupToPerm_smul P (longestElement P b) j (P.root i)

variable {P b} in
/-- **The opposition involution preserves the integral Cartan pairing**, that is, the entries of
the Cartan matrix of the base. -/
@[simp]
theorem pairingIn_opposition (i j : ι) :
    P.pairingIn ℤ (opposition P b i) (opposition P b j) = P.pairingIn ℤ i j :=
  FaithfulSMul.algebraMap_injective ℤ R <| by
    simpa only [RootPairing.algebraMap_pairingIn] using pairing_opposition (b := b) i j

/-- **The permutation of the base induced by the opposition involution is an automorphism of the
Dynkin diagram**: it preserves the Cartan matrix. -/
theorem cartanMatrix_oppositionPerm (i j : b.support) :
    b.cartanMatrix (oppositionPerm P b i) (oppositionPerm P b j) = b.cartanMatrix i j := by
  simp only [RootPairing.Base.cartanMatrixIn_def, coe_oppositionPerm, pairingIn_opposition]

end Opposition

end TauCeti
