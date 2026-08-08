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
is an involution of the base, the **opposition involution** `TauCeti.opposition`, and it preserves
the Cartan pairing, so the permutation it induces on the base is an automorphism of the Dynkin
diagram.

The proof is the classical one. A simple root is exactly a positive root that is not the sum of two
positive roots, and `α ↦ -w₀ α` is an additive bijection of the positive roots, so it preserves
that description. Both halves of the characterisation are proved here: a simple root has height
`1`, hence is not a sum of two roots of height at least `1`; and a positive root that is not simple
is a positive root plus a simple root, which is the decomposition step inside Mathlib's
`RootPairing.Base.IsPos.induction_on_add`, isolated here as a statement of its own.

## Main definitions

* `TauCeti.opposition` is the opposition involution `i ↦ -w₀ i` on root indices.

## Main results

* `TauCeti.mem_support_iff_forall_ne_add`: **the simple roots are exactly the indecomposable
  positive roots**, the description of the base that transports along `-w₀`.
* `TauCeti.root_opposition` and `TauCeti.opposition_involutive`: the opposition map is an
  involution of the root indices realising `α ↦ -w₀ α` on roots.
* `TauCeti.opposition_mem_support` and `TauCeti.bijOn_opposition_support`: **the opposition
  involution permutes the simple roots.**
* `TauCeti.pairing_opposition` and `TauCeti.pairingIn_opposition`: it preserves the Cartan pairing,
  so the induced permutation of the base is a Dynkin diagram automorphism.

## Implementation notes

`TauCeti.opposition` is defined on all of `ι`, not on the subtype `↥b.support`, so that it composes
with the permutation action of the Weyl group without coercions;
`TauCeti.bijOn_opposition_support` records that the simple roots are stable, which is the content.
Its definition spells root negation as `P.reflectionPerm i i` rather than through Mathlib's
`RootPairing.indexNeg`, since the latter is not a global instance and would have to be introduced
by a `let` at every use site; `TauCeti.opposition_eq_reflectionPerm` is the resulting unfolding
lemma.

The indecomposability characterisation is stated with root vectors rather than with an index-level
sum, matching Mathlib's `RootPairing.Base.height_add` and `RootPairing.Base.IsPos.add`, whose
hypothesis is an equation between root vectors: an index-level statement would need a chosen index
for the sum, which need not be unique for a non-reduced pairing.

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

/-! ### The simple roots are the indecomposable positive roots -/

section Indecomposable

variable [CharZero R] (b : P.Base)

variable {P b} in
/-- **A simple root is not the sum of two positive roots.** Heights add, a positive root has height
at least `1`, and a simple root has height exactly `1`. -/
theorem root_ne_add_of_mem_support {i : ι} (hi : i ∈ b.support) {j k : ι}
    (hj : b.IsPos j) (hk : b.IsPos k) : P.root i ≠ P.root j + P.root k := fun h ↦ by
  have hadd := b.height_add h
  rw [b.height_one_of_mem_support hi] at hadd
  rw [RootPairing.Base.isPos_iff] at hj hk
  omega

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

variable {P b} in
/-- **A positive root that is not simple is a positive root plus a simple root.** This is the
decomposition step of Mathlib's `RootPairing.Base.IsPos.induction_on_add`, stated on its own: some
simple root pairs positively with `i`, so subtracting it leaves a root, and that root is still
positive because only a height `1` was removed. -/
theorem exists_isPos_root_eq_add_of_notMem_support {i : ι} (hi : b.IsPos i)
    (hi' : i ∉ b.support) :
    ∃ j ∈ b.support, ∃ k, b.IsPos k ∧ P.root i = P.root k + P.root j := by
  obtain ⟨j, hj, hj'⟩ := hi.exists_mem_support_pos_pairingIn
  rw [P.zero_lt_pairingIn_iff'] at hj'
  have hij : i ≠ j := by rintro rfl; exact hi' hj
  obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
  exact ⟨j, hj, k, hi.sub hj hk, by rw [hk]; module⟩

variable {P b} in
/-- **The simple roots are exactly the indecomposable positive roots.** This is the description of
the base that mentions only the additive structure of the positive roots, so it is the one that
transports along an additive bijection of the positive roots such as `-w₀`. -/
theorem mem_support_iff_forall_ne_add {i : ι} :
    i ∈ b.support ↔
      b.IsPos i ∧ ∀ j k, b.IsPos j → b.IsPos k → P.root i ≠ P.root j + P.root k := by
  refine ⟨fun hi ↦ ⟨RootPairing.Base.isPos_of_mem_support hi,
    fun _ _ hj hk ↦ root_ne_add_of_mem_support hi hj hk⟩, fun ⟨hi, hne⟩ ↦ ?_⟩
  by_contra hi'
  obtain ⟨j, hj, k, hk, hjk⟩ := exists_isPos_root_eq_add_of_notMem_support hi hi'
  exact hne k j hk (RootPairing.Base.isPos_of_mem_support hj) hjk

end Indecomposable

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
theorem opposition_eq_reflectionPerm (i : ι) :
    opposition P b i =
      P.reflectionPerm (P.weylGroupToPerm (longestElement P b) i)
        (P.weylGroupToPerm (longestElement P b) i) :=
  (rfl)

/-- **The opposition involution negates the longest-element translate of a root.** -/
@[simp]
theorem root_opposition (i : ι) :
    P.root (opposition P b i) = -(longestElement P b • P.root i) := by
  rw [opposition_eq_reflectionPerm, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, RootPairing.weylGroup_apply_root]

variable {P b} in
/-- **The opposition involution preserves positivity.** The longest element sends a positive root
to a negative root, and negating a negative root gives a positive one. -/
theorem isPos_opposition {i : ι} (hi : b.IsPos i) : b.IsPos (opposition P b i) := by
  let := P.indexNeg
  rw [opposition_eq_reflectionPerm, ← RootPairing.indexNeg_neg,
    RootPairing.Base.IsPos.neg_iff_not, ← mem_negRoots]
  exact mapsTo_posRoots_negRoots_longestElement P b ((mem_posRoots P b i).mpr hi)

/-- **The opposition involution is an involution.** Root negation commutes with the Weyl-group
action on indices, and the longest element is an involution. -/
theorem opposition_involutive : Involutive (opposition P b) := fun i ↦ by
  let := P.indexNeg
  rw [opposition_eq_reflectionPerm, opposition_eq_reflectionPerm, ← RootPairing.indexNeg_neg,
    ← RootPairing.indexNeg_neg, RootPairing.weylGroupToPerm_neg, neg_neg]
  exact weylGroupToPerm_longestElement_involutive P b i

/-- The opposition involution is a bijection of the root indices. -/
theorem opposition_bijective : Bijective (opposition P b) :=
  (opposition_involutive P b).bijective

/-- **The opposition involution permutes the simple roots.** A simple root is an indecomposable
positive root; `-w₀` is additive, preserves positivity, and is its own inverse, so it cannot turn
an indecomposable positive root into a decomposable one. -/
theorem opposition_mem_support {i : ι} (hi : i ∈ b.support) : opposition P b i ∈ b.support := by
  rw [mem_support_iff_forall_ne_add]
  refine ⟨isPos_opposition (RootPairing.Base.isPos_of_mem_support hi), fun j k hj hk hjk ↦ ?_⟩
  -- Applying `-w₀` to a decomposition of `-w₀ αᵢ` decomposes `αᵢ` itself.
  refine root_ne_add_of_mem_support hi (isPos_opposition hj) (isPos_opposition hk) ?_
  rw [root_opposition, root_opposition, ← neg_add, ← smul_add, ← hjk, root_opposition, smul_neg,
    neg_neg, smul_smul_longestElement]

variable {P b} in
/-- Membership of the base is invariant under the opposition involution. -/
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

/-! ### The opposition involution is a diagram automorphism -/

variable {P b} in
/-- **The opposition involution preserves the Cartan pairing.** Negating both arguments preserves
it, and so does the Weyl group; hence the permutation of the base induced by `-w₀` is an
automorphism of the Dynkin diagram. -/
theorem pairing_opposition (i j : ι) :
    P.pairing (opposition P b i) (opposition P b j) = P.pairing i j := by
  rw [opposition_eq_reflectionPerm, opposition_eq_reflectionPerm,
    RootPairing.pairing_reflectionPerm_self_left, RootPairing.pairing_reflectionPerm_self_right,
    neg_neg, ← RootPairing.root_coroot'_eq_pairing, ← RootPairing.root_coroot'_eq_pairing,
    ← RootPairing.weylGroup_apply_root]
  exact RootPairing.coroot'_weylGroupToPerm_smul P (longestElement P b) j (P.root i)

variable {P b} in
/-- **The opposition involution preserves the integral Cartan pairing**, that is, the entries of
the Cartan matrix of the base. -/
theorem pairingIn_opposition (i j : ι) :
    P.pairingIn ℤ (opposition P b i) (opposition P b j) = P.pairingIn ℤ i j :=
  FaithfulSMul.algebraMap_injective ℤ R <| by
    simpa only [RootPairing.algebraMap_pairingIn] using pairing_opposition (b := b) i j

end Opposition

end TauCeti
