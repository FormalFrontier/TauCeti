/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The Weyl orbit of the simple roots

A base of a root pairing carries only finitely much data — the Cartan matrix of its simple roots —
yet it controls every root, because the Weyl-group orbits of the simple roots cover all roots. This
file proves that covering statement, at the level of root indices, and draws the consequence that
concerns lengths: a root-positive form takes on the roots exactly the values it takes on the simple
roots.

The proof is the lowering argument of Layer 1, packaged by Mathlib as
`RootPairing.Base.induction_reflect`: reflecting a positive root in a suitable simple root
decreases its height, and reflection in a root sends that root to its negative, so induction on
height reaches a simple root from anywhere.

## Main results

* `TauCeti.exists_mem_support_weylGroupToPerm_eq`: **every root index is the image of a simple root
  index under the Weyl group.**
* `TauCeti.RootPairing.RootPositiveForm.rootLength_weylGroupToPerm`: root length is a Weyl-group
  invariant, with `TauCeti.RootPairing.RootPositiveForm.rootLength_reflectionPerm` the special case
  of a single reflection.
* `TauCeti.RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq`: **every root has the
  length of some simple root.** This is what turns a statement about the two entries of a rank-two
  Cartan matrix into a statement about all the roots.

## References

This file shows that the simple-root Weyl orbits cover all roots, as part of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, Ch. VI §1.5, and Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §10.3, where the same statement is proved by the same induction.
-/

public section

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **Every root is Weyl-conjugate to a simple root.** Stated on root indices: for a base `b`, each
index `j` satisfies `P.weylGroupToPerm w i = j` for some `i` in the support of `b` and some
Weyl-group element `w`.

The Weyl-group element is far from unique — the stabilizer of a simple root index is generally
nontrivial — so this is an existence statement and not a parametrization of the roots by
`b.support × P.weylGroup`. -/
theorem exists_mem_support_weylGroupToPerm_eq [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) (j : ι) :
    ∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = j := by
  -- One reflection more: prefix the Weyl-group element by the reflection in `k`, which lies in the
  -- Weyl group whether or not `k` is simple.
  have step : ∀ k x : ι, (∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = x) →
      ∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = P.reflectionPerm k x := by
    rintro k x ⟨i, hi, w, rfl⟩
    exact ⟨i, hi, _root_.RootPairing.weylGroup.ofIdx P k * w,
      TauCeti.RootPairing.weylGroupToPerm_ofIdx_mul_apply P w k i⟩
  exact b.induction_reflect j (fun k hk ↦ step k k hk) (fun i hi ↦ ⟨i, hi, 1, by simp⟩)
    fun x k hx _ ↦ step k x hx

namespace RootPairing.RootPositiveForm

variable {S : Type*} [CommRing S] [LinearOrder S] [Algebra S R]
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]

/-- **Root length is a Weyl-group invariant.** A root-positive form is invariant under the Weyl
group by construction, and the Weyl group carries the root indexed by `i` to the root indexed by
`P.weylGroupToPerm w i`. -/
-- Not a `simp` lemma: `simp` unfolds `P.weylGroupToPerm w i` to `(↑↑w).indexEquiv i` through
-- `MonoidHom.domRestrict_apply` and `RootPairing.Equiv.indexHom_apply`, so this left-hand side is
-- never in normal form. The `reflectionPerm` form below is the usable `simp` lemma.
theorem rootLength_weylGroupToPerm (B : P.RootPositiveForm S) (w : P.weylGroup) (i : ι) :
    B.rootLength (P.weylGroupToPerm w i) = B.rootLength i := by
  apply FaithfulSMul.algebraMap_injective S R
  rw [B.algebraMap_rootLength, B.algebraMap_rootLength, ← P.weylGroup_apply_root w i]
  exact _root_.RootPairing.InvariantForm.apply_weylGroup_smul P (B := B.toInvariantForm) w _ _

/-- Reflection in any root preserves root lengths. Mathlib's
`RootPairing.RootPositiveForm.rootLength_reflectionPerm_self` is the case `i = j`. -/
@[simp]
theorem rootLength_reflectionPerm (B : P.RootPositiveForm S) (i j : ι) :
    B.rootLength (P.reflectionPerm i j) = B.rootLength j := by
  rw [← TauCeti.RootPairing.weylGroupToPerm_ofIdx_apply P i j]
  exact rootLength_weylGroupToPerm B _ j

/-- **Every root has the length of one of the simple roots.** Consequently the set of root lengths
of a root pairing is read off its base, which is what lets a rank-two Cartan matrix control the
lengths of all the roots and not only of the two simple ones. -/
theorem exists_mem_support_rootLength_eq [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (B : P.RootPositiveForm S) (b : P.Base) (j : ι) :
    ∃ i ∈ b.support, B.rootLength j = B.rootLength i := by
  obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
  exact ⟨i, hi, rootLength_weylGroupToPerm B w i⟩

end RootPairing.RootPositiveForm

end TauCeti
