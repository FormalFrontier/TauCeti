/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius

/-!
# Uniqueness of Frobenius elements for faithful actions

This file adds the group-level uniqueness consequence of Mathlib's algebra-homomorphism
Frobenius theorem.  It is stated for a faithful monoid action on a commutative ring, so it can be
used independently of any number-field or Legendre-symbol specialization.
-/

public section

open nonZeroDivisors

namespace TauCeti

/-- Suppose `S` is Noetherian and `Q` is a prime of `S` containing all zero-divisors. If the
action of `G` on `S` is faithful and the extension is unramified at `Q`, then a Frobenius element
of `G` at `Q` is unique. -/
theorem _root_.IsArithFrobAt.eq_of_isUnramifiedAt
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Monoid G]
    [MulSemiringAction G S] [SMulCommClass G R S] [FaithfulSMul G S]
    {Q : Ideal S} [Q.IsPrime] (hQ : Q.primeCompl ≤ S⁰)
    [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S]
    {σ τ : G} (hσ : _root_.IsArithFrobAt R σ Q) (hτ : _root_.IsArithFrobAt R τ Q) : σ = τ := by
  apply MulSemiringAction.toAlgHom_injective R S
  exact AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ hτ hQ

end TauCeti
