/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Dedekind-domain ramification and inertia counting compatibility

This file preserves the old Dedekind-domain name for the generalized ramification/inertia
counting criterion.

## Main results

* `TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`:
  a deprecated compatibility wrapper for the old Dedekind-domain signature.
-/

public section

open Ideal Module

namespace TauCeti.DedekindDomain

/-- Deprecated compatibility wrapper for the old Dedekind-domain signature of
`TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`. -/
@[deprecated TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup
  (since := "2026-06-19")]
theorem ncard_primesOver_eq_natCard_iff_of_isGaloisGroup {A B : Type*} [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [IsTorsionFree A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsMaximal] (_hP : P ≠ ⊥) :
    (primesOver P B).ncard = Nat.card G ↔
      P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 :=
  TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup G P

end TauCeti.DedekindDomain
