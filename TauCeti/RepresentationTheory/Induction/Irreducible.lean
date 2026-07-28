/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Induction.Conjugate
public import TauCeti.RepresentationTheory.Induction.Transitivity

/-!
# Irreducibility of conjugate representations

This file packages conjugation by a group element as an equivalence of representation categories,
using the generic restriction equivalence.

## Main definitions

* `TauCeti.conjRepEquivalence`: conjugation as an equivalence of representation categories.

## References

This implements the irreducibility part of Layer 1 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Semiring k] [Group G]

/-- Conjugation by a group element is an equivalence of representation categories. -/
noncomputable def conjRepEquivalence (s : G) (H : Subgroup G) :
    _root_.Rep k H ≌ _root_.Rep k (MulAut.conj s • H : Subgroup G) :=
  Rep.resEquivalence (conjSubgroupEquiv s H)

/-- The forward functor of the conjugation equivalence is restriction along conjugation. -/
@[simp]
theorem conjRepEquivalence_functor (s : G) (H : Subgroup G) :
    (conjRepEquivalence (k := k) s H).functor =
      _root_.Rep.resFunctor (conjSubgroupEquiv s H).toMonoidHom := by
  rw [conjRepEquivalence, Rep.resEquivalence_functor]

/-- The inverse functor of the conjugation equivalence restricts along inverse conjugation. -/
@[simp]
theorem conjRepEquivalence_inverse (s : G) (H : Subgroup G) :
    (conjRepEquivalence (k := k) s H).inverse =
      _root_.Rep.resFunctor (conjSubgroupEquiv s H).symm.toMonoidHom := by
  rw [conjRepEquivalence, Rep.resEquivalence_inverse]

end TauCeti
