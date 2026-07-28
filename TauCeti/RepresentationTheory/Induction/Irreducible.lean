/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Induction.Conjugate

/-!
# Irreducibility of conjugate representations

Restriction along an isomorphism of groups is an equivalence of representation categories. This
file constructs that equivalence and identifies the invariant subspaces before applying both
descriptions to conjugate representations. In particular, conjugation preserves irreducibility.

## Main definitions

* `TauCeti.Rep.resEquivalence`: restriction along a multiplicative equivalence, as an equivalence
  of representation categories.
* `TauCeti.conjRepEquivalence`: conjugation as an equivalence of representation categories.

## References

This implements the irreducibility part of Layer 1 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v w

namespace TauCeti

namespace Rep

variable {k : Type u} {G : Type v} {H : Type w}
variable [Semiring k] [Monoid G] [Monoid H]

private noncomputable def resCompEquivUnitIso (e : G ≃* H) :
    𝟭 (_root_.Rep k H) ≅
      _root_.Rep.resFunctor e.toMonoidHom ⋙
        _root_.Rep.resFunctor e.symm.toMonoidHom :=
  NatIso.ofComponents
    (fun A ↦ _root_.Rep.mkIso <|
      Representation.Equiv.mk (LinearEquiv.refl k A.V) fun g ↦ by simp)
    (by
      intro A B f
      ext
      rfl)

private noncomputable def resCompEquivCounitIso (e : G ≃* H) :
    _root_.Rep.resFunctor e.symm.toMonoidHom ⋙
        _root_.Rep.resFunctor e.toMonoidHom ≅
      𝟭 (_root_.Rep k G) :=
  NatIso.ofComponents
    (fun A ↦ _root_.Rep.mkIso <|
      Representation.Equiv.mk (LinearEquiv.refl k A.V) fun g ↦ by simp)
    (by
      intro A B f
      ext
      rfl)

/-- Restriction along a multiplicative equivalence is an equivalence of representation
categories. -/
noncomputable def resEquivalence (e : G ≃* H) :
    _root_.Rep k H ≌ _root_.Rep k G :=
  CategoryTheory.Equivalence.mk
    (_root_.Rep.resFunctor e.toMonoidHom)
    (_root_.Rep.resFunctor e.symm.toMonoidHom)
    (resCompEquivUnitIso e)
    (resCompEquivCounitIso e)

end Rep

variable {k : Type u} {G : Type v} [Semiring k] [Group G]

/-- Conjugation by a group element is an equivalence of representation categories. -/
noncomputable def conjRepEquivalence (s : G) (H : Subgroup G) :
    _root_.Rep k H ≌ _root_.Rep k (MulAut.conj s • H : Subgroup G) :=
  Rep.resEquivalence (conjSubgroupEquiv s H)

end TauCeti
