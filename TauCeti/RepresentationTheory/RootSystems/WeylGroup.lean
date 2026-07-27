/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# Faithful permutation actions of Weyl groups

This file proves that the action of the automorphism group of a root system on its root indices is
faithful.  Consequently, every subgroup of that automorphism group, and in particular the Weyl
group, is finite when the root index type is finite.

## Main results

* `TauCeti.RootPairing.Equiv.indexHom_injective` says that an automorphism of a root system is
  determined by its permutation of the roots.
* `TauCeti.finite_subgroup_aut` proves that every subgroup of the automorphism group of a finite
  root system is finite.
* `TauCeti.finite_weylGroup` is the resulting finiteness theorem for the Weyl group.

## References

* [Root systems roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/RootSystems/README.md)
-/

public section

open Function Set

namespace TauCeti

variable {ι R M N : Type*}

section RootSystem

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

namespace RootPairing.Equiv

/-- If the roots span, an automorphism of a root pairing is determined by its permutation of the
root indices. -/
theorem indexHom_injective_of_span_eq_top (hspan : Submodule.span R (range P.root) = ⊤) :
    Function.Injective (_root_.RootPairing.Equiv.indexHom P) := by
  intro f g hfg
  apply _root_.RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on_range hspan fun i ↦ ?_
  have hfg' : f.indexEquiv i = g.indexEquiv i :=
    congrFun (congrArg DFunLike.coe hfg) i
  calc
    _ = f • P.root i := rfl
    _ = P.root (f.indexEquiv i) := (_root_.RootPairing.Equiv.root_indexEquiv_eq_smul P i f).symm
    _ = P.root (g.indexEquiv i) := congrArg P.root hfg'
    _ = g • P.root i := _root_.RootPairing.Equiv.root_indexEquiv_eq_smul P i g
    _ = _ := rfl

/-- An automorphism of a root system is determined by its permutation of the root indices. -/
theorem indexHom_injective [P.IsRootSystem] :
    Function.Injective (_root_.RootPairing.Equiv.indexHom P) :=
  indexHom_injective_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P))

end RootPairing.Equiv

/-- If the roots span, the action of the Weyl group on root indices is faithful. -/
theorem weylGroupToPerm_injective_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) :
    Function.Injective P.weylGroupToPerm :=
  (RootPairing.Equiv.indexHom_injective_of_span_eq_top P hspan).comp Subtype.val_injective

/-- The action of the Weyl group on root indices is faithful. -/
theorem weylGroupToPerm_injective [P.IsRootSystem] : Function.Injective P.weylGroupToPerm :=
  (RootPairing.Equiv.indexHom_injective P).comp Subtype.val_injective

variable [Finite ι]

/-- If the roots span, every subgroup of the automorphism group is finite when the root index type
is finite. -/
theorem finite_subgroup_aut_of_span_eq_top (hspan : Submodule.span R (range P.root) = ⊤)
    (G : Subgroup P.Aut) : Finite G :=
  Finite.of_injective ((_root_.RootPairing.Equiv.indexHom P).restrict G)
    ((RootPairing.Equiv.indexHom_injective_of_span_eq_top P hspan).comp Subtype.val_injective)

/-- Every subgroup of the automorphism group of a finite root system is finite. -/
theorem finite_subgroup_aut [P.IsRootSystem] (G : Subgroup P.Aut) : Finite G :=
  finite_subgroup_aut_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P)) G

/-- If the roots span, the automorphism group is finite when the root index type is finite. -/
theorem finite_rootPairing_aut_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) : Finite P.Aut :=
  Finite.of_injective (_root_.RootPairing.Equiv.indexHom P)
    (RootPairing.Equiv.indexHom_injective_of_span_eq_top P hspan)

/-- The automorphism group of a finite root system is finite. -/
theorem finite_rootSystem_aut [P.IsRootSystem] : Finite P.Aut :=
  finite_rootPairing_aut_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P))

/-- If the roots span, every subgroup of the automorphism group has order at most the factorial of
the number of roots. -/
theorem card_subgroup_aut_le_factorial_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤)
    (G : Subgroup P.Aut) : Nat.card G ≤ Nat.factorial (Nat.card ι) := by
  calc
    Nat.card G ≤ Nat.card (ι ≃ ι) := Nat.card_le_card_of_injective
      ((_root_.RootPairing.Equiv.indexHom P).restrict G)
        ((RootPairing.Equiv.indexHom_injective_of_span_eq_top P hspan).comp
          Subtype.val_injective)
    _ = Nat.factorial (Nat.card ι) := Nat.card_perm

/-- Every subgroup of the automorphism group of a finite root system has order at most the
factorial of the number of roots. -/
theorem card_subgroup_aut_le_factorial [P.IsRootSystem] (G : Subgroup P.Aut) :
    Nat.card G ≤ Nat.factorial (Nat.card ι) :=
  card_subgroup_aut_le_factorial_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P)) G

/-- If the roots span, the automorphism group has order at most the factorial of the number of
roots. -/
theorem card_rootPairing_aut_le_factorial_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) :
    Nat.card P.Aut ≤ Nat.factorial (Nat.card ι) :=
  calc
    Nat.card P.Aut ≤ Nat.card (ι ≃ ι) := Nat.card_le_card_of_injective
      (_root_.RootPairing.Equiv.indexHom P)
        (RootPairing.Equiv.indexHom_injective_of_span_eq_top P hspan)
    _ = Nat.factorial (Nat.card ι) := Nat.card_perm

/-- The automorphism group of a finite root system has order at most the factorial of the number
of roots. -/
theorem card_rootSystem_aut_le_factorial [P.IsRootSystem] :
    Nat.card P.Aut ≤ Nat.factorial (Nat.card ι) :=
  card_rootPairing_aut_le_factorial_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P))

/-- If the roots span, the Weyl group is finite when the root index type is finite. -/
theorem finite_weylGroup_of_span_eq_top (hspan : Submodule.span R (range P.root) = ⊤) :
    Finite P.weylGroup :=
  finite_subgroup_aut_of_span_eq_top P hspan P.weylGroup

/-- The Weyl group of a finite root system is finite. -/
theorem finite_weylGroup [P.IsRootSystem] : Finite P.weylGroup :=
  finite_subgroup_aut P P.weylGroup

/-- If the roots span, the order of the Weyl group is at most the factorial of the number of
roots. -/
theorem card_weylGroup_le_factorial_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) :
    Nat.card P.weylGroup ≤ Nat.factorial (Nat.card ι) :=
  card_subgroup_aut_le_factorial_of_span_eq_top P hspan P.weylGroup

/-- The order of a finite Weyl group is at most the factorial of the number of roots. -/
theorem card_weylGroup_le_factorial [P.IsRootSystem] :
    Nat.card P.weylGroup ≤ Nat.factorial (Nat.card ι) :=
  card_subgroup_aut_le_factorial P P.weylGroup

end RootSystem

end TauCeti
