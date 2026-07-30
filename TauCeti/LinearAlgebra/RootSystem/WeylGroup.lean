/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# Permutation actions of Weyl groups

This file proves that the action of the automorphism group of a root system on its root indices is
faithful.  Consequently, every subgroup of that automorphism group, and in particular the Weyl
group, is finite when the root index type is finite.  It also records how that action evaluates on
simple reflections, how it interacts with root negation, the conjugation and involution identities
satisfied by the reflections themselves, and the sign change a reflection induces on its own coroot
functional.

## Main results

* `TauCeti.RootPairing.Equiv.indexHom_injective` says that an automorphism of a root system is
  determined by its permutation of the roots.
* `TauCeti.RootPairing.coroot'_reflection_self` says a reflection reverses the sign of its own
  coroot functional.
* `TauCeti.RootPairing.weylGroupToPerm_ofIdx_apply` evaluates the action of a simple reflection.
* `TauCeti.RootPairing.ofIdx_reflectionPerm` and `TauCeti.RootPairing.ofIdx_inv` record the
  conjugation and involution identities for reflections, viewed in the Weyl group.
* `TauCeti.RootPairing.ofIdx_weylGroupToPerm` conjugates a root reflection into the reflection in
  the image root.
* `TauCeti.RootPairing.weylGroupToPerm_neg` says the action commutes with root negation.
* `TauCeti.RootPairing.finite_subgroup_aut` proves that every subgroup of the automorphism group of
  a finite root system is finite.
* `TauCeti.RootPairing.finite_weylGroup` is the resulting finiteness theorem for the Weyl group.

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
  simp only [_root_.RootPairing.Equiv.weightHom_apply, LinearEquiv.coe_coe,
    _root_.RootPairing.Equiv.weightEquiv_apply,
    _root_.RootPairing.Hom.root_weightMap_apply, hfg']

/-- An automorphism of a root system is determined by its permutation of the root indices. -/
theorem indexHom_injective [P.IsRootSystem] :
    Function.Injective (_root_.RootPairing.Equiv.indexHom P) :=
  indexHom_injective_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P))

end RootPairing.Equiv

namespace RootPairing

/-- Reflecting a root in itself negates its coroot functional. -/
@[simp]
lemma coroot'_reflectionPerm_self (i : ι) : P.coroot' (P.reflectionPerm i i) = -P.coroot' i := by
  rw [_root_.RootPairing.coroot', P.coroot_reflectionPerm, P.coreflection_apply_self]
  simp

/-- A reflection reverses the sign of its own coroot functional. -/
@[grind =]
lemma coroot'_reflection_self (i : ι) (x : M) :
    P.coroot' i (P.reflection i x) = -P.coroot' i x := by
  rw [P.coroot'_reflection, coroot'_reflectionPerm_self]
  simp

/-- If the roots span, the action of the Weyl group on root indices is faithful. -/
theorem weylGroupToPerm_injective_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) :
    Function.Injective P.weylGroupToPerm :=
  (Equiv.indexHom_injective_of_span_eq_top P hspan).comp Subtype.val_injective

/-- The action of the Weyl group on root indices is faithful. -/
theorem weylGroupToPerm_injective [P.IsRootSystem] : Function.Injective P.weylGroupToPerm :=
  (Equiv.indexHom_injective P).comp Subtype.val_injective

/-- The Weyl-group permutation of a simple reflection is the corresponding root-index
reflection. -/
lemma weylGroupToPerm_ofIdx_apply (i j : ι) :
    P.weylGroupToPerm (_root_.RootPairing.weylGroup.ofIdx P i) j =
      P.reflectionPerm i j := by
  -- Mathlib exposes the underlying reflection equivalence, but not its restriction to the
  -- Weyl group. Unfolding just those two wrappers connects the APIs.
  change (_root_.RootPairing.Equiv.reflection P i).indexEquiv j = P.reflectionPerm i j
  exact congrArg (fun e : ι ≃ ι => e j)
    (_root_.RootPairing.Equiv.reflection_indexEquiv P i)

/-- Right multiplication by a simple reflection acts by first reflecting the root index. -/
lemma weylGroupToPerm_mul_ofIdx_apply (w : P.weylGroup) (i j : ι) :
    P.weylGroupToPerm (w * _root_.RootPairing.weylGroup.ofIdx P i) j =
      P.weylGroupToPerm w (P.reflectionPerm i j) := by
  rw [map_mul]
  exact congrArg (P.weylGroupToPerm w) (weylGroupToPerm_ofIdx_apply P i j)

/-- Reflecting the root `αᵢ` in the root `αⱼ` conjugates the reflection in `αᵢ` by the reflection
in `αⱼ`. This is `RootPairing.reflection_reflectionPerm` transported to the Weyl group. -/
lemma ofIdx_reflectionPerm (i j : ι) :
    _root_.RootPairing.weylGroup.ofIdx P (P.reflectionPerm j i) =
      _root_.RootPairing.weylGroup.ofIdx P j * _root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j := by
  apply Subtype.ext
  have hreflection :
      _root_.RootPairing.Equiv.reflection P (P.reflectionPerm j i) =
        _root_.RootPairing.Equiv.reflection P j * _root_.RootPairing.Equiv.reflection P i *
          _root_.RootPairing.Equiv.reflection P j := by
    apply _root_.RootPairing.Equiv.weightHom_injective P
    simpa only [map_mul, _root_.RootPairing.Equiv.weightHom_apply,
      _root_.RootPairing.Equiv.reflection_weightEquiv] using
      P.reflection_reflectionPerm
  exact hreflection

/-- A root reflection is its own inverse. -/
@[simp]
lemma ofIdx_inv (i : ι) :
    (_root_.RootPairing.weylGroup.ofIdx P i)⁻¹ = _root_.RootPairing.weylGroup.ofIdx P i := by
  apply Subtype.ext
  exact _root_.RootPairing.Equiv.reflection_inv P i

/-- Conjugating the reflection in `αᵢ` by a Weyl-group element `w` gives the reflection in the root
that `w` sends `αᵢ` to. This is the group-level form of the invariance of the root system under the
Weyl group, and it is what lets a leading letter of a word be cancelled in the exchange
condition. -/
theorem ofIdx_weylGroupToPerm (w : P.weylGroup) (i : ι) :
    _root_.RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm w i) =
      w * _root_.RootPairing.weylGroup.ofIdx P i * w⁻¹ := by
  revert i
  obtain ⟨w, hw⟩ := w
  induction hw using _root_.RootPairing.weylGroup.induction with
  | mem j =>
    intro i
    -- `weylGroup.ofIdx` is the reflection automorphism packaged with its membership proof.
    have hj : (⟨_root_.RootPairing.Equiv.reflection P j,
        P.reflection_mem_weylGroup j⟩ : P.weylGroup) =
        _root_.RootPairing.weylGroup.ofIdx P j :=
      Subtype.ext rfl
    rw [hj, weylGroupToPerm_ofIdx_apply, ofIdx_inv, ofIdx_reflectionPerm]
  | one =>
    intro i
    have h1 : (⟨1, one_mem P.weylGroup⟩ : P.weylGroup) = 1 := Subtype.ext (by simp)
    rw [h1]
    simp
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    intro i
    have hmul : (⟨g₁ * g₂, mul_mem hg₁ hg₂⟩ : P.weylGroup) =
        (⟨g₁, hg₁⟩ : P.weylGroup) * ⟨g₂, hg₂⟩ := Subtype.ext (by simp)
    rw [hmul, map_mul, Equiv.Perm.mul_apply, ih₁, ih₂]
    group

/-- The Weyl-group action on root indices commutes with root negation. -/
lemma weylGroupToPerm_neg (w : P.weylGroup) (j : ι) :
    letI := P.indexNeg
    P.weylGroupToPerm w (-j) = -(P.weylGroupToPerm w j) := by
  letI := P.indexNeg
  apply P.root.injective
  calc
    P.root (P.weylGroupToPerm w (-j)) = w • P.root (-j) :=
      (P.weylGroup_apply_root w (-j)).symm
    _ = w • (-P.root j) := by
      rw [_root_.RootPairing.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self]
    _ = -(w • P.root j) := smul_neg _ _
    _ = -P.root (P.weylGroupToPerm w j) :=
      congrArg Neg.neg (P.weylGroup_apply_root w j)
    _ = P.root (-(P.weylGroupToPerm w j)) := by
      rw [_root_.RootPairing.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self]

variable [Finite ι]

/-- If the roots span, every subgroup of the automorphism group is finite when the root index type
is finite. -/
theorem finite_subgroup_aut_of_span_eq_top (hspan : Submodule.span R (range P.root) = ⊤)
    (G : Subgroup P.Aut) : Finite G :=
  Finite.of_injective ((_root_.RootPairing.Equiv.indexHom P).restrict G)
    ((Equiv.indexHom_injective_of_span_eq_top P hspan).comp Subtype.val_injective)

/-- Every subgroup of the automorphism group of a finite root system is finite. -/
theorem finite_subgroup_aut [P.IsRootSystem] (G : Subgroup P.Aut) : Finite G :=
  finite_subgroup_aut_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P)) G

/-- If the roots span, the automorphism group is finite when the root index type is finite. -/
theorem finite_aut_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) : Finite P.Aut :=
  Finite.of_injective (_root_.RootPairing.Equiv.indexHom P)
    (Equiv.indexHom_injective_of_span_eq_top P hspan)

/-- The automorphism group of a finite root system is finite. -/
theorem finite_aut [P.IsRootSystem] : Finite P.Aut :=
  finite_aut_of_span_eq_top P
    (_root_.RootPairing.IsRootSystem.span_root_eq_top (P := P))

/-- If the roots span, every subgroup of the automorphism group has order at most the factorial of
the number of roots. -/
theorem card_subgroup_aut_le_factorial_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤)
    (G : Subgroup P.Aut) : Nat.card G ≤ Nat.factorial (Nat.card ι) := by
  calc
    Nat.card G ≤ Nat.card (ι ≃ ι) := Nat.card_le_card_of_injective
      ((_root_.RootPairing.Equiv.indexHom P).restrict G)
        ((Equiv.indexHom_injective_of_span_eq_top P hspan).comp
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
theorem card_aut_le_factorial_of_span_eq_top
    (hspan : Submodule.span R (range P.root) = ⊤) :
    Nat.card P.Aut ≤ Nat.factorial (Nat.card ι) :=
  calc
    Nat.card P.Aut ≤ Nat.card (ι ≃ ι) := Nat.card_le_card_of_injective
      (_root_.RootPairing.Equiv.indexHom P)
        (Equiv.indexHom_injective_of_span_eq_top P hspan)
    _ = Nat.factorial (Nat.card ι) := Nat.card_perm

/-- The automorphism group of a finite root system has order at most the factorial of the number
of roots. -/
theorem card_aut_le_factorial [P.IsRootSystem] :
    Nat.card P.Aut ≤ Nat.factorial (Nat.card ι) :=
  card_aut_le_factorial_of_span_eq_top P
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

/-- The order of the Weyl group of a finite root system is at most the factorial of the number of
roots. -/
theorem card_weylGroup_le_factorial [P.IsRootSystem] :
    Nat.card P.weylGroup ≤ Nat.factorial (Nat.card ι) :=
  card_subgroup_aut_le_factorial P P.weylGroup

end RootPairing

end RootSystem

end TauCeti
