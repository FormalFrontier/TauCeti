/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.EquivInvariance

/-!
# Permutation actions of Weyl groups

This file proves that the action of the automorphism group of a root system on its root indices is
faithful.  Consequently, every subgroup of that automorphism group, and in particular the Weyl
group, is finite when the root index type is finite.  It also records how that action evaluates on
simple reflections, how it interacts with root negation, and the sign change a reflection induces
on its own coroot functional.  Alongside it, the weight-space action of the Weyl group is faithful,
with no spanning hypothesis needed.  More generally, an automorphism transports coroot functionals
along its action on weights, matching the coroot functional of a root with that of its image.

## Main results

* `TauCeti.RootPairing.Equiv.indexHom_injective` says that an automorphism of a root system is
  determined by its permutation of the roots.
* `TauCeti.RootPairing.coroot'_reflection_self` says a reflection reverses the sign of its own
  coroot functional.
* `TauCeti.RootPairing.coroot'_smul` and `TauCeti.RootPairing.coroot'_weylGroupToPerm_smul` say an
  automorphism, and in particular a Weyl-group element, carries the coroot functional of a root to
  the coroot functional of its image.
* `TauCeti.RootPairing.weylGroupToPerm_ofIdx_apply` evaluates the action of a simple reflection.
* `TauCeti.RootPairing.weylGroupToPerm_neg` says the action commutes with root negation.
* `TauCeti.RootPairing.weylGroup.ofIdx_mul_self` says a simple reflection is an involution.
* `TauCeti.RootPairing.weylGroup.ofIdx_ne_one` says a simple reflection is not the identity over a
  ring of characteristic zero.
* `TauCeti.RootPairing.weylGroup.eq_one_of_smul_eq_self` says a Weyl-group element acting trivially
  on the weight space is the identity.
* `TauCeti.RootPairing.weylGroup.ext` says two Weyl-group elements agreeing on the weight space are
  equal.
* `TauCeti.RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj` says that conjugating a simple
  reflection by a Weyl-group element gives the reflection in the image root index.
* `TauCeti.RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal` says orthogonal roots have
  commuting reflections.
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

/-- An automorphism of a root pairing transports coroot functionals along its action on weights. -/
@[grind =]
lemma coroot'_smul (g : P.Aut) (i : ι) (x : M) :
    P.coroot' i (g • x) = P.coroot' (g.indexEquiv.symm i) x := by
  -- This is the transpose condition packaged in `RootPairing.Hom.weight_coweight_transpose`.
  have h := congrFun (congrArg DFunLike.coe
    (_root_.RootPairing.Hom.weight_coweight_transpose_apply P P (P.coroot i) g.toHom)) x
  simp only [LinearMap.dualMap_apply, _root_.RootPairing.Hom.coroot_coweightMap_apply] at h
  exact h

/-- **A Weyl-group element matches the coroot functional of a root with the coroot functional of
its image.** -/
@[grind =]
lemma coroot'_weylGroupToPerm_smul (w : P.weylGroup) (i : ι) (x : M) :
    P.coroot' (P.weylGroupToPerm w i) (w • x) = P.coroot' i x := by
  have h := coroot'_smul P (w : P.Aut) ((w : P.Aut).indexEquiv i) x
  rw [_root_.Equiv.symm_apply_apply] at h
  exact h

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

/-- Left multiplication by a simple reflection acts by reflecting the resulting root index. -/
lemma weylGroupToPerm_ofIdx_mul_apply (w : P.weylGroup) (i j : ι) :
    P.weylGroupToPerm (_root_.RootPairing.weylGroup.ofIdx P i * w) j =
      P.reflectionPerm i (P.weylGroupToPerm w j) := by
  rw [map_mul]
  exact weylGroupToPerm_ofIdx_apply P i (P.weylGroupToPerm w j)

/-- The Weyl-group action on root indices commutes with root negation. -/
lemma weylGroupToPerm_neg (w : P.weylGroup) (j : ι) :
    letI := P.indexNeg
    P.weylGroupToPerm w (-j) = -(P.weylGroupToPerm w j) :=
  by simp [RootPairing.indexNeg_neg]

namespace weylGroup

/-- A simple reflection of the Weyl group is the corresponding reflection of the root pairing. -/
@[simp]
lemma coe_ofIdx (i : ι) :
    ((_root_.RootPairing.weylGroup.ofIdx P i : P.weylGroup) : P.Aut) =
      _root_.RootPairing.Equiv.reflection P i :=
  rfl

/-- A simple reflection of the Weyl group is its own inverse. -/
@[simp]
lemma ofIdx_inv_eq (i : ι) :
    (_root_.RootPairing.weylGroup.ofIdx P i)⁻¹ = _root_.RootPairing.weylGroup.ofIdx P i :=
  Subtype.ext (_root_.RootPairing.Equiv.reflection_inv P i)

/-- A simple reflection of the Weyl group is an involution. -/
@[simp]
lemma ofIdx_mul_self (i : ι) :
    _root_.RootPairing.weylGroup.ofIdx P i * _root_.RootPairing.weylGroup.ofIdx P i = 1 := by
  rw [mul_eq_one_iff_eq_inv, ofIdx_inv_eq]

/-- **A simple reflection is not the identity** over a ring of characteristic zero. -/
theorem ofIdx_ne_one [CharZero R] (i : ι) :
    _root_.RootPairing.weylGroup.ofIdx P i ≠ 1 := by
  intro h
  have hi := congrArg (fun w : P.weylGroup => P.coroot' i (w • P.root i)) h
  simp only [one_smul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same] at hi
  norm_num at hi

variable {P} in
/-- A Weyl-group element acting trivially on the weight space is the identity: the weight-space
representation of the automorphism group of a root pairing is faithful. -/
theorem eq_one_of_smul_eq_self {w : P.weylGroup} (h : ∀ x : M, w • x = x) : w = 1 := by
  have hw : (w : P.Aut) = 1 := by
    refine _root_.RootPairing.Equiv.weightHom_injective P ?_
    rw [map_one]
    exact LinearEquiv.ext fun x ↦ h x
  exact Subtype.ext (by simpa using hw)

variable {P} in
/-- Two Weyl-group elements agreeing on the weight space are equal. -/
@[ext]
theorem ext {v w : P.weylGroup} (h : ∀ x : M, v • x = w • x) : v = w := by
  rw [← mul_inv_eq_one]
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  rw [mul_smul, h, smul_inv_smul]

/-- **Conjugating a simple reflection transports it along the permutation action**: the reflection
in the image of a root index is the conjugate of the reflection in that root index. -/
theorem ofIdx_weylGroupToPerm_eq_conj (w : P.weylGroup) (i : ι) :
    _root_.RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm w i) =
      w * _root_.RootPairing.weylGroup.ofIdx P i * w⁻¹ := by
  refine ext fun x ↦ ?_
  -- Both sides send `x` to `x - ⟨x, αᵢ^∨⟩ • w αᵢ`, the right-hand side after undoing `w`.
  have hcoroot : P.coroot' i (w⁻¹ • x) = P.coroot' (P.weylGroupToPerm w i) x := by
    conv_rhs => rw [← smul_inv_smul w x]
    exact (coroot'_weylGroupToPerm_smul P w i (w⁻¹ • x)).symm
  have hroot : w • P.root i = P.root (P.weylGroupToPerm w i) := P.weylGroup_apply_root w i
  calc
    _root_.RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm w i) • x
        = x - P.coroot' (P.weylGroupToPerm w i) x • P.root (P.weylGroupToPerm w i) := by
      simp [_root_.RootPairing.reflection_apply]
    _ = w • (w⁻¹ • x - P.coroot' i (w⁻¹ • x) • P.root i) := by
      rw [smul_sub, smul_inv_smul, smul_comm, hroot, hcoroot]
    _ = (w * _root_.RootPairing.weylGroup.ofIdx P i * w⁻¹) • x := by
      simp [mul_smul, _root_.RootPairing.reflection_apply]

/-- **Orthogonal roots have commuting reflections** in the Weyl group. -/
theorem commute_ofIdx_of_isOrthogonal {i j : ι} (h : P.IsOrthogonal i j) :
    Commute (_root_.RootPairing.weylGroup.ofIdx P i) (_root_.RootPairing.weylGroup.ofIdx P j) := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  apply _root_.RootPairing.Equiv.weightHom_injective P
  simpa only [coe_ofIdx, map_mul, _root_.RootPairing.Equiv.weightHom_apply,
    _root_.RootPairing.Equiv.reflection_weightEquiv] using
    (_root_.RootPairing.isOrthogonal_comm P i j h).eq

end weylGroup

variable [Finite ι]

/-- If the roots span, every subgroup of the automorphism group is finite when the root index type
is finite. -/
theorem finite_subgroup_aut_of_span_eq_top (hspan : Submodule.span R (range P.root) = ⊤)
    (G : Subgroup P.Aut) : Finite G :=
  Finite.of_injective ((_root_.RootPairing.Equiv.indexHom P).domRestrict G)
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
      ((_root_.RootPairing.Equiv.indexHom P).domRestrict G)
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
