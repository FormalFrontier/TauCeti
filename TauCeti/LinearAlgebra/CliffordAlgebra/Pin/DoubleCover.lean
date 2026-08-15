/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.GroupExtension.Of.Surjective
public import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Kernel

/-!
# The Pin double cover as a group extension

For a positive-dimensional finite nondegenerate quadratic space over a field in which `2` is
invertible, the kernel equivalence from `Pin.Kernel` and any proof that the action is surjective
package the Pin double cover as a `GroupExtension`; in particular, the action is surjective over a
separably closed field.

## Main definitions and results

* `TauCeti.CliffordAlgebra.pinDoubleCoverOfSurjective` packages any surjective Pin action as a
  group extension.
* `TauCeti.CliffordAlgebra.pinDoubleCover` packages
  `1 → ZMod 2 → Pin(Q) → O(Q) → 1` as a group extension.
* `TauCeti.CliffordAlgebra.pinDoubleCoverOfSurjective_inl_ofAdd_one` and
  `TauCeti.CliffordAlgebra.pinDoubleCoverOfSurjective_rightHom` characterize the generic
  extension.
* `TauCeti.CliffordAlgebra.pinDoubleCover_inl_ofAdd_one` and
  `TauCeti.CliffordAlgebra.pinDoubleCover_rightHom` characterize the separably closed case.

## References

This supplies the Pin short exact sequence of Layer 2 over a separably closed field. See
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2. The API and proof structure are adapted
from `TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DoubleCover`.
-/

public section

open CliffordAlgebra

namespace TauCeti.CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- A surjective Pin action on a positive-dimensional nondegenerate quadratic space over a field
in which `2` is invertible is the group extension `1 → ZMod 2 → Pin(Q) → O(Q) → 1`. -/
noncomputable def pinDoubleCoverOfSurjective
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (pinToOrthogonal Q)) :
    GroupExtension (Multiplicative (ZMod 2)) (pinGroup Q)
      (QuadraticMap.orthogonalGroup Q) :=
  GroupExtension.ofMulEquivKer hsurj (zmodTwoMulEquivKerPinToOrthogonal Q hQ)

/-- The inclusion in a Pin double cover built from a surjectivity proof sends the generator to
the scalar `-1`. -/
@[simp]
theorem pinDoubleCoverOfSurjective_inl_ofAdd_one
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (pinToOrthogonal Q)) :
    (pinDoubleCoverOfSurjective Q hQ hsurj).inl (Multiplicative.ofAdd 1) =
      spinToPin Q (spinGroup.negOne Q hQ.ne_zero) := by
  rw [pinDoubleCoverOfSurjective, GroupExtension.ofMulEquivKer_inl,
    MonoidHom.comp_apply]
  exact congrArg Subtype.val (zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one Q hQ)

/-- The projection in a Pin double cover built from a surjectivity proof is the Pin action. -/
@[simp]
theorem pinDoubleCoverOfSurjective_rightHom
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (pinToOrthogonal Q)) :
    (pinDoubleCoverOfSurjective Q hQ hsurj).rightHom = pinToOrthogonal Q :=
  GroupExtension.ofMulEquivKer_rightHom _ _

/-- For a positive-dimensional nondegenerate quadratic space over a separably closed field in
which `2` is invertible, the Pin action is the group extension
`1 → ZMod 2 → Pin(Q) → O(Q) → 1`. -/
noncomputable def pinDoubleCover [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (pinGroup Q)
      (QuadraticMap.orthogonalGroup Q) :=
  pinDoubleCoverOfSurjective Q hQ (pinToOrthogonal_surjective Q hQ)

/-- The separably closed Pin double cover is the generic construction applied to canonical
surjectivity. -/
theorem pinDoubleCover_def [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    pinDoubleCover Q hQ =
      pinDoubleCoverOfSurjective Q hQ (pinToOrthogonal_surjective Q hQ) :=
  (rfl)

/-- The inclusion in the separably closed Pin double cover sends the generator to the scalar
`-1`. -/
@[simp]
theorem pinDoubleCover_inl_ofAdd_one [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (pinDoubleCover Q hQ).inl (Multiplicative.ofAdd 1) =
      spinToPin Q (spinGroup.negOne Q hQ.ne_zero) := by
  rw [pinDoubleCover_def, pinDoubleCoverOfSurjective_inl_ofAdd_one]

/-- The projection in the separably closed Pin double cover is the Pin action. -/
@[simp]
theorem pinDoubleCover_rightHom [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (pinDoubleCover Q hQ).rightHom = pinToOrthogonal Q := by
  rw [pinDoubleCover_def, pinDoubleCoverOfSurjective_rightHom]

end TauCeti.CliffordAlgebra
