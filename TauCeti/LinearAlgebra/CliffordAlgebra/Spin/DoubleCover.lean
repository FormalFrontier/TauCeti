/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Surjectivity
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# The Spin double cover as a group extension

For a positive-dimensional finite nondegenerate quadratic space over a field in which `2` is
invertible, the kernel equivalence from `Spin.Kernel` and any proof that the action is surjective
package the Spin double cover as a `GroupExtension`; in particular, the action is surjective over a
separably closed field.

## Main definitions and results

* `CliffordAlgebra.spinDoubleCoverOfSurjective` packages any surjective Spin action as a
  group extension.
* `CliffordAlgebra.spinDoubleCover` packages
  `1 → ZMod 2 → Spin(Q) → SO(Q) → 1` as a group extension.
* `CliffordAlgebra.spinDoubleCoverOfSurjective_inl_ofAdd_one` and
  `CliffordAlgebra.spinDoubleCoverOfSurjective_rightHom` characterize the generic
  extension.
* `CliffordAlgebra.spinDoubleCover_inl_ofAdd_one` and
  `CliffordAlgebra.spinDoubleCover_rightHom` characterize the separably closed case.

## References

This supplies the Spin short exact sequence of Layer 2 over a separably closed field; the Pin/O(V)
sequence and the general-field spinor-norm version are not covered. See
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- A surjective Spin action on a positive-dimensional nondegenerate quadratic space over a field
in which `2` is invertible is the group extension `1 → ZMod 2 → Spin(Q) → SO(Q) → 1`. -/
noncomputable def spinDoubleCoverOfSurjective
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (QuadraticMap.specialOrthogonalGroup Q) :=
  GroupExtension.ofMulEquivKer hsurj
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ)

/-- The inclusion in a Spin double cover built from a surjectivity proof sends the generator to
the scalar `-1`. -/
@[simp]
theorem spinDoubleCoverOfSurjective_inl_ofAdd_one
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    (spinDoubleCoverOfSurjective Q hQ hsurj).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q hQ.ne_zero := by
  rw [spinDoubleCoverOfSurjective, GroupExtension.ofMulEquivKer_inl,
    MonoidHom.comp_apply]
  exact congrArg Subtype.val
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one Q hQ)

/-- The projection in a Spin double cover built from a surjectivity proof is the Spin action. -/
@[simp]
theorem spinDoubleCoverOfSurjective_rightHom
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    (spinDoubleCoverOfSurjective Q hQ hsurj).rightHom = spinToSpecialOrthogonal Q :=
  GroupExtension.ofMulEquivKer_rightHom _ _

/-- For a positive-dimensional nondegenerate quadratic space over a separably closed field in
which `2` is invertible, the Spin action is the group extension
`1 → ZMod 2 → Spin(Q) → SO(Q) → 1`. -/
noncomputable def spinDoubleCover [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (QuadraticMap.specialOrthogonalGroup Q) :=
  spinDoubleCoverOfSurjective Q hQ (spinToSpecialOrthogonal_surjective Q hQ)

/-- The separably closed Spin double cover is the generic construction applied to canonical
surjectivity. -/
theorem spinDoubleCover_def [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinDoubleCover Q hQ =
      spinDoubleCoverOfSurjective Q hQ (spinToSpecialOrthogonal_surjective Q hQ) :=
  (rfl)

/-- The inclusion in the separably closed Spin double cover sends the generator to the scalar
`-1`. -/
@[simp]
theorem spinDoubleCover_inl_ofAdd_one [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover Q hQ).inl (Multiplicative.ofAdd 1) = spinGroup.negOne Q hQ.ne_zero := by
  rw [spinDoubleCover_def, spinDoubleCoverOfSurjective_inl_ofAdd_one]

/-- The projection in the separably closed Spin double cover is the Spin action. -/
@[simp]
theorem spinDoubleCover_rightHom [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover Q hQ).rightHom = spinToSpecialOrthogonal Q := by
  rw [spinDoubleCover_def, spinDoubleCoverOfSurjective_rightHom]

end CliffordAlgebra
