/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal

/-!
# Surjectivity of the Spin action

The determinant-one Pin elements are even, so Pin surjectivity restricts to Spin surjectivity onto
the special orthogonal group.

## Main definitions and results

* `CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_pinToOrthogonal_surjective`
  restricts any surjective Pin action to a surjective Spin action on the special orthogonal group.
* `CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_isSquare` proves its
  surjectivity when every reflection normalization scalar is a square.
* `CliffordAlgebra.spinToSpecialOrthogonal_surjective` specializes this to a
  separably closed field.

## References

This advances Layer 2's double-cover target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

section Surjectivity

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] [Invertible (2 : R)]

/-- A surjective Pin action on a finite free module restricts to a surjective Spin action on the
special orthogonal group. -/
theorem spinToSpecialOrthogonal_surjective_of_pinToOrthogonal_surjective
    (Q : QuadraticForm R M) (hpin : Function.Surjective (pinToOrthogonal Q)) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  intro g
  have hg := QuadraticMap.mem_specialOrthogonalGroup_iff.1 g.2
  obtain ⟨p, hp⟩ := hpin ⟨g, hg.1⟩
  let s : spinGroup Q :=
    ⟨p, p.2, mem_even_of_det_pinToOrthogonal_eq_one Q p (by rw [hp]; exact hg.2)⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_spinToSpecialOrthogonal_apply, ← coe_spinToOrthogonal_apply,
    ← pinToOrthogonal_spinToPin]
  have hspinpin : spinToPin Q s = p := Subtype.ext (by rw [coe_spinToPin_apply])
  rw [hspinpin, hp]

section Field

variable {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]

/-- The Spin action surjects onto the special orthogonal group when every reflection
normalization scalar is a square. -/
theorem spinToSpecialOrthogonal_surjective_of_isSquare
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsquare : ∀ (v : V) [Invertible (Q v)], IsSquare (-⅟(Q v))) :
    Function.Surjective (spinToSpecialOrthogonal Q) :=
  spinToSpecialOrthogonal_surjective_of_pinToOrthogonal_surjective Q
    (pinToOrthogonal_surjective_of_isSquare Q hQ hsquare)

section IsSepClosed

variable [IsSepClosed K]

/-- The Spin action surjects onto the special orthogonal group for a finite-dimensional
nondegenerate quadratic space over a separably closed field. -/
theorem spinToSpecialOrthogonal_surjective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (spinToSpecialOrthogonal Q) :=
  spinToSpecialOrthogonal_surjective_of_pinToOrthogonal_surjective Q
    (pinToOrthogonal_surjective Q hQ)

end IsSepClosed

end Field

end Surjectivity

end CliffordAlgebra
