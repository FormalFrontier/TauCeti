/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal

/-!
# Surjectivity of the Spin action

The determinant-one Pin elements are even, so Pin surjectivity restricts to Spin surjectivity onto
the special orthogonal group.

## Main definitions and results

* `TauCeti.CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_isSquare` proves its
  surjectivity when every reflection normalization scalar is a square.
* `TauCeti.CliffordAlgebra.spinToSpecialOrthogonal_surjective` specializes this to a
  separably closed field.

## References

This advances Layer 2's double-cover target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.CliffordAlgebra

universe u v

section Surjectivity

variable {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]

/-- The Spin action surjects onto the special orthogonal group when every reflection
normalization scalar is a square. -/
theorem spinToSpecialOrthogonal_surjective_of_isSquare
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsquare : ∀ (v : V) [Invertible (Q v)], IsSquare (-⅟(Q v))) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  have hpin := pinToOrthogonal_surjective_of_isSquare Q hQ hsquare
  intro g
  let og : QuadraticMap.orthogonalGroup Q :=
    ⟨(g : V ≃ₗ[K] V), (QuadraticMap.mem_specialOrthogonalGroup_iff.1 g.2).1⟩
  obtain ⟨p, hp⟩ := hpin og
  have hdet_one :
      LinearEquiv.det
        (((pinToOrthogonal Q p : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V)) = 1 := by
    rw [hp]
    exact (QuadraticMap.mem_specialOrthogonalGroup_iff.1 g.2).2
  let s : spinGroup Q := ⟨p, p.2, mem_even_of_det_pinToOrthogonal_eq_one Q p hdet_one⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_spinToSpecialOrthogonal_apply, ← coe_spinToOrthogonal_apply]
  have hspinpin : spinToPin Q s = p := by
    apply Subtype.ext
    rw [coe_spinToPin_apply]
  rw [← pinToOrthogonal_spinToPin, hspinpin, hp]

section IsSepClosed

variable [IsSepClosed K]

/-- The Spin action surjects onto the special orthogonal group for a finite-dimensional
nondegenerate quadratic space over a separably closed field. -/
theorem spinToSpecialOrthogonal_surjective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (spinToSpecialOrthogonal Q) :=
  spinToSpecialOrthogonal_surjective_of_isSquare Q hQ fun v _ ↦
    IsSepClosed.exists_eq_mul_self (-⅟(Q v))

end IsSepClosed

end Surjectivity

end TauCeti.CliffordAlgebra
