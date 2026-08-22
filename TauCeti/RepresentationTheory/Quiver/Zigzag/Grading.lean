/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# The zigzag relations are homogeneous

Every zigzag relator of a simple graph is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the two quadratic families sit in degree two, and each long
generator is a single path, homogeneous of its own length. Consequently both relation ideals of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Relations` are homogeneous ideals.

## Main results

* `TauCeti.IsZigzagRelator.isHomogeneousElem` and
  `TauCeti.IsQuadraticZigzagRelator.mem_grade_two`: the relators are homogeneous, the quadratic
  ones in degree two.
* `TauCeti.isHomogeneous_zigzagIdeal` and `TauCeti.isHomogeneous_quadraticZigzagIdeal`: **the
  relation ideals are homogeneous.**

## References

This is the homogeneity half of the grading clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks for the relation ideal to be
homogeneous for the path-length grading. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-- **The quadratic zigzag relators sit in degree two**: a non-returning length-two path is a
single basis path of length two, and a difference of two length-two backtracks is a difference of
two such. -/
theorem IsQuadraticZigzagRelator.mem_grade_two {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) : x ∈ grade k (DoubledQuiver G) 2 := by
  cases hx with
  | nonreturn p hp _ => exact ofPath_mem_grade_of_length hp
  | equal_backtracks p q hp hq =>
    exact Submodule.sub_mem _ (ofPath_mem_grade_of_length hp) (ofPath_mem_grade_of_length hq)

/-- The quadratic zigzag relators are homogeneous. -/
theorem IsQuadraticZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) :
    SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x :=
  ⟨2, IsQuadraticZigzagRelator.mem_grade_two k G hx⟩

/-- **The uniform zigzag relators are homogeneous**: the quadratic ones in degree two, and each
long generator in the degree its own length names. -/
theorem IsZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x := by
  cases hx with
  | quadratic h => exact IsQuadraticZigzagRelator.isHomogeneousElem k G h
  | long_path y _ => exact ⟨y.2.2.length, ofPath_mem_grade y⟩

variable [Finite V]

/-- **The quadratic relation ideal is homogeneous** for the path-length grading. -/
theorem isHomogeneous_quadraticZigzagIdeal :
    (quadraticZigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [quadraticZigzagIdeal_eq_span]
  exact isHomogeneous_asIdeal_span _ fun _ hx =>
    IsQuadraticZigzagRelator.isHomogeneousElem k G hx

/-- **The uniform relation ideal is homogeneous** for the path-length grading. This is what makes
the zigzag quotient a graded algebra. -/
theorem isHomogeneous_zigzagIdeal :
    (zigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [zigzagIdeal_eq_span]
  exact isHomogeneous_asIdeal_span _ fun _ hx => IsZigzagRelator.isHomogeneousElem k G hx

end TauCeti
