/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift

/-!
# The one-step Cartan--Dieudonne reduction

Let `g` be an orthogonal automorphism and let `v` have invertible norm. At least one of `g v - v`
and `g v + v` has invertible norm. A reflection in the former carries `g v` to `v`; a reflection
in the latter followed by the reflection in `v` does the same. Since these reflections lift to the
Pin group over a separably closed field of characteristic not two, an element in the range of
`pinToOrthogonal` can be multiplied into `g` to make it fix `v`.

This is the one-vector reduction used by the finite-dimensional Cartan--Dieudonne induction.

## Main result

* `TauCeti.CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_apply_eq_self`: an element in the
  range of the Pin action corrects an orthogonal automorphism to fix a chosen vector of invertible
  norm.

## References

This advances Layer 2's "The double cover" target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace CliffordAlgebra

variable {K : Type u} {V : Type v} [Field K] [IsSepClosed K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- Given an orthogonal automorphism `g` and a vector `v` of invertible norm, an element in the
range of the Pin action can be multiplied into `g` so that the product fixes `v`. The correcting
orthogonal element is the image under `pinToOrthogonal` of a lift of either one reflection or two
reflections. -/
theorem exists_mem_range_pinToOrthogonal_mul_apply_eq_self
    (g : QuadraticMap.orthogonalGroup Q) (v : V)
    [Invertible (Q v)] :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v = v) := by
  have reflection_mem_range (w : V) [Invertible (Q w)] :
      QuadraticMap.reflectionOrthogonal Q w ∈ (pinToOrthogonal Q).range :=
    reflection_mem_range_pinToOrthogonal_of_isSquare Q w
      (IsSepClosed.exists_eq_mul_self _)
  have hmap : Q ((g : V ≃ₗ[K] V) v) = Q v :=
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2 v
  rcases QuadraticMap.isUnit_sub_or_add_of_map_eq Q _ v hmap
      (isUnit_of_invertible (Q v)).ne_zero with hsub | hadd
  · let : Invertible (Q ((g : V ≃ₗ[K] V) v - v)) := hsub.invertible
    refine ⟨QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[K] V) v - v),
      reflection_mem_range _, ?_⟩
    simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal, LinearEquiv.mul_apply]
    exact QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ v hmap
  · have : Invertible (Q ((g : V ≃ₗ[K] V) v - -v)) := by
      simpa only [sub_neg_eq_add] using hadd.invertible
    refine ⟨QuadraticMap.reflectionOrthogonal Q v *
        QuadraticMap.reflectionOrthogonal Q ((g : V ≃ₗ[K] V) v - -v),
      (pinToOrthogonal Q).range.mul_mem (reflection_mem_range v) (reflection_mem_range _), ?_⟩
    simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal, LinearEquiv.mul_apply]
    rw [QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ (-v)
      (hmap.trans (Q.map_neg v).symm), map_neg, QuadraticMap.reflection_apply_self, neg_neg]

end CliffordAlgebra
end TauCeti
