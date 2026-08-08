/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift

/-!
# The one-step Cartan--Dieudonne reduction

Let `g` be an orthogonal automorphism and let `v` have invertible norm. At least one of `g v - v`
and `g v + v` has invertible norm. A reflection in the former carries `g v` to `v`; a reflection
in the latter followed by the reflection in `v` does the same. Since these reflections lift to the
Pin group over an algebraically closed field, an element in the range of `pinToOrthogonal` can be
multiplied into `g` to make it fix `v`.

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

variable {K : Type u} {V : Type v} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- Given an orthogonal automorphism `g` and a vector `v` of invertible norm, an element in the
range of the Pin action can be multiplied into `g` so that the product fixes `v`. The correcting
element is the lift of either one reflection or a product of two reflections. -/
theorem exists_mem_range_pinToOrthogonal_mul_apply_eq_self
    (g : QuadraticMap.orthogonalGroup Q) (v : V)
    [Invertible (Q v)] :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v = v) := by
  have hmap : Q ((g : V ≃ₗ[K] V) v) = Q v :=
    QuadraticMap.map_app_of_mem_orthogonalGroup g.2 v
  rcases QuadraticMap.isUnit_sub_or_add_of_map_eq Q _ v hmap with hsub | hadd
  · let : Invertible (Q ((g : V ≃ₗ[K] V) v - v)) := hsub.invertible
    let r : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - v),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r, reflection_mem_range_pinToOrthogonal Q _, ?_⟩
    -- Expose the underlying automorphisms of the subgroup product before applying the reflection
    -- computation.
    change QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v - v)
      ((g : V ≃ₗ[K] V) v) = v
    exact QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ v hmap
  · let : Invertible (Q ((g : V ≃ₗ[K] V) v + v)) := hadd.invertible
    let r₁ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q v, QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    let r₂ : QuadraticMap.orthogonalGroup Q :=
      ⟨QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v + v),
        QuadraticMap.reflection_mem_orthogonalGroup Q _⟩
    refine ⟨r₁ * r₂,
      (pinToOrthogonal Q).range.mul_mem (reflection_mem_range_pinToOrthogonal Q v)
        (reflection_mem_range_pinToOrthogonal Q _), ?_⟩
    -- Expose the two underlying reflections before applying their public computation equations.
    change QuadraticMap.reflection Q v
      (QuadraticMap.reflection Q ((g : V ≃ₗ[K] V) v + v)
        ((g : V ≃ₗ[K] V) v)) = v
    rw [QuadraticMap.reflection_add_apply_eq_neg_of_map_eq Q _ v hmap, map_neg,
      QuadraticMap.reflection_apply_self, neg_neg]

end CliffordAlgebra
end TauCeti
