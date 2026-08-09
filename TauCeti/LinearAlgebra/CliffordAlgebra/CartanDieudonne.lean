/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift

/-!
# Pin corrections over fixed subspaces

Let `g` be an orthogonal automorphism fixing a subspace `W`, and let `x` be an anisotropic vector
orthogonal to `W`. The generic fixed-subspace correction in the quadratic-form layer uses one or
two reflections to make the product fix `W ⊔ K ∙ x`. Over a separably closed field those
reflections lift through the Pin group, so the correcting element lies in the range of
`pinToOrthogonal`.

## Main results

* `TauCeti.CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_eqOn_sup_span_singleton`: a
  Pin-range correction extends a fixed subspace by one orthogonal anisotropic vector.
* `TauCeti.CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_apply_eq_self`: the specialization
  to the zero subspace corrects one vector.

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

/-- Given an orthogonal automorphism that fixes `W` and an anisotropic vector `x` orthogonal to
`W`, a Pin-range correction makes the product fix `W ⊔ K ∙ x` pointwise. -/
theorem exists_mem_range_pinToOrthogonal_mul_eqOn_sup_span_singleton
    (g : QuadraticMap.orthogonalGroup Q) (W : Submodule K V)
    (hfix : ∀ w ∈ W, ((g : V ≃ₗ[K] V) w) = w)
    (x : V) [Invertible (Q x)]
    (hx : x ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W) :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      ∀ y ∈ W ⊔ Submodule.span K {x},
        (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) y) = y :=
  QuadraticMap.exists_mem_subgroup_mul_eqOn_sup_span_singleton_of_reflection_mem Q
    (pinToOrthogonal Q).range (reflection_mem_range_pinToOrthogonal Q) g W hfix x hx

/-- Given an orthogonal automorphism `g` and a vector `v` of invertible norm, an element in the
range of the Pin action can be multiplied into `g` so that the product fixes `v`. -/
theorem exists_mem_range_pinToOrthogonal_mul_apply_eq_self
    (g : QuadraticMap.orthogonalGroup Q) (v : V) [Invertible (Q v)] :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v = v) := by
  obtain ⟨r, hr, hfix⟩ :=
    exists_mem_range_pinToOrthogonal_mul_eqOn_sup_span_singleton Q g ⊥ (by simp) v (by simp)
  exact ⟨r, hr, hfix v (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))⟩

end CliffordAlgebra
end TauCeti
