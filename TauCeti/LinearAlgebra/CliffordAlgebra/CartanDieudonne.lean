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
    (hx : ∀ w ∈ W, Q.IsOrtho x w) :
    ∃ r : QuadraticMap.orthogonalGroup Q, r ∈ (pinToOrthogonal Q).range ∧
      ∀ y ∈ W ⊔ Submodule.span K {x},
        (((r * g : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) y) = y :=
  QuadraticMap.exists_mem_subgroup_mul_eqOn_sup_span_singleton_of_reflection_mem Q
    (pinToOrthogonal Q).range (reflection_mem_range_pinToOrthogonal Q) g W hfix x hx

end CliffordAlgebra
end TauCeti
