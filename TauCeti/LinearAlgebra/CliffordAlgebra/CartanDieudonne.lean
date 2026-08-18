/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne

/-!
# Cartan--Dieudonné for Lipschitz and Pin actions

Over a field of characteristic other than two, Cartan--Dieudonné and the action of a generating
vector show that the Lipschitz action is onto the orthogonal group.

Let `g` be an orthogonal automorphism fixing a subspace `W`, and let `x` be an anisotropic vector
orthogonal to `W`. The generic fixed-subspace correction in the quadratic-form layer uses one or
two reflections to make the product fix `W ⊔ K ∙ x`. Over a separably closed field of
characteristic other than two, those reflections lift through the Pin group, so the correcting
element lies in the range of `pinToOrthogonal`.

## Main results

* `CliffordAlgebra.lipschitzToOrthogonal_surjective`: the Lipschitz action is onto for a
  finite-dimensional nondegenerate quadratic space.
* `CliffordAlgebra.exists_mem_range_pinToOrthogonal_mul_eqOn_sup_span_singleton`: a
  Pin-range correction extends a fixed subspace by one orthogonal anisotropic vector.
* `CliffordAlgebra.pinToOrthogonal_surjective`: over a separably closed field of
  characteristic other than two, the Pin action is surjective on a finite-dimensional
  nondegenerate quadratic space.

## References

This advances Layer 2's "The double cover" target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

universe u v

namespace CliffordAlgebra

open TauCeti

variable {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- The Lipschitz action is onto the orthogonal group of a finite-dimensional nondegenerate
quadratic space over a field of characteristic other than two. -/
theorem lipschitzToOrthogonal_surjective
    [NeZero (2 : K)] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective
      (@lipschitzToOrthogonal K V _ _ _ Q
        (invertibleOfNonzero (NeZero.ne (2 : K)))) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  exact MonoidHom.range_eq_top.mp <|
    QuadraticMap.subgroup_eq_top_of_reflection_mem
      Q hQ (lipschitzToOrthogonal Q).range
      fun v _ ↦ by
        rw [MonoidHom.mem_range]
        exact ⟨⟨unitι Q v, unitι_mem_lipschitzGroup v⟩,
          lipschitzToOrthogonal_unitι Q v⟩

variable [Invertible (2 : K)]

section IsSepClosed

variable [IsSepClosed K]

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

end IsSepClosed

/-- Over a field of characteristic other than two, the twisted-conjugation homomorphism from the
Pin group is surjective when every reflection normalization scalar is a square. -/
theorem pinToOrthogonal_surjective_of_isSquare
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsquare : ∀ (v : V) [Invertible (Q v)], IsSquare (-⅟(Q v))) :
    Function.Surjective (pinToOrthogonal Q) :=
  MonoidHom.range_eq_top.mp <|
    QuadraticMap.subgroup_eq_top_of_reflection_mem
      Q hQ (pinToOrthogonal Q).range
      fun v _ ↦ reflection_mem_range_pinToOrthogonal_of_isSquare Q v (hsquare v)

section IsSepClosed

variable [IsSepClosed K]

/-- The twisted-conjugation homomorphism from the Pin group is surjective for a
finite-dimensional nondegenerate quadratic space over a separably closed field of characteristic
other than two. -/
theorem pinToOrthogonal_surjective
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (pinToOrthogonal Q) :=
  pinToOrthogonal_surjective_of_isSquare Q hQ fun v _ ↦
    IsSepClosed.exists_eq_mul_self (-⅟(Q v))

end IsSepClosed
end CliffordAlgebra
