/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Schur's lemma for simple modules

This file packages the two forms of Schur's lemma used by the semisimple-algebra development.

For simple modules over an arbitrary ring, Mathlib proves that a linear map is either bijective or
zero (`LinearMap.bijective_or_eq_zero`). Consequently the entire hom group vanishes exactly when the
two modules are not linearly equivalent. When an equivalence does exist, Mathlib's
`LinearEquiv.arrowCongrAddEquiv` identifies the hom group with either endomorphism ring by
composition; no separate construction is needed here.

Over an algebraically closed field, a finite-dimensional division algebra is the base field. The
proof uses Mathlib's stronger theorem that the algebra map from an algebraically closed field into
an integral algebra is bijective. Finite dimensionality supplies integrality.

## Main results

* `TauCeti.hom_eq_zero_of_isEmpty_linearEquiv`: every map between inequivalent simple modules is
  zero.
* `TauCeti.subsingleton_linearMap_iff_isEmpty_linearEquiv`: the corresponding characterization of
  the whole hom group.
* `TauCeti.nontrivial_linearMap_iff_nonempty_linearEquiv`: two simple modules are equivalent exactly
  when their hom group is nontrivial.
* `TauCeti.algEquiv_self_of_finiteDimensional_divisionRing`: a finite-dimensional division algebra
  over an algebraically closed field is isomorphic to that field as an algebra.

## References

This implements Layer 1, "Schur, assembled", of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See N. Jacobson, *Basic Algebra II*, Chapter 3, or T. Y. Lam, *A First Course in Noncommutative
Rings*, Chapter 1.
-/

public section

namespace TauCeti

universe u v w

/-! ### Maps between simple modules -/

section SimpleModules

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [IsSimpleModule R M] [IsSimpleModule R N]

/-- **Schur's lemma, vanishing form.** A linear map between simple modules is zero if the two
modules are not linearly equivalent.

The `IsEmpty` hypothesis is the constructive form of saying that no equivalence exists. -/
theorem hom_eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) (f : M →ₗ[R] N) :
    f = 0 := by
  rcases f.bijective_or_eq_zero with hf | hf
  · exact (h.false (LinearEquiv.ofBijective f hf)).elim
  · exact hf

/-- The hom group between simple modules is a subsingleton if the modules are not linearly
equivalent. -/
theorem subsingleton_linearMap_of_isEmpty_linearEquiv (h : IsEmpty (M ≃ₗ[R] N)) :
    Subsingleton (M →ₗ[R] N) :=
  ⟨fun f g ↦ sub_eq_zero.mp (hom_eq_zero_of_isEmpty_linearEquiv h (f - g))⟩

/-- The hom group between two simple modules is a subsingleton exactly when the modules are not
linearly equivalent. -/
theorem subsingleton_linearMap_iff_isEmpty_linearEquiv :
    Subsingleton (M →ₗ[R] N) ↔ IsEmpty (M ≃ₗ[R] N) := by
  constructor
  · intro h
    letI := h
    exact ⟨fun e ↦ by
      have hzero : e.toLinearMap = 0 := Subsingleton.elim _ _
      haveI := IsSimpleModule.nontrivial R M
      exact e.toLinearMap.ne_zero_of_injective e.injective hzero⟩
  · exact subsingleton_linearMap_of_isEmpty_linearEquiv

/-- The hom group between two simple modules is nontrivial exactly when the modules are linearly
equivalent. This is the existence form of Schur's lemma. -/
theorem nontrivial_linearMap_iff_nonempty_linearEquiv :
    Nontrivial (M →ₗ[R] N) ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_linearMap_iff_isEmpty_linearEquiv,
    not_isEmpty_iff]

end SimpleModules

/-! ### Division algebras over algebraically closed fields -/

section IsAlgClosed

variable {k : Type u} {D : Type v} [Field k] [IsAlgClosed k] [DivisionRing D] [Algebra k D]
variable [FiniteDimensional k D]

/-- A finite-dimensional division algebra over an algebraically closed field is the field itself,
as an isomorphism of algebras.

Finite dimensionality makes `D` integral over `k`; Mathlib proves that the algebra map from an
algebraically closed field to any integral division algebra is bijective. -/
theorem algEquiv_self_of_finiteDimensional_divisionRing : Nonempty (D ≃ₐ[k] k) :=
  ⟨(AlgEquiv.ofBijective (Algebra.ofId k D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

/-- A finite-dimensional division algebra over an algebraically closed field has dimension one. -/
@[simp]
theorem finrank_divisionRing_eq_one : Module.finrank k D = 1 := by
  obtain ⟨e⟩ := algEquiv_self_of_finiteDimensional_divisionRing (k := k) (D := D)
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]

end IsAlgClosed

end TauCeti
