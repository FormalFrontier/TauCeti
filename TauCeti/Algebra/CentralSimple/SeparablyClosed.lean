/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the central-division-algebra form of Artin--Wedderburn is refined below, and its
-- hypotheses occur in the exported matrix-presentation theorem.
public import TauCeti.Algebra.CentralSimple.Wedderburn
-- `IsSepClosed` occurs throughout the exported signatures.
public import Mathlib.FieldTheory.IsSepClosed
-- Non-public: Jacobson--Noether supplies a separable element outside the centre of any
-- noncommutative finite-dimensional central division algebra.
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Central simple algebras over separably closed fields

A finite-dimensional central simple algebra over a separably closed field is a full matrix
algebra.  This strengthens the algebraically closed case used in the initial splitting-field API
and is the field-theoretic input for refining an arbitrary finite splitting extension to a finite
separable one.

The only extra issue over the algebraically closed proof is the coefficient division algebra in
Artin--Wedderburn.  If a finite-dimensional central division algebra `D` over a separably closed
field `K` were larger than `K`, the Jacobson--Noether theorem would produce an element of `D`
outside `K` that is separable over `K`.  Its irreducible minimal polynomial would have degree one,
because `K` is separably closed, so the element would in fact lie in `K`, a contradiction.

The scalar-extension and splitting consequences live in
`TauCeti/Algebra/CentralSimple/Degree.lean` and
`TauCeti/Algebra/CentralSimple/Splitting.lean`, where they replace the former algebraically closed
special cases.

## Main results

* `TauCeti.baseFieldAlgEquivOfIsSepClosed`: a finite-dimensional central division algebra over a
  separably closed field is the base field.
* `TauCeti.IsSimpleRing.exists_algEquiv_matrix_of_isSepClosed`: a finite-dimensional central simple
  algebra over a separably closed field is a full matrix algebra.

## References

This is the separably-closed-field prerequisite for the finite separable splitting extension in
Layer 6, “Splitting fields, maximal subfields, and the index”, of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See N. Jacobson, *Basic Algebra II*, 2nd ed., Chapter 15, and P. Gille and T. Szamuely,
*Central Simple Algebras and Galois Cohomology*, Section 2.2.
-/

public section

namespace TauCeti

open Polynomial

universe u

/-! ### Central division algebras over a separably closed field -/

section Division

variable (K : Type*) [Field K] [IsSepClosed K]
variable (D : Type u) [DivisionRing D] [Algebra K D]

/-- An element of a division algebra that is separable over a separably closed base field belongs
to the image of that base field.

The minimal polynomial is irreducible because the ambient algebra is a division ring.  It is
separable by hypothesis, hence has degree one over a separably closed field. The degree-one
calculation adapts Mathlib's `IsSepClosed.algebraMap_surjective` from a field extension to a single
element of a possibly noncommutative division algebra. -/
theorem mem_bot_of_isSeparable {x : D} (hx : IsSeparable K x) :
    x ∈ (⊥ : Subalgebra K D) := by
  rw [Algebra.mem_bot]
  refine ⟨-(minpoly K x).coeff 0, ?_⟩
  have hlead : (minpoly K x).leadingCoeff = 1 := minpoly.monic hx.isIntegral
  have hdegree : (minpoly K x).degree = 1 :=
    IsSepClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx.isIntegral) hx
  have heval : aeval x (minpoly K x) = 0 := minpoly.aeval K x
  rw [eq_X_add_C_of_degree_eq_one hdegree, hlead, C_1, one_mul, aeval_add, aeval_X,
    aeval_C, add_eq_zero_iff_eq_neg] at heval
  exact (map_neg (algebraMap K D) ((minpoly K x).coeff 0)).trans heval.symm

variable [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- The structure map from a separably closed field onto a finite-dimensional central division
algebra is surjective.

If its image were proper, Jacobson--Noether would give a separable element outside it, contradicting
`TauCeti.mem_bot_of_isSeparable`. -/
theorem algebraMap_surjective_of_isSepClosed : Function.Surjective (algebraMap K D) := by
  have hbot : (⊥ : Subalgebra K D) = ⊤ := by
    by_contra hne
    obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
    exact hx (mem_bot_of_isSeparable K D hsep)
  intro x
  apply Algebra.mem_bot.mp
  rw [hbot]
  exact Set.mem_univ x

/-- A finite-dimensional central division algebra over a separably closed field is the base field,
as an equivalence of algebras. -/
noncomputable def baseFieldAlgEquivOfIsSepClosed : D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K D)
    ⟨RingHom.injective (algebraMap K D), algebraMap_surjective_of_isSepClosed K D⟩).symm

@[simp]
theorem baseFieldAlgEquivOfIsSepClosed_symm_apply (a : K) :
    (baseFieldAlgEquivOfIsSepClosed K D).symm a = algebraMap K D a := by
  rw [baseFieldAlgEquivOfIsSepClosed, AlgEquiv.symm_symm]
  exact AlgEquiv.ofBijective_apply _ _ a

@[simp]
theorem algebraMap_baseFieldAlgEquivOfIsSepClosed (x : D) :
    algebraMap K D (baseFieldAlgEquivOfIsSepClosed K D x) = x := by
  rw [← baseFieldAlgEquivOfIsSepClosed_symm_apply, AlgEquiv.symm_apply_apply]

/-- A finite-dimensional central division algebra over a separably closed field is
one-dimensional over that field. -/
@[simp]
theorem finrank_eq_one_of_isSepClosed : Module.finrank K D = 1 := by
  rw [(baseFieldAlgEquivOfIsSepClosed K D).toLinearEquiv.finrank_eq, Module.finrank_self]

end Division

/-! ### Central simple algebras -/

namespace IsSimpleRing

variable (K : Type*) [Field K] [IsSepClosed K]
variable (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **Artin--Wedderburn over a separably closed field.** A finite-dimensional central simple
`K`-algebra is a full matrix algebra over `K`. -/
theorem exists_algEquiv_matrix_of_isSepClosed :
    ∃ (n : ℕ) (_ : NeZero n), Module.finrank K A = n ^ 2 ∧
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, D, _, _, _, _, hrank, ⟨e⟩⟩ :=
    exists_algEquiv_matrix_centralDivisionRing K A
  refine ⟨n, hn, ?_, ⟨e.trans (AlgEquiv.mapMatrix (baseFieldAlgEquivOfIsSepClosed K D))⟩⟩
  rw [hrank, finrank_eq_one_of_isSepClosed K D, mul_one]

end IsSimpleRing

end TauCeti
