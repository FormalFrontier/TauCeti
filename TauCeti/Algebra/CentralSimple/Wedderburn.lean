/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Central.Matrix
public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn-Artin for central simple algebras

Mathlib's `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite` writes a finite-dimensional
simple `K`-algebra `A` as a matrix algebra `Matrix (Fin n) (Fin n) D` over a division algebra `D`,
but it says nothing about the centre of `D`: the theorem is about simplicity alone. For the theory
of central simple algebras one needs the refinement in which `D` is again **central** over `K`,
because that is the hypothesis every later structure theorem (the degree, Skolem-Noether, the Brauer
group) carries.

This file supplies the missing step. Feeding Mathlib's Wedderburn-Artin theorem the centrality
descent `TauCeti.isCentral_of_isCentral_matrix` gives `A ≃ₐ[K] Matrix (Fin n) (Fin n) D` with `D` a
central division algebra, together with the dimension count `finrank K A = n ^ 2 * finrank K D`.

The same file settles the finite base field. A finite division ring is a field (little Wedderburn),
so `Algebra.IsCentral.baseField_essentially_unique` collapses a finite central division algebra to
its base field, and every central simple algebra over a finite field is a full matrix algebra
`Matrix (Fin n) (Fin n) K`. In particular its dimension is the square `n ^ 2`. Centrality is what
makes this work: `𝔽_{q^m}` is a finite division algebra over `𝔽_q` which is *not* the base field,
the failure being exactly that its structure map is not surjective.

## Main results

* `TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`: **Wedderburn-Artin for central
  simple algebras**. A finite-dimensional central simple `K`-algebra `A` is
  `Matrix (Fin n) (Fin n) D` for a finite-dimensional **central** division `K`-algebra `D`, and
  `finrank K A = n ^ 2 * finrank K D`.
* `TauCeti.baseFieldAlgEquivOfFinite`: a finite central division algebra over a field is the base
  field.
* `TauCeti.IsSimpleRing.exists_algEquiv_matrix_of_finite`: a central simple algebra over a
  **finite** field is a full matrix algebra over that field, and
  `TauCeti.IsSimpleRing.isSquare_finrank_of_finite`: its dimension is a perfect square.

## Implementation notes

`TauCeti.baseFieldAlgEquivOfFinite` assumes `Finite D`, the single hypothesis little Wedderburn
needs, rather than the pair `Finite K` and `FiniteDimensional K D`; the two are equivalent, because
`K` embeds in `D`. The central-simple corollary does take the pair `Finite K` and
`FiniteDimensional K A`, which is how a finite base field is met in practice.

Uniqueness of the pair `(n, D)` is *not* proved here; it needs the invariance of the Wedderburn
data, which is a separate development.

## References

This implements the second bullet of Layer 4 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md)
(`A ≅ Mₙ(D)` for a central division algebra `D`, with `finrank K A = n² · finrank K D`) together
with its finite-field worked example. See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12,
and P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Chapter 2.
-/

public section

namespace TauCeti

universe u

/-! ### Wedderburn-Artin for central simple algebras -/

namespace IsSimpleRing

variable (K : Type*) [Field K] (A : Type u) [Ring A] [Algebra K A]

/-- **Wedderburn-Artin for central simple algebras.** A finite-dimensional central simple
`K`-algebra `A` is isomorphic to a matrix algebra over a finite-dimensional **central** division
`K`-algebra `D`, and then `finrank K A = n ^ 2 * finrank K D`.

Mathlib's `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite` supplies everything except the
centrality of `D`, which comes from `TauCeti.isCentral_of_isCentral_matrix`. -/
theorem exists_algEquiv_matrix_centralDivisionRing [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
      Module.finrank K A = n ^ 2 * Module.finrank K D ∧
        Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  have := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, hD, hDalg, hDfin, ⟨e⟩⟩ :=
    _root_.IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Nonempty (Fin n) := ⟨0⟩
  have : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A _ e
  refine ⟨n, hn, D, hD, hDalg, isCentral_of_isCentral_matrix K D (Fin n), hDfin, ?_, ⟨e⟩⟩
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin]
  ring

end IsSimpleRing

/-! ### Finite central division algebras and finite base fields -/

section Finite

variable (K : Type*) [Field K] (D : Type*) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [Finite D]

/-- A **finite central division algebra over a field is the base field**, as an isomorphism of
`K`-algebras.

A finite division ring is a field by little Wedderburn (the instance `littleWedderburn`), so `K → D`
is a central extension of fields and `Algebra.IsCentral.baseField_essentially_unique` applied to the
tower `D / D / K` makes it bijective. Centrality is essential: `𝔽_{q^m}` is a finite division
algebra over `𝔽_q` whose structure map is not surjective for `m > 1`. -/
noncomputable def baseFieldAlgEquivOfFinite : D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K D)
    (Algebra.IsCentral.baseField_essentially_unique K D D)).symm

@[simp]
theorem baseFieldAlgEquivOfFinite_symm_apply (a : K) :
    (baseFieldAlgEquivOfFinite K D).symm a = algebraMap K D a := by
  simp [baseFieldAlgEquivOfFinite]

@[simp]
theorem algebraMap_baseFieldAlgEquivOfFinite (x : D) :
    algebraMap K D (baseFieldAlgEquivOfFinite K D x) = x := by
  rw [← baseFieldAlgEquivOfFinite_symm_apply, AlgEquiv.symm_apply_apply]

/-- A finite central division algebra over a field is one-dimensional over it. -/
@[simp]
theorem finrank_eq_one_of_finite : Module.finrank K D = 1 := by
  rw [(baseFieldAlgEquivOfFinite K D).toLinearEquiv.finrank_eq, Module.finrank_self]

end Finite

namespace IsSimpleRing

variable (K : Type*) [Field K] [Finite K] (A : Type u) [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **A central simple algebra over a finite field is a full matrix algebra.** Over a finite field
the only finite-dimensional central division algebra is the field itself, so the division algebra in
the Wedderburn presentation collapses and `finrank K A = n ^ 2`.

This is the finite-field analogue of Mathlib's
`IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`; note that `IsSimpleRing A` alone would not
suffice, since `A` could be a proper field extension of `K`. -/
theorem exists_algEquiv_matrix_of_finite :
    ∃ (n : ℕ) (_ : NeZero n), Module.finrank K A = n ^ 2 ∧
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, D, _, _, _, _, hrank, ⟨e⟩⟩ := exists_algEquiv_matrix_centralDivisionRing K A
  have : Finite D := Module.finite_of_finite K
  refine ⟨n, hn, ?_, ⟨e.trans (AlgEquiv.mapMatrix (baseFieldAlgEquivOfFinite K D))⟩⟩
  rw [hrank, finrank_eq_one_of_finite K D, mul_one]

/-- The dimension of a central simple algebra over a finite field is a perfect square. -/
theorem isSquare_finrank_of_finite : IsSquare (Module.finrank K A) := by
  obtain ⟨n, _, hrank, -⟩ := exists_algEquiv_matrix_of_finite K A
  exact ⟨n, by rw [hrank, sq]⟩

end IsSimpleRing

end TauCeti
