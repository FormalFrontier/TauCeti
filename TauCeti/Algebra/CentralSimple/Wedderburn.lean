/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix
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

This file supplies the missing step. Mathlib proves that a matrix algebra over a central algebra is
central (`Algebra.IsCentral.matrix`); the converse is `TauCeti.isCentral_of_isCentral_matrix`, which
reads off the centre of `D` from the centre of `Matrix ι ι D` using
`Matrix.subalgebraCenter_eq_scalarAlgHom_map` and injectivity of `Matrix.scalarAlgHom`. Feeding it
Mathlib's Wedderburn-Artin theorem gives `A ≃ₐ[K] Matrix (Fin n) (Fin n) D` with `D` a central
division algebra, together with the dimension count `finrank K A = n ^ 2 * finrank K D`.

The same file settles the finite base field. A finite division ring is a field (little Wedderburn),
and a *commutative* algebra is central exactly when its structure map is onto, so a central division
algebra over a finite field is the field itself and every central simple algebra over a finite field
is a full matrix algebra `Matrix (Fin n) (Fin n) K`. In particular its dimension is the square
`n ^ 2`. Centrality is what makes this work: `𝔽_{q^m}` is a finite division algebra over `𝔽_q`
which is *not* the base field, and `TauCeti.isCentral_iff_surjective_algebraMap` locates the
failure precisely in the surjectivity of the structure map.

## Main results

* `TauCeti.isCentral_of_isCentral_matrix`: if `Matrix ι ι D` is central over `K` for a nonempty
  finite `ι`, then so is `D`; `TauCeti.isCentral_matrix_iff` packages this with Mathlib's converse.
* `TauCeti.exists_algEquiv_matrix_centralDivisionRing`: **Wedderburn-Artin for central simple
  algebras**. A finite-dimensional central simple `K`-algebra `A` is `Matrix (Fin n) (Fin n) D` for
  a finite-dimensional **central** division `K`-algebra `D`, and
  `finrank K A = n ^ 2 * finrank K D`.
* `TauCeti.surjective_algebraMap_of_mul_comm`, `TauCeti.isCentral_iff_surjective_algebraMap`: a
  commutative `K`-algebra is central iff its structure map is surjective.
* `TauCeti.algebraMap_bijective_of_finite`, `TauCeti.baseFieldAlgEquivOfFinite`: a finite central
  division algebra over a field is the base field.
* `TauCeti.exists_algEquiv_matrix_of_finite`: a central simple algebra over a **finite** field is a
  full matrix algebra over that field, and `TauCeti.isSquare_finrank_of_finite`: its dimension is a
  perfect square.

## Implementation notes

`TauCeti.isCentral_of_isCentral_matrix` is deliberately *not* an instance: its hypothesis mentions
`Matrix ι ι D` while its conclusion mentions only `D`, so instance search could not run it
backwards, and the index type `ι` is unconstrained by the goal.

`TauCeti.algebraMap_bijective_of_finite` assumes `Finite D`, the single hypothesis little Wedderburn
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

/-! ### Centrality descends from a matrix algebra to its coefficients -/

section Descent

variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D]
  (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- If a matrix algebra `Matrix ι ι D` over a nonempty finite index type is central over `K`, then
its coefficient algebra `D` is central over `K`.

The centre of `Matrix ι ι D` is the image of the centre of `D` under the scalar embedding
`Matrix.scalarAlgHom`, which is injective because `ι` is nonempty; so the centre of `D` is `⊥` as
soon as the centre of the matrix algebra is. This is the converse of `Algebra.IsCentral.matrix`. -/
theorem isCentral_of_isCentral_matrix [Algebra.IsCentral K (Matrix ι ι D)] :
    Algebra.IsCentral K D := by
  have hinj : Function.Injective (Matrix.scalarAlgHom ι K : D →ₐ[K] Matrix ι ι D) :=
    fun _ _ h ↦ by simpa using h
  have h : (Subalgebra.center K D).map (Matrix.scalarAlgHom ι K) =
      (⊥ : Subalgebra K D).map (Matrix.scalarAlgHom ι K) := by
    rw [Algebra.map_bot, ← Matrix.subalgebraCenter_eq_scalarAlgHom_map,
      Algebra.IsCentral.center_eq_bot]
  exact ⟨(Subalgebra.map_injective hinj h).le⟩

/-- A matrix algebra over a nonempty finite index type is central exactly when its coefficient
algebra is. -/
theorem isCentral_matrix_iff :
    Algebra.IsCentral K (Matrix ι ι D) ↔ Algebra.IsCentral K D :=
  ⟨fun _ ↦ isCentral_of_isCentral_matrix K D ι, fun _ ↦ Algebra.IsCentral.matrix K D ι⟩

end Descent

/-! ### Wedderburn-Artin for central simple algebras -/

section CentralSimple

variable (K : Type*) [Field K] (A : Type u) [Ring A] [Algebra K A]

/-- Transporting a dimension count along a matrix presentation: an algebra isomorphic to
`n × n` matrices over `D` has dimension `n ^ 2 * finrank K D`. -/
theorem finrank_eq_sq_mul_finrank {n : ℕ} {D : Type*} [Ring D] [Algebra K D]
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) :
    Module.finrank K A = n ^ 2 * Module.finrank K D := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin]
  ring

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
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Nonempty (Fin n) := ⟨0⟩
  have : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A _ e
  exact ⟨n, hn, D, hD, hDalg, isCentral_of_isCentral_matrix K D (Fin n), hDfin,
    finrank_eq_sq_mul_finrank K A e, ⟨e⟩⟩

end CentralSimple

/-! ### Central algebras that happen to be commutative -/

/-- If a central `K`-algebra has commutative multiplication then its structure map is surjective:
every element lies in the centre, hence in the image of `K`.

Commutativity is taken as a hypothesis rather than as a `CommSemiring` instance so that the lemma
applies to a `DivisionRing` that little Wedderburn has shown to be commutative, without introducing
a second multiplicative structure on it. -/
theorem surjective_algebraMap_of_mul_comm (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D]
    [Algebra.IsCentral K D] (h : ∀ x y : D, x * y = y * x) :
    Function.Surjective (algebraMap K D) := fun x ↦ by
  obtain ⟨a, ha⟩ :=
    (Algebra.IsCentral.mem_center_iff K).mp (Subalgebra.mem_center_iff.mpr fun b ↦ h b x)
  exact ⟨a, ha.symm⟩

/-- A commutative `K`-algebra is central over `K` exactly when its structure map is surjective: the
centre of a commutative algebra is all of it, so demanding that the centre be the image of `K`
demands that everything be in the image of `K`.

This is the precise sense in which centrality is a strong condition on a field extension: `L / K` is
central only when `L = K`. It is also what makes the finite-field results below work, once little
Wedderburn has made a finite division algebra commutative. -/
theorem isCentral_iff_surjective_algebraMap (K D : Type*) [CommSemiring K] [CommSemiring D]
    [Algebra K D] : Algebra.IsCentral K D ↔ Function.Surjective (algebraMap K D) := by
  refine ⟨fun _ ↦ surjective_algebraMap_of_mul_comm K D fun x y ↦ mul_comm x y,
    fun h ↦ ⟨fun x _ ↦ ?_⟩⟩
  obtain ⟨a, rfl⟩ := h x
  exact Algebra.mem_bot.mpr ⟨a, rfl⟩

/-! ### Finite central division algebras and finite base fields -/

section Finite

variable (K : Type*) [Field K] (D : Type*) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [Finite D]

/-- A **finite central division algebra over a field is the base field**: its structure map is
bijective.

A finite division ring is commutative by little Wedderburn, and a commutative central algebra has
surjective structure map; injectivity is automatic over a field. Centrality is essential: `𝔽_{q^m}`
is a finite division algebra over `𝔽_q` whose structure map is not surjective for `m > 1`. -/
theorem algebraMap_bijective_of_finite : Function.Bijective (algebraMap K D) :=
  ⟨(algebraMap K D).injective,
    surjective_algebraMap_of_mul_comm K D (Finite.isDomain_to_isField D).mul_comm⟩

/-- The identification of a finite central division algebra with its base field, as an isomorphism
of `K`-algebras. -/
noncomputable def baseFieldAlgEquivOfFinite : D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K D) (algebraMap_bijective_of_finite K D)).symm

@[simp]
theorem baseFieldAlgEquivOfFinite_symm_apply (a : K) :
    (baseFieldAlgEquivOfFinite K D).symm a = algebraMap K D a := by
  simp [baseFieldAlgEquivOfFinite]

/-- A finite central division algebra over a field is one-dimensional over it. -/
theorem finrank_eq_one_of_finite : Module.finrank K D = 1 := by
  rw [(baseFieldAlgEquivOfFinite K D).toLinearEquiv.finrank_eq, Module.finrank_self]

end Finite

section FiniteField

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

end FiniteField

end TauCeti
