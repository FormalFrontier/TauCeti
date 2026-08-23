/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.BrauerGroup.Group` is imported publicly: the statements use the Brauer class
-- map, `CSA.of`, and the finite-dimensional central division-algebra vocabulary that it re-exports.
public import TauCeti.Algebra.BrauerGroup.Group
-- Non-public: the existence half is Wedderburn--Artin for a central simple algebra, while the
-- uniqueness half uses the algebra-linear invariance of the division algebra in a matrix
-- presentation. Neither implementation theorem occurs in the public statements.
import TauCeti.Algebra.CentralSimple.Wedderburn
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing

/-!
# Division-algebra representatives of Brauer classes

Every class in the Brauer group of a field has a representative which is a finite-dimensional
central **division** algebra, and this representative is unique up to isomorphism as an algebra
over the base field.

Existence is the Wedderburn--Artin theorem. A representative `A` of the class has a presentation
`A ≃ₐ[K] Mₙ(D)` for a central division algebra `D`; an algebra isomorphism and passage to matrices
both preserve the Brauer class, so `[A] = [D]`.

For uniqueness, if central division algebras `D` and `E` have the same class, Brauer equivalence
gives positive `n` and `m` and an algebra isomorphism `Mₙ(D) ≃ₐ[K] Mₘ(E)`. The algebra-linear
Wedderburn uniqueness theorem
`TauCeti.nonempty_algEquiv_of_algEquiv_matrix` then gives `D ≃ₐ[K] E`. Its algebra linearity is
load-bearing: ring-level Wedderburn uniqueness alone would not say that the resulting isomorphism
fixes the chosen copy of `K`.

## Main results

* `TauCeti.BrauerGroup.exists_eq_mk_centralDivisionRing`: every Brauer class is represented by a
  finite-dimensional central division algebra.
* `TauCeti.BrauerGroup.nonempty_algEquiv_of_mk_eq_mk`: two central division algebras representing
  the same class are isomorphic over the base field.
* `TauCeti.BrauerGroup.isBrauerEquivalent_iff_nonempty_algEquiv`: Brauer equivalence of two
  central division algebras is equivalent to the existence of that algebra isomorphism.

## References

This proves the “unique division-algebra representative” target in Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §2.4, and
R. S. Pierce, *Associative Algebras*, Chapter 12.
-/

public section

namespace TauCeti

universe u v

namespace BrauerGroup

variable (K : Type u) [Field K]

/-- **Every Brauer class has a central division-algebra representative.** More precisely, for
every `x : BrauerGroup K` there is a finite-dimensional central division `K`-algebra `D` whose
Brauer class is `x`.

The representative is not chosen as data: the theorem records its existence, while
`TauCeti.BrauerGroup.nonempty_algEquiv_of_mk_eq_mk` says that any two choices are isomorphic over
`K`. -/
theorem exists_eq_mk_centralDivisionRing (x : BrauerGroup.{u, v} K) :
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra K D) (_ : Algebra.IsCentral K D)
      (_ : FiniteDimensional K D), x = mk (CSA.of K D) := by
  induction x using BrauerGroup.inductionOn with
  | _ A =>
      obtain ⟨n, hn, D, hD, hDalg, hDcentral, hDfinite, -, ⟨e⟩⟩ :=
        IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
      let _ : DivisionRing D := hD
      let _ : Algebra K D := hDalg
      let _ : Algebra.IsCentral K D := hDcentral
      let _ : FiniteDimensional K D := hDfinite
      refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      calc
        mk A = mk (CSA.matrix (CSA.of K D) n) := mk_eq_mk_of_algEquiv e
        _ = mk (CSA.of K D) := mk_matrix (K := K) (CSA.of K D) n

variable {K}

/-- **Central division algebras in the same Brauer class are isomorphic over the base field.**

Equality of classes produces a Brauer equivalence, hence an algebra isomorphism between positive
matrix algebras over `D` and `E`. Algebra-linear Wedderburn uniqueness recovers an isomorphism of
the coefficient division algebras themselves. -/
theorem nonempty_algEquiv_of_mk_eq_mk
    {D E : Type v} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] [DivisionRing E] [Algebra K E] [Algebra.IsCentral K E]
    [FiniteDimensional K E]
    (h : mk (CSA.of K D) = mk (CSA.of K E)) : Nonempty (D ≃ₐ[K] E) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := mk_eq_mk_iff.mp h
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
  exact nonempty_algEquiv_of_algEquiv_matrix (K := K) (AlgEquiv.refl :
    Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin n) (Fin n) D) e

/-- **Two central division algebras are Brauer equivalent exactly when they are isomorphic as
algebras over the base field.**

The reverse implication is the general fact that algebra isomorphisms preserve Brauer classes;
the forward implication is the uniqueness of division-algebra representatives. -/
@[simp]
theorem isBrauerEquivalent_iff_nonempty_algEquiv
    {D E : Type v} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] [DivisionRing E] [Algebra K E] [Algebra.IsCentral K E]
    [FiniteDimensional K E] :
    IsBrauerEquivalent (CSA.of K D) (CSA.of K E) ↔ Nonempty (D ≃ₐ[K] E) :=
  ⟨fun h ↦ nonempty_algEquiv_of_mk_eq_mk (mk_eq_mk_iff.2 h),
    fun ⟨e⟩ ↦ IsBrauerEquivalent.of_algEquiv K e⟩

end BrauerGroup

end TauCeti
