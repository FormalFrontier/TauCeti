/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.End` is imported publicly: its two instances are what let
-- `CSA.of K (Module.End K V)` elaborate in the statement of
-- `TauCeti.isBrauerEquivalent_moduleEnd_base`. It re-exports `TauCeti.Algebra.CentralSimple.Degree`
-- and hence `TauCeti.Algebra.CentralSimple.TensorProduct`, whose instances
-- `TauCeti.Algebra.IsCentral.tensorProduct` and `TauCeti.IsSimpleRing.tensorProduct` make
-- `TauCeti.CSA.tensorProduct` well defined, together with `Mathlib.RingTheory.TensorProduct.Basic`
-- (hence the `⊗[K]` notation), `Mathlib.Algebra.Central.Basic` and
-- `Mathlib.RingTheory.SimpleRing.Basic`, which is why none of those is imported again here.
public import TauCeti.Algebra.CentralSimple.End
public import Mathlib.Algebra.BrauerGroup.Defs
-- The two matrix instances appear in the statements below, through `TauCeti.CSA.matrix` and
-- through `CSA.of K (Matrix (Fin n) (Fin n) K)`.
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.RingTheory.SimpleRing.Matrix
-- Non-public: the four algebra isomorphisms doing the work occur only in proofs and in the body of
-- `TauCeti.CSA.tensorProductMatrixAlgEquiv` -- Mathlib's Kronecker product of matrix algebras, the
-- composition and reindexing equivalences of matrix algebras, and the matrix presentation
-- `algEquivMatrix` of an endomorphism algebra.
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Brauer equivalence: matrix algebras, split algebras, and the tensor product

Two finite-dimensional central simple `K`-algebras are **Brauer equivalent** when they become
isomorphic after passing to matrix algebras over them: `IsBrauerEquivalent A B` is Mathlib's
`∃ n m ≠ 0, Mₙ(A) ≃ₐ[K] Mₘ(B)`. Mathlib defines this relation, checks that it is an equivalence
relation, and forms the quotient `BrauerGroup K` -- but the quotient carries no algebraic structure
yet, and there is no way to feed the relation an algebra: `CSA K` is a bundled structure with no
constructor exported, so even `Mₙ(A)` is not available as a `CSA K`.

This file supplies the working API. It builds the three constructors that the theory needs
(`TauCeti.CSA.of`, `TauCeti.CSA.matrix`, `TauCeti.CSA.tensorProduct`, and the base field itself as
`TauCeti.CSA.base`), proves the two structural facts that make the eventual group law on
`BrauerGroup K` well defined -- passing to matrices does not change the Brauer class, and the
tensor product respects Brauer equivalence -- and identifies the **Brauer-trivial** algebras that
are the intended identity: a full matrix algebra over `K`, and the endomorphism algebra of a
nonzero finite-dimensional `K`-vector space.

The group law itself is deliberately not installed here. Multiplication, commutativity,
associativity and the identity are all available from the statements below, but the inverse is not:
it rests on the separate opposite isomorphism `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] M_{finrank K A}(K)`, which belongs
to the theory of the Azumaya map rather than to the Brauer-equivalence bookkeeping done here.
Installing a monoid structure now, to replace it by a group structure later, would only create
work; so `BrauerGroup K` is left as Mathlib's bare quotient.

## Matrix absorption

The one genuine computation is `TauCeti.CSA.tensorProductMatrixAlgEquiv`,
`Mₘ(A) ⊗[K] Mₙ(B) ≃ₐ[K] M_{mn}(A ⊗[K] B)`. It is not proved here: it is Mathlib's Kronecker
product of matrix algebras, `Matrix.kroneckerTMulAlgEquiv`, whose target is indexed by
`Fin m × Fin n`, transported along `finProdFinEquiv` to the `Fin (m * n)` indexing that
`IsBrauerEquivalent` is stated in. Everything about the tensor product below is a consequence of it
and of the transport `Algebra.TensorProduct.congr`.

## Universes

`CSA.{u, v} K` places the algebra in a universe `v` of its own, and `IsBrauerEquivalent` compares
two algebras in the *same* `v`. The general lemmas below are therefore stated for an arbitrary `v`,
but every statement mentioning the base field -- `TauCeti.CSA.base`, and so all of the
Brauer-triviality section -- needs `v = u`, since `K : Type u` cannot be moved. This is not a
restriction in practice: `BrauerGroup K` is the interesting object at `v = u`.

## Main definitions

* `TauCeti.CSA.of`: an algebra with the three central-simple instances, as an element of `CSA K`;
  `TauCeti.CSA.base K` is `K` itself.
* `TauCeti.CSA.matrix A n` and `TauCeti.CSA.tensorProduct A B`: `Mₙ(A)` and `A ⊗[K] B` as elements
  of `CSA K`. The underlying type of each is the expected one by definition.

## Main results

* `TauCeti.isBrauerEquivalent_matrix`: `Mₙ(A)` is Brauer equivalent to `A`. This is the
  reflexivity that the relation is designed for, and it is what makes the Brauer class of a split
  algebra the identity.
* `TauCeti.isBrauerEquivalent_tensorProduct_congr`: **the tensor product respects Brauer
  equivalence**, so it descends to `BrauerGroup K`. With
  `TauCeti.isBrauerEquivalent_tensorProduct_comm`,
  `TauCeti.isBrauerEquivalent_tensorProduct_assoc` and
  `TauCeti.isBrauerEquivalent_tensorProduct_base` this is the commutative-monoid half of the group
  law.
* `TauCeti.isBrauerEquivalent_base_of_nonempty_algEquiv_matrix`: **a split algebra is Brauer
  trivial**, with the two standard instances
  `TauCeti.isBrauerEquivalent_matrix_base` (`Mₙ(K)`) and
  `TauCeti.isBrauerEquivalent_moduleEnd_base` (`Module.End K V`).

## References

* [Semisimple algebras, Artin-Wedderburn, and the structure of their modules roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
  Layer 6, "Brauer-triviality prerequisites".
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.4.
* R. S. Pierce, *Associative Algebras*, Springer GTM 88 (1982), Chapter 12.
-/

public section

open scoped TensorProduct

universe u v

namespace TauCeti

variable (K : Type u) [Field K]

/-! ### Constructing central simple algebras -/

/-- A finite-dimensional central simple `K`-algebra, packaged as an element of Mathlib's `CSA K`.

Mathlib's `CSA K` bundles the carrier together with its three properties and exports no
constructor, so this is the way in. The underlying type of `CSA.of K A` is `A` by definition, and
the algebra structure on it is the given one, so an `A`-level isomorphism is a `CSA.of K A`-level
isomorphism with no glue. -/
@[expose]
def CSA.of (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] : CSA.{u, v} K where
  toAlgCat := AlgCat.of K A

/-- The base field as a central simple algebra over itself. This is the Brauer class of the split
algebras, and the intended identity of `BrauerGroup K`. -/
@[expose]
def CSA.base : CSA.{u, u} K := CSA.of K K

variable {K}

/-- The `n × n` matrices over a central simple `K`-algebra, again a central simple `K`-algebra.
Brauer equivalence is exactly the relation that identifies this with `A`
(`TauCeti.isBrauerEquivalent_matrix`). -/
@[expose]
def CSA.matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] : CSA.{u, v} K :=
  CSA.of K (Matrix (Fin n) (Fin n) A)

/-- The tensor product of two central simple `K`-algebras, again a central simple `K`-algebra by
`TauCeti.Algebra.IsCentral.tensorProduct` and `TauCeti.IsSimpleRing.tensorProduct`. This is the
operation that descends to the group law on `BrauerGroup K`
(`TauCeti.isBrauerEquivalent_tensorProduct_congr`). -/
@[expose]
def CSA.tensorProduct (A B : CSA.{u, v} K) : CSA.{u, v} K :=
  CSA.of K (A ⊗[K] B)

/-! ### Brauer equivalence -/

/-- Isomorphic central simple algebras are Brauer equivalent: take `1 × 1` matrices on both
sides. -/
theorem isBrauerEquivalent_of_nonempty_algEquiv {A B : CSA.{u, v} K}
    (e : Nonempty (A ≃ₐ[K] B)) : IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, e.map AlgEquiv.mapMatrix⟩

/-- **Passing to matrices does not change the Brauer class.** This is the whole point of the
relation, and the reason `IsBrauerEquivalent` is coarser than isomorphism: `Mₙ(A)` and `A` are
almost never isomorphic, their dimensions differing by a factor of `n ^ 2`. -/
theorem isBrauerEquivalent_matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    IsBrauerEquivalent (CSA.matrix A n) A :=
  ⟨1, n, one_ne_zero, NeZero.ne n, ⟨(Matrix.compAlgEquiv (Fin 1) (Fin n) A K).trans
    (Matrix.reindexAlgEquiv K A (finProdFinEquiv.trans (finCongr (one_mul n))))⟩⟩

/-- Matrix algebras over Brauer equivalent algebras are Brauer equivalent, in any two sizes. -/
theorem isBrauerEquivalent_matrix_congr {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B)
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsBrauerEquivalent (CSA.matrix A m) (CSA.matrix B n) :=
  ((isBrauerEquivalent_matrix A m).trans h).trans (isBrauerEquivalent_matrix B n).symm

/-- **Matrix absorption**: `Mₘ(A) ⊗[K] Mₙ(B) ≃ₐ[K] M_{mn}(A ⊗[K] B)`.

This is Mathlib's Kronecker product of matrix algebras, `Matrix.kroneckerTMulAlgEquiv`, whose
target is indexed by `Fin m × Fin n`, reindexed along `finProdFinEquiv` to the `Fin (m * n)`
indexing that `IsBrauerEquivalent` uses. Only that reindexing is done here; the algebra structure
on the Kronecker product is entirely Mathlib's. -/
def CSA.tensorProductMatrixAlgEquiv (A B : CSA.{u, v} K) (m n : ℕ) [NeZero m] [NeZero n] :
    CSA.tensorProduct (CSA.matrix A m) (CSA.matrix B n) ≃ₐ[K]
      CSA.matrix (CSA.tensorProduct A B) (m * n) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) K K A B).trans
    (Matrix.reindexAlgEquiv K _ finProdFinEquiv)

/-- **The tensor product respects Brauer equivalence**, so it descends to a binary operation on
`BrauerGroup K`.

The proof is matrix absorption twice over: `Mₘₙ(A ⊗ B) ≃ Mₘ(A) ⊗ Mₙ(B)`, which the hypotheses turn
into `Mₘ'(A') ⊗ Mₙ'(B') ≃ Mₘ'ₙ'(A' ⊗ B')`. -/
theorem isBrauerEquivalent_tensorProduct_congr {A A' B B' : CSA.{u, v} K}
    (hA : IsBrauerEquivalent A A') (hB : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (CSA.tensorProduct A B) (CSA.tensorProduct A' B') := by
  obtain ⟨m, m', hm, hm', ⟨eA⟩⟩ := hA
  obtain ⟨n, n', hn, hn', ⟨eB⟩⟩ := hB
  have : NeZero m := ⟨hm⟩
  have : NeZero m' := ⟨hm'⟩
  have : NeZero n := ⟨hn⟩
  have : NeZero n' := ⟨hn'⟩
  exact ⟨m * n, m' * n', Nat.mul_ne_zero hm hn, Nat.mul_ne_zero hm' hn',
    ⟨(CSA.tensorProductMatrixAlgEquiv A B m n).symm.trans
      ((Algebra.TensorProduct.congr eA eB).trans
        (CSA.tensorProductMatrixAlgEquiv A' B' m' n'))⟩⟩

/-- The tensor product of central simple algebras is commutative up to Brauer equivalence -- indeed
up to isomorphism, by `Algebra.TensorProduct.comm`. -/
theorem isBrauerEquivalent_tensorProduct_comm (A B : CSA.{u, v} K) :
    IsBrauerEquivalent (CSA.tensorProduct A B) (CSA.tensorProduct B A) :=
  isBrauerEquivalent_of_nonempty_algEquiv ⟨Algebra.TensorProduct.comm K A B⟩

/-- The tensor product of central simple algebras is associative up to Brauer equivalence -- indeed
up to isomorphism, by `Algebra.TensorProduct.assoc`. -/
theorem isBrauerEquivalent_tensorProduct_assoc (A B C : CSA.{u, v} K) :
    IsBrauerEquivalent (CSA.tensorProduct (CSA.tensorProduct A B) C)
      (CSA.tensorProduct A (CSA.tensorProduct B C)) :=
  isBrauerEquivalent_of_nonempty_algEquiv ⟨Algebra.TensorProduct.assoc K K K A B C⟩

/-! ### Brauer-trivial algebras

A central simple `K`-algebra is **split**, or **Brauer trivial**, when it is a full matrix algebra
over `K`. Over an algebraically closed field every central simple algebra is split; over a general
field the split algebras are exactly the class of `TauCeti.CSA.base K`, the identity of the
eventual group law. -/

/-- The base field is the identity for the tensor product, up to Brauer equivalence -- indeed up to
isomorphism, by `Algebra.TensorProduct.rid`. -/
theorem isBrauerEquivalent_tensorProduct_base (A : CSA.{u, u} K) :
    IsBrauerEquivalent (CSA.tensorProduct A (CSA.base K)) A :=
  isBrauerEquivalent_of_nonempty_algEquiv ⟨Algebra.TensorProduct.rid K K A⟩

/-- **A split central simple algebra is Brauer trivial.** -/
theorem isBrauerEquivalent_base_of_nonempty_algEquiv_matrix {A : CSA.{u, u} K} {n : ℕ} [NeZero n]
    (e : Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)) : IsBrauerEquivalent A (CSA.base K) :=
  (isBrauerEquivalent_of_nonempty_algEquiv (B := CSA.matrix (CSA.base K) n) e).trans
    (isBrauerEquivalent_matrix (CSA.base K) n)

variable (K) in
/-- **A full matrix algebra over `K` is Brauer trivial.** -/
theorem isBrauerEquivalent_matrix_base (n : ℕ) [NeZero n] :
    IsBrauerEquivalent (CSA.of K (Matrix (Fin n) (Fin n) K)) (CSA.base K) :=
  isBrauerEquivalent_base_of_nonempty_algEquiv_matrix ⟨AlgEquiv.refl⟩

variable (K) in
/-- **The endomorphism algebra of a nonzero finite-dimensional vector space is Brauer trivial.**
This is the form in which triviality is used: the identity class of `BrauerGroup K` contains
`Module.End K V`, so exhibiting an algebra as endomorphisms of a vector space exhibits its Brauer
class as trivial. -/
theorem isBrauerEquivalent_moduleEnd_base (V : Type u) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] :
    IsBrauerEquivalent (CSA.of K (Module.End K V)) (CSA.base K) :=
  have : NeZero (Module.finrank K V) := ⟨Module.finrank_pos.ne'⟩
  isBrauerEquivalent_base_of_nonempty_algEquiv_matrix ⟨algEquivMatrix (Module.finBasis K V)⟩

end TauCeti
