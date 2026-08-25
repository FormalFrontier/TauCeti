/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.CentralSimple.TensorProduct` is imported publicly: its instances
-- `TauCeti.Algebra.IsCentral.tensorProduct` and `TauCeti.IsSimpleRing.tensorProduct` are two of the
-- three things that make `TauCeti.CSA.tensorProduct` well defined. It re-exports
-- `Mathlib.RingTheory.TensorProduct.Basic` (hence the `⊗[K]` notation),
-- `Mathlib.Algebra.Central.Basic` and `Mathlib.RingTheory.SimpleRing.Basic`, which is why none of
-- those is imported again here.
public import TauCeti.Algebra.CentralSimple.TensorProduct
-- The third is finite-dimensionality of `A ⊗[K] B`, Mathlib's `Module.Finite.tensorProduct`.
public import Mathlib.RingTheory.TensorProduct.Finite
-- `CSA`, `IsBrauerEquivalent` and `BrauerGroup` occur in the statements below. This also
-- re-exports `Mathlib.LinearAlgebra.Matrix.Reindex`, hence the reindexing `Matrix.reindexAlgEquiv`
-- used below, which is why that is not imported again here.
public import Mathlib.Algebra.BrauerGroup.Defs
-- The two matrix instances appear in the statements below, through `TauCeti.CSA.matrix`: they are
-- what bundles `Mₙ(A)` as a term of `CSA K`.
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.RingTheory.SimpleRing.Matrix
-- Mathlib's Kronecker product of matrix algebras is the body of
-- `TauCeti.Matrix.kroneckerTMulFinAlgEquiv`, and a compiled definition may not refer to a
-- privately imported one, so this import is public too. It re-exports
-- `Mathlib.Data.Matrix.Composition` and `Mathlib.RingTheory.TensorProduct.Maps`, hence the two
-- further equivalences used in the proofs below, `Matrix.compAlgEquiv` and
-- `Algebra.TensorProduct.congr`, which is why neither is imported again here.
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Brauer equivalence: bundling central simple algebras, matrices, and the tensor product

Two finite-dimensional central simple `K`-algebras are **Brauer equivalent** when they become
isomorphic after passing to matrix algebras over them: `IsBrauerEquivalent A B` is Mathlib's
`∃ n m ≠ 0, Mₙ(A) ≃ₐ[K] Mₘ(B)`. Mathlib defines this relation, checks that it is an equivalence
relation, and forms the quotient `BrauerGroup K` -- but the quotient carries no algebraic structure
yet, and nothing is on record for the relation to be fed: `CSA K` is a structure over `AlgCat K`,
so its constructor takes a bundled object rather than an algebra, and Mathlib names no member of
it -- not even `Mₙ(A)`.

This file supplies the working API. It builds the constructors that the theory needs
(`TauCeti.CSA.of`, and on top of it `TauCeti.CSA.base`, `TauCeti.CSA.matrix` and
`TauCeti.CSA.tensorProduct`), records the two moves that leave a Brauer class unchanged -- an
isomorphism of algebras, and passage to matrices over the algebra -- and proves that the tensor
product respects Brauer equivalence, so that it descends to `BrauerGroup K`.

The group law itself is deliberately not installed here. Multiplication, commutativity,
associativity and the identity are all available from the statements below, but the inverse is not:
it rests on the separate opposite isomorphism `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] M_{finrank K A}(K)`, which belongs
to the theory of the Azumaya map rather than to the Brauer-equivalence bookkeeping done here.
Installing a monoid structure now, to replace it by a group structure later, would only create
work; so `BrauerGroup K` is left as Mathlib's bare quotient. Which algebras are in the identity
class is the subject of `TauCeti/Algebra/BrauerGroup/Trivial.lean`, which builds on this file.

## Matrix absorption

The one genuine computation is `Mₘ(A) ⊗[K] Mₙ(B) ≃ₐ[K] M_{mn}(A ⊗[K] B)`. It is not proved here:
it is Mathlib's Kronecker product of matrix algebras, `Matrix.kroneckerTMulAlgEquiv`, whose target
is indexed by `Fin m × Fin n`, transported along `finProdFinEquiv` to the `Fin (m * n)` indexing
that `IsBrauerEquivalent` is stated in. Since neither central simplicity nor positivity of the
sizes enters, it is stated in that generality first, as
`TauCeti.Matrix.kroneckerTMulFinAlgEquiv`, over any commutative semiring and any two algebras
over it; `TauCeti.CSA.tensorProductMatrixAlgEquiv` is the bundled `CSA` reading that Brauer
equivalence consumes. Everything about the tensor product below is a consequence of it and of the
transport `Algebra.TensorProduct.congr`.

## Universes

`CSA.{u, v} K` places the algebra in a universe `v` of its own, and `IsBrauerEquivalent` compares
two algebras in the *same* `v`. The general lemmas below are therefore stated for an arbitrary `v`,
but every statement mentioning the base field -- `TauCeti.CSA.base`, and so
`TauCeti.isBrauerEquivalent_tensorProduct_base` -- needs `v = u`, since `K : Type u` cannot be
moved. This is not a restriction in practice: `BrauerGroup K` is the interesting object at `v = u`.

## Main definitions

* `TauCeti.CSA.of`: an algebra with the three central-simple instances, as a term of `CSA K`;
  `TauCeti.CSA.base K` is `K` itself.
* `TauCeti.CSA.matrix A n` and `TauCeti.CSA.tensorProduct A B`: `Mₙ(A)` and `A ⊗[K] B` as terms
  of `CSA K`. The underlying type of each is the expected one by definition.
* `TauCeti.Matrix.kroneckerTMulFinAlgEquiv`: matrix absorption
  `Mₘ(A) ⊗[R] Mₙ(B) ≃ₐ[R] M_{mn}(A ⊗[R] B)` for arbitrary algebras and sizes, and
  `TauCeti.CSA.tensorProductMatrixAlgEquiv`, its bundled `CSA` reading.

## Main results

* `TauCeti.IsBrauerEquivalent.of_algEquiv` and `TauCeti.isBrauerEquivalent_matrix`: the two moves
  that leave a Brauer class unchanged -- an isomorphism of algebras, and passage to matrices over
  the algebra. The second is the reason `IsBrauerEquivalent` is coarser than isomorphism, and it is
  what makes the Brauer class of a split algebra the identity.
* `TauCeti.isBrauerEquivalent_tensorProduct_congr`: **the tensor product respects Brauer
  equivalence**, so it descends to `BrauerGroup K`. With
  `TauCeti.isBrauerEquivalent_tensorProduct_comm`,
  `TauCeti.isBrauerEquivalent_tensorProduct_assoc` and
  `TauCeti.isBrauerEquivalent_tensorProduct_base` this is the commutative-monoid half of the group
  law.

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

namespace CSA

/-- A finite-dimensional central simple `K`-algebra, bundled as a term of Mathlib's `CSA K`.

Mathlib's `CSA K` carries its algebra as an `AlgCat K` together with three instance fields; this
is the constructor turning the unbundled hypotheses used everywhere else into that bundling. It is
an `abbrev` so that the carrier of `TauCeti.CSA.of K A` is reducibly `A`, and instances stated for
`A` are found for it. -/
abbrev of (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] : CSA.{u, v} K where
  toAlgCat := AlgCat.of K A

theorem coe_of (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] : (of K A : Type v) = A :=
  rfl

/-- The base field as a central simple algebra over itself. This is the Brauer class of the split
algebras, and the intended identity of `BrauerGroup K`. -/
abbrev base : CSA.{u, u} K := of K K

variable {K}

/-- The `n × n` matrices over a central simple `K`-algebra, again a central simple `K`-algebra.
Brauer equivalence is exactly the relation that identifies this with `A`
(`TauCeti.isBrauerEquivalent_matrix`). -/
abbrev matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] : CSA.{u, v} K :=
  of K (Matrix (Fin n) (Fin n) A)

/-- The tensor product of two central simple `K`-algebras, again a central simple `K`-algebra by
`TauCeti.Algebra.IsCentral.tensorProduct` and `TauCeti.IsSimpleRing.tensorProduct`. This is the
operation that descends to the group law on `BrauerGroup K`
(`TauCeti.isBrauerEquivalent_tensorProduct_congr`). -/
abbrev tensorProduct (A B : CSA.{u, v} K) : CSA.{u, v} K :=
  of K (A ⊗[K] B)

end CSA

/-! ### The two moves that preserve a Brauer class -/

/-- **An isomorphism of algebras is a Brauer equivalence**: take one-by-one matrices on both
sides. -/
theorem IsBrauerEquivalent.of_algEquiv {A B : CSA.{u, v} K} (e : A ≃ₐ[K] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix (m := Fin 1)⟩⟩

/-- **Passing to matrices does not change the Brauer class.** This is the move making Brauer
equivalence strictly coarser than isomorphism -- `Mₙ(A)` and `A` are almost never isomorphic, their
dimensions differing by a factor of `n ^ 2` -- and it is why `Mₙ(K)` will be the identity class: it
is `Mₙ` of the identity algebra.

The witness is the smallest one available, `M₁(Mₙ(A)) ≃ₐ Mₙ(A)`, which is `Matrix.compAlgEquiv`
followed by the reindexing `Fin 1 × Fin n ≃ Fin n`. -/
theorem isBrauerEquivalent_matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    IsBrauerEquivalent (CSA.matrix A n) A :=
  ⟨1, n, one_ne_zero, NeZero.ne n,
    ⟨(Matrix.compAlgEquiv (Fin 1) (Fin n) A K).trans
      (Matrix.reindexAlgEquiv K A (finProdFinEquiv.trans (finCongr (one_mul n))))⟩⟩

/-- Matrix algebras over Brauer equivalent algebras are Brauer equivalent, in any two sizes. -/
theorem isBrauerEquivalent_matrix_congr {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B)
    (m n : ℕ) [NeZero m] [NeZero n] :
    IsBrauerEquivalent (CSA.matrix A m) (CSA.matrix B n) :=
  ((isBrauerEquivalent_matrix K A m).trans h).trans (isBrauerEquivalent_matrix K B n).symm

/-! ### Matrix absorption -/

/-- **Matrix absorption**: `Mₘ(A) ⊗[R] Mₙ(B) ≃ₐ[R] M_{mn}(A ⊗[R] B)`, over any commutative
semiring `R` and any two `R`-algebras, in any two sizes.

Neither central simplicity nor positivity of the sizes plays any part, so neither is assumed;
`TauCeti.CSA.tensorProductMatrixAlgEquiv` is the bundled reading that Brauer equivalence
consumes. -/
def Matrix.kroneckerTMulFinAlgEquiv (m n : ℕ) (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [Algebra R A] (B : Type*) [Semiring B] [Algebra R B] :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) B ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) (A ⊗[R] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) R R A B).trans
    (Matrix.reindexAlgEquiv R _ finProdFinEquiv)

variable {K}

/-- **Matrix absorption** for central simple algebras:
`Mₘ(A) ⊗[K] Mₙ(B) ≃ₐ[K] M_{mn}(A ⊗[K] B)` as an isomorphism of terms of `CSA K`. This is
`TauCeti.Matrix.kroneckerTMulFinAlgEquiv`, read through the constructors `TauCeti.CSA.matrix` and
`TauCeti.CSA.tensorProduct`, whose underlying types are the expected ones by definition. -/
def CSA.tensorProductMatrixAlgEquiv (A B : CSA.{u, v} K) (m n : ℕ) [NeZero m] [NeZero n] :
    CSA.tensorProduct (CSA.matrix A m) (CSA.matrix B n) ≃ₐ[K]
      CSA.matrix (CSA.tensorProduct A B) (m * n) :=
  Matrix.kroneckerTMulFinAlgEquiv m n K A B

variable (K)

/-! ### The tensor product of Brauer classes -/

/-- **The tensor product respects Brauer equivalence**, so it descends to a binary operation on
`BrauerGroup K`. -/
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
  IsBrauerEquivalent.of_algEquiv K (Algebra.TensorProduct.comm K A B)

/-- The tensor product of central simple algebras is associative up to Brauer equivalence -- indeed
up to isomorphism, by `Algebra.TensorProduct.assoc`. -/
theorem isBrauerEquivalent_tensorProduct_assoc (A B C : CSA.{u, v} K) :
    IsBrauerEquivalent (CSA.tensorProduct (CSA.tensorProduct A B) C)
      (CSA.tensorProduct A (CSA.tensorProduct B C)) :=
  IsBrauerEquivalent.of_algEquiv K (Algebra.TensorProduct.assoc K K K A B C)

/-- The base field is the identity for the tensor product, up to Brauer equivalence -- indeed up to
isomorphism, by `Algebra.TensorProduct.rid`. -/
theorem isBrauerEquivalent_tensorProduct_base (A : CSA.{u, u} K) :
    IsBrauerEquivalent (CSA.tensorProduct A (CSA.base K)) A :=
  IsBrauerEquivalent.of_algEquiv K (Algebra.TensorProduct.rid K K A)

end TauCeti
