/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.TensorProduct` is imported publicly: the scalar extension
-- `L ⊗[K] A` appears in the statements below, and it is the simplicity instance
-- `TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` proved there that makes those statements
-- provable. It also re-exports `Mathlib.RingTheory.TensorProduct.Basic` (hence the `⊗[K]`
-- notation and the algebra structure on `L ⊗[K] A`) and `Mathlib.Algebra.Central.Basic`, which is
-- why neither is imported again here.
public import TauCeti.Algebra.CentralSimple.TensorProduct
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- Non-public: `AlgebraicClosure` and Mathlib's algebraically closed Wedderburn-Artin theorem are
-- used only inside proofs, and the complex numbers and the real quaternions only by the worked
-- examples at the end of the file (`TauCeti.Algebra.Central.Quaternion` re-exports
-- `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation there).
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import TauCeti.Algebra.Central.Quaternion

/-!
# The degree of a central simple algebra

A finite-dimensional central simple algebra has square dimension over its base field. This file
proves that, and defines the **degree** `TauCeti.Algebra.deg K A` as the square root of
`Module.finrank K A`.

The proof is the base-change one, and it needs no theory of maximal subfields. Let `L / K` be a
field extension with `L` algebraically closed. Then `L ⊗[K] A` is again simple, because `L` is a
simple `K`-algebra and `A` is central simple
(`TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right`); it is finite-dimensional over `L` of the
same dimension as `A` over `K` (`Module.finrank_baseChange`); so Mathlib's
`IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` writes it as `Matrix (Fin n) (Fin n) L`, whose
dimension is `n ^ 2`. Only simplicity of the scalar extension is used: the sharper statement that
`L ⊗[K] A` is central simple *over `L`* is not needed here, and is not proved.

Centrality of `A` over `K` is essential rather than decorative: `ℂ` is a simple, finite-dimensional
`ℝ`-algebra whose dimension `2` is not a perfect square. That negative control is checked at the end
of the file, alongside the real quaternions as the positive one.

The same argument says that an algebraically closed extension **splits** `A`, in `deg K A` rows and
columns; that is recorded as
`TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isAlgClosed`.

## Main results

* `TauCeti.IsSimpleRing.exists_algEquiv_matrix_baseChange_of_isAlgClosed`: an algebraically closed
  extension `L / K` splits a finite-dimensional central simple `K`-algebra `A`, and the matrix size
  `n` satisfies `Module.finrank K A = n ^ 2`.
* `TauCeti.IsSimpleRing.isSquare_finrank`: **the dimension of a finite-dimensional central simple
  algebra is a perfect square**.
* `TauCeti.Algebra.deg`: the degree of a central simple algebra, with
  `TauCeti.Algebra.deg_sq : deg K A ^ 2 = Module.finrank K A`, its multiplicativity
  `TauCeti.Algebra.deg_tensorProduct` and `TauCeti.Algebra.deg_matrix`, the reading
  `TauCeti.Algebra.deg_eq_mul_deg_of_algEquiv_matrix` off a Wedderburn presentation, and the
  splitting `TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isAlgClosed` restated with
  matrix size `deg K A`.

## Implementation notes

`TauCeti.Algebra.deg` is defined for every `K`-algebra, as `Nat.sqrt (Module.finrank K A)`, the way
`Module.finrank` is defined for every module: outside the central simple case the value is junk and
no lemma below claims otherwise. Its characteristic property is
`TauCeti.Algebra.deg_eq_of_finrank_eq_sq`, which needs no hypotheses on `A` beyond the square
dimension it is handed; every other lemma about `deg` here is derived from it, so the definition is
never unfolded downstream.

`TauCeti.IsSimpleRing.isSquare_finrank` subsumes the finite-base-field
`TauCeti.IsSimpleRing.isSquare_finrank_of_finite` of
`TauCeti/Algebra/CentralSimple/Wedderburn.lean`, which is left in place: its elementary proof runs
through little Wedderburn rather than an algebraic closure, and it sits with the finite-field
structure theorem
`TauCeti.IsSimpleRing.exists_algEquiv_matrix_of_finite` that it is read off.

## References

This implements the third bullet of Layer 4 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md)
(square dimension by base change to the algebraic closure, and the degree defined as its square
root). See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.4, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-! ### Splitting by an algebraically closed extension -/

namespace IsSimpleRing

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **An algebraically closed extension splits a central simple algebra.** If `L / K` is a field
extension with `L` algebraically closed and `A` is a finite-dimensional central simple `K`-algebra,
then `L ⊗[K] A` is a full matrix algebra over `L`, and its size `n` records the dimension of `A` as
`Module.finrank K A = n ^ 2`.

Centrality of `A` over `K` is what makes the scalar extension simple; simplicity of `A` alone does
not suffice. The standard witness is `A = ℂ` over `K = ℝ`, whose scalar extension `ℂ ⊗[ℝ] ℂ` is a
product of two copies of `ℂ`; the shadow of that failure which is checked in this file is that
`Module.finrank ℝ ℂ = 2` is not a perfect square. -/
theorem exists_algEquiv_matrix_baseChange_of_isAlgClosed [IsAlgClosed L] :
    ∃ (n : ℕ) (_ : NeZero n), Module.finrank K A = n ^ 2 ∧
      Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := _root_.IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed L (L ⊗[K] A)
  refine ⟨n, hn, ?_, ⟨e⟩⟩
  rw [← Module.finrank_baseChange (R := L) (S := K) (M' := A), e.toLinearEquiv.finrank_eq,
    Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]

/-- **The dimension of a finite-dimensional central simple algebra is a perfect square.**

Base change to an algebraic closure of `K` splits `A`, and a full matrix algebra has square
dimension. Centrality cannot be dropped: `Module.finrank ℝ ℂ = 2`. -/
theorem isSquare_finrank : IsSquare (Module.finrank K A) := by
  obtain ⟨n, -, hrank, -⟩ :=
    exists_algEquiv_matrix_baseChange_of_isAlgClosed K (AlgebraicClosure K) A
  exact ⟨n, by rw [hrank, sq]⟩

end IsSimpleRing

/-! ### The degree -/

namespace Algebra

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]

/-- The **degree** of a central simple `K`-algebra `A`: the square root of `Module.finrank K A`,
which is a perfect square by `TauCeti.IsSimpleRing.isSquare_finrank`. Equivalently, the size of the
matrix algebra that `A` becomes over an algebraically closed extension of `K`
(`TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isAlgClosed`).

This is defined for an arbitrary `K`-algebra, and takes a junk value unless `A` is central simple;
`TauCeti.Algebra.deg_eq_of_finrank_eq_sq` is the characteristic property. -/
noncomputable def deg : ℕ := Nat.sqrt (Module.finrank K A)

variable {K A}

/-- The characteristic property of the degree: a `K`-algebra of dimension `n ^ 2` has degree `n`.
Every other lemma about `TauCeti.Algebra.deg` is derived from this one. -/
theorem deg_eq_of_finrank_eq_sq {n : ℕ} (h : Module.finrank K A = n ^ 2) : deg K A = n := by
  rw [deg, h, Nat.sqrt_eq']

/-- Two isomorphic `K`-algebras have the same degree. -/
theorem deg_eq_of_algEquiv {B : Type*} [Ring B] [Algebra K B] (e : A ≃ₐ[K] B) :
    deg K A = deg K B := by
  rw [deg, deg, e.toLinearEquiv.finrank_eq]

variable (K A)

@[simp]
theorem deg_self : deg K K = 1 :=
  deg_eq_of_finrank_eq_sq (by simp)

section CentralSimple

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- The dimension of a central simple algebra is the square of its degree. -/
@[simp]
theorem deg_sq : deg K A ^ 2 = Module.finrank K A := by
  obtain ⟨n, hn⟩ := IsSimpleRing.isSquare_finrank K A
  rw [deg_eq_of_finrank_eq_sq (n := n) (by rw [hn, sq]), hn, sq]

/-- A central simple algebra is nonzero, so its degree is. -/
theorem deg_ne_zero : deg K A ≠ 0 := fun h =>
  Module.finrank_pos.ne' (by rw [← deg_sq K A, h, zero_pow two_ne_zero])

/-- A central simple algebra has positive degree. -/
theorem deg_pos : 0 < deg K A :=
  Nat.pos_of_ne_zero (deg_ne_zero K A)

/-- The degree is multiplicative under tensor product: this is the degree-level shadow of the fact
that central simple `K`-algebras are closed under `⊗[K]`. -/
theorem deg_tensorProduct (B : Type*) [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] [FiniteDimensional K B] :
    deg K (A ⊗[K] B) = deg K A * deg K B :=
  deg_eq_of_finrank_eq_sq <| by
    rw [Module.finrank_tensorProduct, ← deg_sq K A, ← deg_sq K B]; ring

/-- Passing to `n × n` matrices multiplies the degree by `n`. -/
theorem deg_matrix (n : ℕ) : deg K (Matrix (Fin n) (Fin n) A) = n * deg K A :=
  deg_eq_of_finrank_eq_sq <| by
    rw [Module.finrank_matrix, Fintype.card_fin, ← deg_sq K A]; ring

end CentralSimple

variable {K A}

/-- The degree read off a matrix presentation: if `A` is `n × n` matrices over a central simple
`K`-algebra `D` then `deg K A = n * deg K D`. Fed the central division algebra `D` of
`TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`, this is the degree of a
Wedderburn presentation; note that `A` itself carries no hypotheses here, since they are inherited
through the isomorphism. -/
theorem deg_eq_mul_deg_of_algEquiv_matrix {n : ℕ} {D : Type*} [Ring D] [Algebra K D]
    [Algebra.IsCentral K D] [IsSimpleRing D] [FiniteDimensional K D]
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) : deg K A = n * deg K D := by
  rw [deg_eq_of_algEquiv e, deg_matrix]

end Algebra

namespace IsSimpleRing

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L]
  (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- An algebraically closed extension `L / K` splits a finite-dimensional central simple
`K`-algebra `A` into matrices of size exactly `TauCeti.Algebra.deg K A`. -/
theorem nonempty_algEquiv_matrix_baseChange_of_isAlgClosed :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (Algebra.deg K A)) (Fin (Algebra.deg K A)) L) := by
  obtain ⟨n, -, hrank, he⟩ := exists_algEquiv_matrix_baseChange_of_isAlgClosed K L A
  rwa [Algebra.deg_eq_of_finrank_eq_sq hrank]

end IsSimpleRing

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

variable (K : Type*) [Field K] (n : ℕ)

/-- A full matrix algebra has degree its size. -/
example : Algebra.deg K (Matrix (Fin n) (Fin n) K) = n := by
  rw [Algebra.deg_matrix, Algebra.deg_self, mul_one]

/-- The real quaternions are a central division algebra of degree `2`. -/
example : Algebra.deg ℝ ℍ[ℝ] = 2 :=
  Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)

/-- The perfect-square theorem applies to the real quaternions: all three of `Algebra.IsCentral`,
`IsSimpleRing` and `FiniteDimensional` are found by instance search. -/
example : IsSquare (Module.finrank ℝ ℍ[ℝ]) := IsSimpleRing.isSquare_finrank ℝ ℍ[ℝ]

/-- The negative control for `TauCeti.IsSimpleRing.isSquare_finrank`: `ℂ` is a simple,
finite-dimensional `ℝ`-algebra of dimension `2`, which is not a perfect square. So centrality is
doing real work in that theorem; `ℂ` is exactly the `ℝ`-algebra it excludes. -/
example : ¬ IsSquare (Module.finrank ℝ ℂ) := by
  rw [Complex.finrank_real_complex]
  exact Nat.prime_two.prime.not_isSquare

end Examples

end TauCeti
