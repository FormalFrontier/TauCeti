/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Subalgebra.Center
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- `FiniteDimensional` is a hypothesis of, and a conclusion of, the presentation results below.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: `Matrix.entryLinearMap` is used only inside a proof, to exhibit a coefficient algebra
-- as a linear quotient of its matrix block, and `Module.finrank_pos` together with
-- `LinearMap.finrank_le_finrank_of_surjective` only to bound a block from below by the dimension of
-- its coefficients and from above by that of the algebra presented.
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite products of matrix algebras

The dimension and the center of a product `Π i, Matₙᵢ(k)` of matrix algebras over a field, both
read off the sizes `nᵢ` alone, together with the dimensions that an algebra equivalence
`A ≃ₐ[k] ∏ᵢ Matₙᵢ(Dᵢ)` onto such a product — over an arbitrary family of coefficient algebras
`Dᵢ` — transports back to the algebra `A` presented. Such a product is what a structure theorem of
Artin--Wedderburn type presents an algebra as, and these are the invariants such a presentation
transports; nothing here needs the presentation to come from Artin--Wedderburn, nor the
coefficients to be division algebras.

* `TauCeti.finrank_pi_matrix`: the dimension of the product is `∑ᵢ nᵢ²`;
* `TauCeti.centerPiMatrixAlgEquiv`: when every size is nonzero the center consists of the tuples of
  scalar matrices, so it is the algebra `ι → k` of functions on the index, whose dimension is the
  number of factors (`TauCeti.finrank_center_pi_matrix`);
* `TauCeti.finiteDimensional_of_algEquiv_pi_matrix`: the coefficient algebra of a block of *nonzero*
  size in a presentation of a finite-dimensional algebra is itself finite-dimensional. A block of
  size `0` is the zero ring whatever its coefficients are, so it constrains them not at all: the
  positivity hypothesis is essential rather than an artefact of the proof;
* `TauCeti.finrank_eq_sum_sq_finrank`: **the dimension count** `finrank k A = ∑ᵢ nᵢ² · finrank k Dᵢ`
  for an algebra presented as `∏ᵢ Matₙᵢ(Dᵢ)`. The count itself needs no positivity: a block of size
  `0` contributes `0` to both sides;
* `TauCeti.sq_le_finrank_of_algEquiv_pi_matrix` and `TauCeti.card_le_finrank_of_algEquiv_pi_matrix`:
  the bounds `nᵢ² ≤ finrank k A` on the degree of a single block with nontrivial coefficients — no
  other block plays any part, so the index need not even be finite — and, when every block is
  nonzero over nontrivial coefficients, `Nat.card ι ≤ finrank k A` on the number of blocks.

## References

The dimension count implements the Layer 2 target "the dimension count" of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `finrank_eq_sum_sq_finrank`; its algebraically closed form lives in
`TauCeti/RingTheory/Semisimple/DimensionCount.lean`. See C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §25, or T. Y. Lam, *A First
Course in Noncommutative Rings*, §3.
-/

public section

namespace TauCeti

open scoped BigOperators

variable (k : Type*) [Field k] {ι : Type*} (d : ι → ℕ)

/-- The center of a product of nonzero matrix algebras over a field consists of the tuples of
scalar matrices, so it is the algebra of functions on the index. -/
noncomputable def centerPiMatrixAlgEquiv [∀ i, NeZero (d i)] :
    Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) ≃ₐ[k] (ι → k) :=
  centerPiAlgEquiv.trans (AlgEquiv.piCongrRight fun i =>
    haveI : Nonempty (Fin (d i)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (d i)))
    centerAlgEquivOfIsCentral k _)

/-- `centerPiMatrixAlgEquiv` reads off the scalar of each component: the `i`-th component of a
central tuple is the scalar matrix on the `i`-th value of the corresponding function. -/
@[simp]
theorem algebraMap_centerPiMatrixAlgEquiv_apply [∀ i, NeZero (d i)]
    (x : Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) (i : ι) :
    algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (centerPiMatrixAlgEquiv k d x i) =
      (x : Π i, Matrix (Fin (d i)) (Fin (d i)) k) i := by
  simp [centerPiMatrixAlgEquiv]

/-- The inverse of `centerPiMatrixAlgEquiv` assembles a function on the index into the tuple of the
corresponding scalar matrices. -/
@[simp]
theorem centerPiMatrixAlgEquiv_symm_apply_coe [∀ i, NeZero (d i)] (f : ι → k) (i : ι) :
    ((centerPiMatrixAlgEquiv k d).symm f : Π i, Matrix (Fin (d i)) (Fin (d i)) k) i =
      algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (f i) := by
  simp [centerPiMatrixAlgEquiv]

section FiniteIndex

variable [Fintype ι]

/-- The dimension of a finite product of matrix algebras is the sum of the squares of the sizes. -/
theorem finrank_pi_matrix :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) = ∑ i, d i ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix]
  simp [sq]

/-- The center of a finite product of nonzero matrix algebras over a field has dimension the number
of factors. -/
theorem finrank_center_pi_matrix [∀ i, NeZero (d i)] :
    Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) =
      Fintype.card ι := by
  rw [(centerPiMatrixAlgEquiv k d).toLinearEquiv.finrank_eq, Module.finrank_pi]

end FiniteIndex

/-! ### Dimensions read off a presentation -/

section Presentation

variable {d : ι → ℕ} {A : Type*} [Ring A] [Algebra k A] {D : ι → Type*} [∀ i, Ring (D i)]
  [∀ i, Algebra k (D i)]

section Blocks

variable [FiniteDimensional k A] (e : A ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))

include e

/-- A matrix block of a presentation of a finite-dimensional algebra as a product of matrix algebras
is finite-dimensional: it is a direct factor, hence a linear quotient, of the algebra. -/
private theorem finiteDimensional_matrix_of_algEquiv_pi_matrix (i : ι) :
    FiniteDimensional k (Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have : Module.Finite k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.of_surjective _ (LinearMap.proj_surjective (R := k)
    (φ := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i)

/-- The coefficient algebra of a block of nonzero size in a presentation of a finite-dimensional
algebra as a product of matrix algebras is itself finite-dimensional, so no such presentation can
smuggle an infinite-dimensional coefficient algebra into a nonzero block.

The positivity hypothesis `NeZero (d i)` is essential and not an artefact of the proof: a block of
size `0` is the zero ring whatever its coefficients are, so it constrains `D i` not at all. Every
Artin--Wedderburn presentation supplies that positivity. -/
theorem finiteDimensional_of_algEquiv_pi_matrix (i : ι) [NeZero (d i)] :
    FiniteDimensional k (D i) := by
  have := finiteDimensional_matrix_of_algEquiv_pi_matrix k e i
  obtain ⟨j⟩ : Nonempty (Fin (d i)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (d i)))
  exact Module.Finite.of_surjective (Matrix.entryLinearMap k (D i) j j)
    fun x => ⟨Matrix.of fun _ _ => x, rfl⟩

end Blocks

section Count

variable [Fintype ι] [FiniteDimensional k A]

/-- **The Wedderburn dimension count.** If a finite-dimensional `k`-algebra `A` is presented as a
finite product `∏ᵢ Matₙᵢ(Dᵢ)` of matrix algebras, then `finrank k A = ∑ᵢ nᵢ² · finrank k Dᵢ`.

No positivity is needed: a block of size `0` contributes `0` to both sides, whatever its
coefficients are. Only the presentation is used: `A` is not assumed semisimple, although by
`RingEquiv.isSemisimpleRing` it is one as soon as the coefficients `Dᵢ` are division algebras. -/
theorem finrank_eq_sum_sq_finrank (e : A ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    Module.finrank k A = ∑ i, d i ^ 2 * Module.finrank k (D i) := by
  have : ∀ i, Module.Finite k (Matrix (Fin (d i)) (Fin (d i)) (D i)) := fun i =>
    finiteDimensional_matrix_of_algEquiv_pi_matrix k e i
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix, Fintype.card_fin, sq]

end Count

section Bounds

variable [FiniteDimensional k A] (e : A ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))

include e

/-- **The degree of a block is bounded by the dimension**: `nᵢ² ≤ finrank k A` for a block with
nontrivial coefficients in a presentation of a finite-dimensional algebra by matrix algebras.

Only the block `i` takes part: the bound reads off the surjection of `A` onto that block alone, so
neither the other coefficient algebras nor the finiteness of the index are assumed. -/
theorem sq_le_finrank_of_algEquiv_pi_matrix (i : ι) [Nontrivial (D i)] :
    d i ^ 2 ≤ Module.finrank k A := by
  rcases eq_or_ne (d i) 0 with h | h
  · simp [h]
  · have : NeZero (d i) := ⟨h⟩
    have := finiteDimensional_of_algEquiv_pi_matrix k e i
    calc d i ^ 2 ≤ d i ^ 2 * Module.finrank k (D i) :=
          Nat.le_mul_of_pos_right _ (Module.finrank_pos (R := k) (M := D i))
      _ = Module.finrank k (Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
          rw [Module.finrank_matrix, Fintype.card_fin, sq]
      _ ≤ Module.finrank k A :=
          LinearMap.finrank_le_finrank_of_surjective
            (f := (LinearMap.proj (R := k) (φ := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i)
              ∘ₗ (e.toLinearEquiv : A →ₗ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)))
            ((LinearMap.proj_surjective (R := k)
              (φ := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i).comp
              e.toLinearEquiv.surjective)

/-- **The number of blocks is bounded by the dimension**: a finite-dimensional algebra presented by
nonzero matrix blocks over nontrivial coefficients has at most `finrank k A` of them.

For the group algebra of a finite group over a splitting field this bounds the number of irreducible
representations by the order of the group. -/
theorem card_le_finrank_of_algEquiv_pi_matrix [Finite ι] [∀ i, NeZero (d i)]
    [∀ i, Nontrivial (D i)] : Nat.card ι ≤ Module.finrank k A := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [finrank_eq_sum_sq_finrank k e, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun i _ => ?_
  have := finiteDimensional_of_algEquiv_pi_matrix k e i
  exact Nat.one_le_iff_ne_zero.mpr <| Nat.mul_ne_zero (pow_ne_zero 2 (NeZero.ne (d i)))
    (Module.finrank_pos (R := k) (M := D i)).ne'

end Bounds

end Presentation

end TauCeti
