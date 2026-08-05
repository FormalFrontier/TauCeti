/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.Matrix.Pi` is imported publicly: it supplies `TauCeti.finrank_pi_matrix`, the
-- already split case of the count proved below, and it re-exports
-- `Mathlib.LinearAlgebra.Dimension.Constructions`, hence `Module.finrank` and the dimension
-- formulas `Module.finrank_pi_fintype` and `Module.finrank_matrix` that the proofs run on, as well
-- as the `Matrix` occurring in every statement here.
public import TauCeti.Algebra.Matrix.Pi
-- `IsSemisimpleRing` and Artin--Wedderburn appear in the existence statements below.
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
-- `IsAlgClosed` appears in the hypotheses of the split forms below.
public import Mathlib.FieldTheory.IsAlgClosed.Basic
-- Non-public: `TauCeti.nonempty_algEquiv_self_of_finiteDimensional_divisionRing` (the collapse of a
-- finite-dimensional division algebra over an algebraically closed field) and Mathlib's
-- algebraically closed form of Artin--Wedderburn are used only inside proofs, and
-- `Matrix.entryLinearMap` only to exhibit a coefficient algebra as a quotient of its matrix block,
-- so downstream importers do not pay for any of them.
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import TauCeti.RingTheory.Semisimple.Schur

/-!
# The Wedderburn dimension count

Artin--Wedderburn presents a finite-dimensional semisimple algebra `A` over a field `K` as a finite
product of matrix algebras `∏ᵢ Matₙᵢ(Dᵢ)` over division algebras. This file reads the dimension of
`A` off such a presentation,

`finrank K A = ∑ᵢ nᵢ² · finrank K Dᵢ`,

which over an algebraically closed field, where every `Dᵢ` collapses to the base field, becomes the
classical `finrank k A = ∑ᵢ nᵢ²`. Applied to a group algebra that last identity is the relation
`∑ᵢ nᵢ² = |G|` between the degrees of the irreducible representations of a finite group and its
order; `TauCeti/RepresentationTheory/CharacterTable/Wedderburn.lean` derives that special case from
`TauCeti.finrank_pi_matrix`, which this file generalizes away from the split case.

Nothing here needs the presentation to come from Artin--Wedderburn: an algebra equivalence
`A ≃ₐ[K] Π i, Matₙᵢ(Dᵢ)` onto *any* product of matrix algebras is enough, and the coefficients `Dᵢ`
need not be division algebras except where that is said. What finite-dimensionality of `A` buys is
that the blocks are then finite-dimensional too, which is
`TauCeti.finiteDimensional_of_algEquiv_pi_matrix`: no presentation can smuggle in an
infinite-dimensional coefficient algebra. A block of size `0` is the zero ring whatever its
coefficients are, so that statement is exactly where the positivity hypothesis `NeZero (d i)` — the
one Artin--Wedderburn always supplies — is needed.

Two counting consequences close the file: a single block satisfies `nᵢ² ≤ finrank K A`, and, when
every block is nonzero, there are at most `finrank K A` of them. For a group algebra over a
splitting field the latter bounds the number of irreducible representations by `|G|`.

## Main results

* `TauCeti.finiteDimensional_of_algEquiv_pi_matrix`: the coefficient algebras of a presentation of a
  finite-dimensional algebra are finite-dimensional.
* `TauCeti.finrank_eq_sum_sq_finrank`: **the dimension count**,
  `finrank K A = ∑ᵢ nᵢ² · finrank K Dᵢ`.
* `TauCeti.finrank_eq_sum_sq_of_isAlgClosed`: over an algebraically closed field the count reads
  `finrank k A = ∑ᵢ nᵢ²`, because every finite-dimensional division algebra there is the base field;
  `TauCeti.finrank_eq_sum_sq_of_algEquiv_pi_matrix` is the already split form, which needs no
  hypothesis on the field.
* `TauCeti.exists_algEquiv_pi_matrix_divisionRing_finrank` and
  `TauCeti.exists_algEquiv_pi_matrix_of_isAlgClosed_finrank`: Artin--Wedderburn packaged together
  with the count.
* `TauCeti.sq_le_finrank_of_algEquiv_pi_matrix` and
  `TauCeti.card_le_finrank_of_algEquiv_pi_matrix`: the resulting bounds on a block degree and on the
  number of blocks.

## References

This implements the Layer 2 target "the dimension count" of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `finrank_eq_sum_sq_finrank` and `finrank_eq_sum_sq_of_isAlgClosed`. See C. W. Curtis
and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25, or T. Y. Lam,
*A First Course in Noncommutative Rings*, §3.
-/

public section

namespace TauCeti

universe u v w

open Module (finrank)

variable (K : Type u) [Field K] {ι : Type v} {d : ι → ℕ} {A : Type*} [Ring A] [Algebra K A]

/-! ### Finite-dimensionality of the blocks -/

section Blocks

variable {D : ι → Type w} [∀ i, Ring (D i)] [∀ i, Algebra K (D i)] [FiniteDimensional K A]
  (e : A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))

include e

/-- A matrix block of a presentation of a finite-dimensional algebra as a product of matrix algebras
is finite-dimensional: it is a direct factor, hence a linear quotient, of the algebra. -/
theorem finiteDimensional_matrix_of_algEquiv_pi_matrix (i : ι) :
    FiniteDimensional K (Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  classical
  have : Module.Finite K (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.of_surjective
    (LinearMap.proj (R := K) (φ := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i)
    fun x => ⟨Pi.single i x, by simp⟩

/-- The coefficient algebras of a presentation of a finite-dimensional algebra as a product of
matrix algebras are themselves finite-dimensional, so no such presentation can involve an
infinite-dimensional division algebra.

The positivity hypothesis `NeZero (d i)` is essential and not an artefact of the proof: a block of
size `0` is the zero ring whatever its coefficients are, so it constrains `D i` not at all. Every
Artin--Wedderburn presentation supplies that positivity. -/
theorem finiteDimensional_of_algEquiv_pi_matrix (i : ι) [NeZero (d i)] :
    FiniteDimensional K (D i) := by
  have := finiteDimensional_matrix_of_algEquiv_pi_matrix K e i
  obtain ⟨j⟩ : Nonempty (Fin (d i)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (d i)))
  exact Module.Finite.of_surjective (Matrix.entryLinearMap K (D i) j j)
    fun x => ⟨Matrix.of fun _ _ => x, rfl⟩

end Blocks

/-! ### The dimension count -/

section Count

variable [Fintype ι] [FiniteDimensional K A]

section Coefficients

variable {D : ι → Type w} [∀ i, Ring (D i)] [∀ i, Algebra K (D i)]

/-- **The Wedderburn dimension count.** If a finite-dimensional `K`-algebra `A` is presented as a
finite product `∏ᵢ Matₙᵢ(Dᵢ)` of matrix algebras, then `finrank K A = ∑ᵢ nᵢ² · finrank K Dᵢ`.

Only the presentation is used: `A` is not assumed semisimple, although by
`RingEquiv.isSemisimpleRing` it is one as soon as the coefficients `Dᵢ` are division algebras. -/
theorem finrank_eq_sum_sq_finrank (e : A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    finrank K A = ∑ i, d i ^ 2 * finrank K (D i) := by
  have : ∀ i, Module.Finite K (Matrix (Fin (d i)) (Fin (d i)) (D i)) := fun i =>
    finiteDimensional_matrix_of_algEquiv_pi_matrix K e i
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix, Fintype.card_fin, sq]

end Coefficients

omit [FiniteDimensional K A] in
/-- **The dimension count for an already split presentation**: if `A` is presented as a product of
matrix algebras over the base field itself, then `finrank K A = ∑ᵢ nᵢ²`.

No hypothesis on `K` is needed here; algebraic closedness enters
`TauCeti.finrank_eq_sum_sq_of_isAlgClosed` only to force the coefficients of a presentation to be
the base field, and here they already are. -/
theorem finrank_eq_sum_sq_of_algEquiv_pi_matrix
    (e : A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K A = ∑ i, d i ^ 2 :=
  e.toLinearEquiv.finrank_eq.trans (finrank_pi_matrix K d)

/-- **The dimension count over an algebraically closed field.** Every finite-dimensional division
algebra over an algebraically closed field is the field itself, so the coefficient dimensions in
`TauCeti.finrank_eq_sum_sq_finrank` all equal `1` and the count reads `finrank k A = ∑ᵢ nᵢ²`.

This is the identity that becomes `∑ᵢ nᵢ² = |G|` for the group algebra of a finite group over a
splitting field. -/
theorem finrank_eq_sum_sq_of_isAlgClosed [IsAlgClosed K] {D : ι → Type w}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra K (D i)]
    (e : A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    finrank K A = ∑ i, d i ^ 2 := by
  rw [finrank_eq_sum_sq_finrank K e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (d i) 0 with h | h
  · simp [h]
  · have : NeZero (d i) := ⟨h⟩
    have := finiteDimensional_of_algEquiv_pi_matrix K e i
    obtain ⟨f⟩ := nonempty_algEquiv_self_of_finiteDimensional_divisionRing (k := K) (D := D i)
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]

end Count

/-! ### Artin--Wedderburn with the count -/

section Existence

variable (A : Type u) [Ring A] [Algebra K A] [IsSemisimpleRing A] [FiniteDimensional K A]

/-- **Artin--Wedderburn with the dimension count.** A finite-dimensional semisimple `K`-algebra is a
finite product of matrix algebras of positive size over finite-dimensional division `K`-algebras,
and its dimension is `∑ᵢ nᵢ² · finrank K Dᵢ`. -/
theorem exists_algEquiv_pi_matrix_divisionRing_finrank :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra K (D i)) (_ : ∀ i, FiniteDimensional K (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ∧
      finrank K A = ∑ i, d i ^ 2 * finrank K (D i) := by
  obtain ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite K A
  exact ⟨n, D, d, inferInstance, inferInstance, inferInstance, hd, ⟨e⟩,
    finrank_eq_sum_sq_finrank K e⟩

/-- **Artin--Wedderburn with the dimension count, over an algebraically closed field.** A
finite-dimensional semisimple algebra over an algebraically closed field is a finite product of
matrix algebras of positive size over that field, and its dimension is `∑ᵢ nᵢ²`. -/
theorem exists_algEquiv_pi_matrix_of_isAlgClosed_finrank [IsAlgClosed K] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K) ∧
      finrank K A = ∑ i, d i ^ 2 := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  exact ⟨n, d, hd, ⟨e⟩, finrank_eq_sum_sq_of_algEquiv_pi_matrix K e⟩

end Existence

/-! ### Bounds read off the count -/

section Bounds

variable [Finite ι] [FiniteDimensional K A] {D : ι → Type w} [∀ i, Ring (D i)]
  [∀ i, Algebra K (D i)] [∀ i, Nontrivial (D i)]
  (e : A ≃ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))

include e

/-- **The degree of a block is bounded by the dimension**: `nᵢ² ≤ finrank K A` for every block of a
presentation of a finite-dimensional algebra by matrix algebras over nontrivial coefficients. -/
theorem sq_le_finrank_of_algEquiv_pi_matrix (i : ι) : d i ^ 2 ≤ finrank K A := by
  have : Fintype ι := Fintype.ofFinite ι
  rcases eq_or_ne (d i) 0 with h | h
  · simp [h]
  · have : NeZero (d i) := ⟨h⟩
    have := finiteDimensional_of_algEquiv_pi_matrix K e i
    calc d i ^ 2 ≤ d i ^ 2 * finrank K (D i) :=
          Nat.le_mul_of_pos_right _ (Module.finrank_pos (R := K) (M := D i))
      _ ≤ ∑ j, d j ^ 2 * finrank K (D j) :=
          Finset.single_le_sum (f := fun j => d j ^ 2 * finrank K (D j))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = finrank K A := (finrank_eq_sum_sq_finrank K e).symm

/-- **The number of blocks is bounded by the dimension**: a finite-dimensional algebra presented by
nonzero matrix blocks over nontrivial coefficients has at most `finrank K A` of them.

For the group algebra of a finite group over a splitting field this bounds the number of irreducible
representations by the order of the group. -/
theorem card_le_finrank_of_algEquiv_pi_matrix [∀ i, NeZero (d i)] :
    Nat.card ι ≤ finrank K A := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [finrank_eq_sum_sq_finrank K e, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun i _ => ?_
  have := finiteDimensional_of_algEquiv_pi_matrix K e i
  exact Nat.one_le_iff_ne_zero.mpr <| Nat.mul_ne_zero (pow_ne_zero 2 (NeZero.ne (d i)))
    (Module.finrank_pos (R := K) (M := D i)).ne'

end Bounds

end TauCeti
