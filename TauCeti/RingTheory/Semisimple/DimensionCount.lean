/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.Matrix.Pi` is imported publicly: it supplies the dimension count
-- `TauCeti.finrank_eq_sum_sq_finrank` specialized below and the finite-dimensionality
-- `TauCeti.finiteDimensional_of_algEquiv_pi_matrix` of the coefficients, and it re-exports
-- `Module.finrank` as well as the `Matrix` and the `FiniteDimensional` occurring in the statement.
public import TauCeti.Algebra.Matrix.Pi
-- `IsAlgClosed` appears in the hypotheses below.
public import Mathlib.FieldTheory.IsAlgClosed.Basic
-- Non-public: `TauCeti.nonempty_algEquiv_self_of_finiteDimensional_divisionRing` (the collapse of a
-- finite-dimensional division algebra over an algebraically closed field) is used only inside the
-- proof, so downstream importers do not pay for it.
import TauCeti.RingTheory.Semisimple.Schur

/-!
# The Wedderburn dimension count over an algebraically closed field

Artin--Wedderburn presents a finite-dimensional semisimple algebra `A` over a field `K` as a finite
product of matrix algebras `∏ᵢ Matₙᵢ(Dᵢ)` over division algebras, and
`TauCeti.finrank_eq_sum_sq_finrank` reads

`finrank K A = ∑ᵢ nᵢ² · finrank K Dᵢ`

off such a presentation, for coefficients `Dᵢ` of any kind. This file specializes that count to an
algebraically closed base field, where a coefficient division algebra of a block of nonzero size —
finite-dimensional by `TauCeti.finiteDimensional_of_algEquiv_pi_matrix` — is the base field itself,
so the count becomes the classical `finrank k A = ∑ᵢ nᵢ²`. A block of size `0` leaves its
coefficients unconstrained, but contributes `0` to both sides and so needs no such collapse.

Applied to a group algebra that last identity is the relation `∑ᵢ nᵢ² = |G|` between the degrees of
the irreducible representations of a finite group and its order;
`TauCeti/RepresentationTheory/CharacterTable/Wedderburn.lean` derives that special case from
`TauCeti.finrank_pi_matrix`, which the count generalizes away from the split case.

Nothing here needs the presentation to come from Artin--Wedderburn: an algebra equivalence
`A ≃ₐ[K] Π i, Matₙᵢ(Dᵢ)` onto *any* product of matrix algebras over division algebras is enough.

## Main results

* `TauCeti.finrank_eq_sum_sq_of_isAlgClosed`: over an algebraically closed field the count reads
  `finrank k A = ∑ᵢ nᵢ²`.

## References

This implements the Layer 2 target "the dimension count" of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `finrank_eq_sum_sq_of_isAlgClosed`; its companion `finrank_eq_sum_sq_finrank`, which
assumes nothing of the coefficients, is in `TauCeti/Algebra/Matrix/Pi.lean`. See C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25, or T. Y. Lam,
*A First Course in Noncommutative Rings*, §3.
-/

public section

namespace TauCeti

open Module (finrank)

variable (K : Type*) [Field K] {ι : Type*} [Fintype ι] {d : ι → ℕ} {A : Type*} [Ring A]
  [Algebra K A] [FiniteDimensional K A]

/-- **The dimension count over an algebraically closed field.** A finite-dimensional division
algebra over an algebraically closed field is the field itself, so each block of nonzero size in a
presentation `A ≃ₐ[K] ∏ᵢ Matₙᵢ(Dᵢ)` has `finrank K Dᵢ = 1` and the count
`TauCeti.finrank_eq_sum_sq_finrank` reads `finrank k A = ∑ᵢ nᵢ²`. A block of size `0` need not have
finite-dimensional, let alone split, coefficients, but contributes `0` to both sides.

This is the identity that becomes `∑ᵢ nᵢ² = |G|` for the group algebra of a finite group over a
splitting field. -/
theorem finrank_eq_sum_sq_of_isAlgClosed [IsAlgClosed K] {D : ι → Type*}
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

end TauCeti
