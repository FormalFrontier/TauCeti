/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the classes and types occurring in the exported statements. `IsSimpleRing` is both a
-- hypothesis and a conclusion, `Module.End` is the object under study, `IsArtinianRing` and
-- `Module.Finite` are the hypotheses of the simplicity theorem, and `Module.finrank` and
-- `FiniteDimensional` carry the dimension count.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Defs
-- Non-public: used only inside proofs. The matrix presentation of the endomorphism algebra of a
-- power, the dimension of a matrix algebra, the simplicity of the endomorphism ring of an isotypic
-- module, and the isotypic decomposition over a simple Artinian algebra are all internal to the
-- arguments below, and no exported statement mentions a matrix algebra.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.RingTheory.Semisimple.IsotypicEnd
import TauCeti.RingTheory.Semisimple.SimpleArtinian

/-!
# The endomorphism algebra of a module over a simple Artinian algebra

Let `K` be a field, let `R` be a finite-dimensional **simple** `K`-algebra and let `M` be an
`R`-module which is finite-dimensional over `K`. All simple `R`-modules are isomorphic, to a fixed
minimal left ideal `S`, and `M` is a direct sum of `k` copies of `S`
(`TauCeti.IsIsotypicOfType.of_isSimpleRing`), so

  `End_R M ≃ₐ[K] Mat_k(End_R S)`,

a matrix algebra over the division algebra `End_R S` supplied by Schur's lemma. Two consequences
are recorded here: `End_R M` is again a simple ring when `M ≠ 0`, and its dimension satisfies

  `finrank K (End_R M) * finrank K R = (finrank K M)²`.

Only the dimension identity needs the field: simplicity of `End_R M` is stated with no `K` in sight,
for a nonzero module `M` finite over a simple Artinian ring `R`.

The dimension identity is what makes `End_R M` computable without naming `S`, `k` or the division
algebra: writing `finrank K S = s`, `finrank K M = k * s` and `finrank K R = m * s`, the matrix
presentation gives `finrank K (End_R M) = k² * d` and `finrank K (End_R R) = m² * d` for
`d = finrank K (End_R S)`. Since `End_R R` is `R` itself, the second identity reads `m * s = m² * d`
and pins `s = m * d`; substituting turns the first into the displayed formula, in which `S`, `k`,
`m` and `d` have all disappeared.

Applied to `R = B ⊗[K] Aᵐᵒᵖ` acting on a simple algebra `A` containing a central simple subalgebra
`B`, whose endomorphism algebra is the centralizer of `B`, this is the engine of the centralizer
theorem in `TauCeti/Algebra/CentralSimple/Centralizer.lean`.

## Main results

* `TauCeti.IsSimpleRing.finrank_end_mul_finrank_eq_sq`: the dimension identity
  `finrank K (End_R M) * finrank K R = (finrank K M)²`.
* `TauCeti.IsSimpleRing.moduleEnd`: `End_R M` is a simple ring, for `M` a nonzero module finite
  over a simple Artinian ring `R`.

## Implementation notes

The simple module `S` that both `M` and the regular module `R` are compared against is taken to be
a minimal left ideal of `R`, exactly as in `TauCeti/RingTheory/Semisimple/SimpleArtinian.lean`:
taking it inside `R` is what lets the same `S` serve both, which is what makes the two matrix
presentations comparable and lets `d = finrank K (End_R S)` cancel.

Simplicity of `R` is not weakened to semisimplicity. Over a semisimple ring with several blocks
`End_R M` is a *product* of matrix algebras, hence simple only when `M` is isotypic, and the
dimension identity fails: for `R = K × K` and `M = K × 0`, `End_R M` is `K`, so the left-hand side
is `1 * 2 = 2` while `(finrank K M)² = 1`.

## References

This supplies the module-theoretic engine of the Layer 5 centralizer theorem of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12, and T. Y. Lam, *A First Course in
Noncommutative Rings*, GTM 131, Chapter 1.
-/

public section

namespace TauCeti

open Module

namespace IsSimpleRing

section Simplicity

variable {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **The endomorphism ring of a nonzero finite module over a simple Artinian ring is simple.** It
is the matrix ring `Mat_k(End_R S)` over the division ring of Schur's lemma, with `k ≠ 0` because
`M ≠ 0`.

No base field is involved: `M` is a power `Sᵏ` of a minimal left ideal `S` of `R` because `R` is
simple Artinian and `M` is finite over `R`.  That is the only use made of simplicity of `R`, so
this is the specialization of `TauCeti.isSimpleRing_moduleEnd_of_isIsotypic` along
`IsSimpleRing.isIsotypic`. -/
theorem moduleEnd [Nontrivial M] : IsSimpleRing (Module.End R M) :=
  isSimpleRing_moduleEnd_of_isIsotypic (_root_.IsSimpleRing.isIsotypic R M)

end Simplicity

variable (K : Type*) [Field K] {R : Type*} [Ring R] [IsSimpleRing R] [Algebra K R]
  [FiniteDimensional K R]

section Aux

variable (S : Submodule R R) [IsSimpleModule R S]
variable (M : Type*) [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]

/-- The matrix presentation of `End_R M` over the division algebra `End_R S`, together with the
matching dimension count for `M` itself. Both are read off one and the same isomorphism
`M ≃ₗ[R] Sᵏ`, which is why the multiplicity `k` is shared between them. -/
private theorem exists_algEquiv_matrix_end :
    ∃ k : ℕ, finrank K M = k * finrank K S ∧
      Nonempty (Module.End R M ≃ₐ[K] Matrix (Fin k) (Fin k) (Module.End R S)) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R M
  obtain ⟨k, ⟨e⟩⟩ := (IsIsotypicOfType.of_isSimpleRing R (↥S) M).linearEquiv_fun
  refine ⟨k, ?_, ⟨(e.conjAlgEquiv K).trans (endVecAlgEquivMatrixEnd (Fin k) K R (↥S))⟩⟩
  rw [(e.restrictScalars K).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Aux

variable {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]

/-- **The dimension of the endomorphism algebra of a module over a simple Artinian algebra.** For a
finite-dimensional simple `K`-algebra `R` and an `R`-module `M` finite-dimensional over `K`,

  `finrank K (End_R M) * finrank K R = (finrank K M)²`.

Both sides are `k² * m² * d²` in the notation of the module docstring: `M` is `Sᵏ` and `R` is `Sᵐ`
for a minimal left ideal `S` with `finrank K S = m * d`, where `d = finrank K (End_R S)`.

The identity determines `finrank K (End_R M)` outright, since `finrank K R ≠ 0`; it is stated as a
product rather than a quotient to stay inside `ℕ`. -/
theorem finrank_end_mul_finrank_eq_sq :
    finrank K (Module.End R M) * finrank K R = finrank K M ^ 2 := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R R)
  rw [← isSimpleModule_iff_isAtom] at hS
  obtain ⟨k, hk, ⟨eM⟩⟩ := exists_algEquiv_matrix_end K S M
  obtain ⟨m, hm, ⟨eR⟩⟩ := exists_algEquiv_matrix_end K S R
  set s := finrank K S with hs
  set d := finrank K (Module.End R ↥S) with hd
  -- The matrix presentations turn both endomorphism dimensions into `(size)² * d`.
  have hEM : finrank K (Module.End R M) = k ^ 2 * d := by
    rw [(eM.toLinearEquiv).finrank_eq, Module.finrank_matrix, Fintype.card_fin, sq]
  have hER : finrank K (Module.End R R) = m ^ 2 * d := by
    rw [(eR.toLinearEquiv).finrank_eq, Module.finrank_matrix, Fintype.card_fin, sq]
  -- `End_R R` is `R` itself, so the second presentation is a relation between `m`, `s` and `d`.
  have : SMulCommClass R K R := SMulCommClass.symm K R R
  have hself : finrank K (Module.End R R) = finrank K R :=
    (LinearMap.ringLmapEquivSelf R K R).finrank_eq
  have hmpos : 0 < m := by
    by_contra h
    rw [Nat.eq_zero_of_not_pos h, zero_mul] at hm
    exact (Module.finrank_pos (R := K) (M := R)).ne' hm
  have hsmd : s = m * d := by
    have h := hself.symm.trans hER
    rw [hm, sq, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left hmpos h
  rw [hEM, hm, hk, hsmd]
  ring

end IsSimpleRing

end TauCeti
