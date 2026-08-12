/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.BrauerGroup.Group` is imported publicly: `TauCeti.BrauerGroup.mk` and the group
-- structure occur in the statements below, and `TauCeti.BrauerGroup.mk_eq_one_iff` is what the
-- corollaries run on. It re-exports
-- `TauCeti.Algebra.BrauerGroup.Trivial`, hence `TauCeti.IsBrauerTrivial` and the splitting-side
-- implication `TauCeti.isBrauerTrivial_of_isSplittingField` this file converses, and with it `CSA`,
-- `IsBrauerEquivalent`, `BrauerGroup`, `TauCeti.CSA.of`, `TauCeti.CSA.base` and
-- `TauCeti.Algebra.IsSplittingField`; that is why none of those is imported again here.
public import TauCeti.Algebra.BrauerGroup.Group
-- `Mathlib.LinearAlgebra.Dimension.Constructions` is imported publicly for `Module.finrank`, which
-- occurs in the division-algebra statements below; it also supplies the dimension count
-- `Module.finrank_matrix` used in the proofs.
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- Non-public: `TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`, the Wedderburn
-- presentation the argument runs on, is used only in the proofs; no statement here mentions it.
import TauCeti.Algebra.CentralSimple.Wedderburn
-- Non-public: `TauCeti.card_eq_of_ringEquiv_matrix` and
-- `TauCeti.length_eq_card_of_ringEquiv_matrix`, the invariance of the size of a matrix
-- presentation, are the engine of the proofs and are mentioned by no exported statement.
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing

/-!
# A Brauer-trivial algebra is split

`TauCeti/Algebra/BrauerGroup/Trivial.lean` proves that an algebra **split** by its own base field
-- one isomorphic to a full matrix algebra `Mₙ(K)` -- has the identity Brauer class, and leaves the
converse open: nothing there rules out an algebra that becomes a matrix algebra only after passing
to matrices over it. This file closes that gap, and so identifies the identity class of
`BrauerGroup K` exactly.

The missing ingredient is the **uniqueness of the size of a matrix presentation**, proved in
`TauCeti/RingTheory/Semisimple/MatrixDivisionRing.lean`. Given
`Mₚ(A) ≃ₐ[K] M_q(K)`, write `A ≃ₐ[K] M_r(D)` for a central division algebra `D`
(`TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`). Then `Mₚ(A)` is presented as a
matrix ring over a division ring in two ways, of sizes `p * r` over `D` and `q` over `K`, so
`TauCeti.card_eq_of_ringEquiv_matrix` forces `p * r = q`. Comparing dimensions,
`p² · dim_K A = q² = p² r²`, so `dim_K A = r²`, and the Wedderburn dimension count
`dim_K A = r² · dim_K D` collapses `D` to `K`. Hence `A ≃ₐ[K] M_r(K)` already.

A consequence follows for division algebras: a **central division algebra** has the identity Brauer
class only if it *is* the base field, since a division ring is a matrix ring only in size one (its
regular module has length one). This is the base case of the statement that each Brauer class has a
unique division-algebra representative, and it is the standard source of *nonidentity* classes,
hence of the hypothesis that `TauCeti.BrauerGroup.orderOf_mk_eq_two` needs to sharpen
`TauCeti.BrauerGroup.orderOf_mk_dvd_two`; the real quaternions are the worked example, in
`TauCeti/Algebra/BrauerGroup/Quaternion.lean`.

## Main results

* `TauCeti.Algebra.isSplittingField_self_of_isBrauerTrivial`: **a Brauer-trivial algebra is split by
  its own base field**, the converse of `TauCeti.isBrauerTrivial_of_isSplittingField`, packaged as
  the equivalences `TauCeti.isBrauerTrivial_iff_isSplittingField` and
  `TauCeti.BrauerGroup.mk_eq_one_iff_isSplittingField`.
* `TauCeti.isBrauerTrivial_iff_finrank_eq_one`: **a central division algebra is Brauer trivial
  exactly when it is the base field**, with `TauCeti.baseFieldAlgEquivOfIsBrauerTrivial` the
  isomorphism this produces and `TauCeti.BrauerGroup.mk_eq_one_iff_finrank_eq_one` the form for
  classes.

## Implementation notes

Only the size half of the Wedderburn uniqueness is used, in the form
`TauCeti.card_eq_of_ringEquiv_matrix`: the division ring is pinned here by a dimension count
instead, which keeps the argument inside `Module.finrank` and avoids having to promote the ring
isomorphism `D ≃+* K` that `TauCeti.wedderburn_data_unique` also supplies to an isomorphism of
`K`-algebras.

The two `IsBrauerTrivial` equivalences are the `simp` normal form of `TauCeti.IsBrauerTrivial`, the
division-algebra one at default priority and the general one at `low`, because a division algebra is
simple and so matches both left-hand sides; the sharper `Module.finrank` criterion is the one that
should win there. The two `TauCeti.BrauerGroup.mk` forms are deliberately *not* `simp` lemmas:
`TauCeti.BrauerGroup.mk_eq_one_iff` is one already, so `simp` normalizes `mk (CSA.of K A) = 1`
through it and reaches the same right-hand sides; tagging them as well makes the `simpNF` linter
report them as provable by the rules already in the set.

As in `TauCeti/Algebra/BrauerGroup/Trivial.lean`, the statements mentioning `TauCeti.CSA.base K`
are for a `CSA.{u, u} K`, an algebra in the universe of its own base field, because Mathlib's
`IsBrauerEquivalent` relates two algebras in one universe.

## References

This completes the first bullet of Layer 6 ("the API that the identity and inverse rest on") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
whose Layer 2 asks for the Wedderburn uniqueness this consumes, and it supplies the "`[ℍ]` has
order 2" step of that roadmap's Hamilton-quaternion worked example. See P. Gille, T. Szamuely,
*Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.4, and R. S. Pierce, *Associative
Algebras*, Springer GTM 88 (1982), Chapter 12.
-/

public section

namespace TauCeti

universe u

section CentralSimple

variable (K : Type u) [Field K] (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
  [IsSimpleRing A] [FiniteDimensional K A]

/-! ### A Brauer-trivial algebra is split by its own base field -/

/-- **A Brauer-trivial algebra is split by its own base field**: if `Mₚ(A) ≃ₐ[K] M_q(K)` for some
positive `p` and `q`, then already `A ≃ₐ[K] M_r(K)`.

This is the converse of `TauCeti.isBrauerTrivial_of_isSplittingField`, and it is not formal: it
needs the uniqueness of the Wedderburn data. -/
theorem Algebra.isSplittingField_self_of_isBrauerTrivial (h : IsBrauerTrivial (CSA.of K A)) :
    Algebra.IsSplittingField K A K := by
  obtain ⟨p, q, hp, -, ⟨e⟩⟩ := h
  have e' : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin q) (Fin q) K := e
  obtain ⟨r, hr, D, _, _, _, _, hrank, ⟨f⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
  -- The second presentation of `Mₚ(A)`, of size `p * r` and over `D`.
  have g : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin (p * r)) (Fin (p * r)) D :=
    (f.mapMatrix (m := Fin p)).trans <| (Matrix.compAlgEquiv (Fin p) (Fin r) D K).trans <|
      Matrix.reindexAlgEquiv K D finProdFinEquiv
  have hsize : p * r = q := by
    simpa using card_eq_of_ringEquiv_matrix g.toRingEquiv e'.toRingEquiv
  -- `dim_K A = r ^ 2`, by comparing the dimensions of the two sides of `e'`.
  have hA : Module.finrank K A = r ^ 2 := by
    have h1 : Module.finrank K (Matrix (Fin p) (Fin p) A) = p * p * Module.finrank K A := by
      rw [Module.finrank_matrix, Fintype.card_fin]
    have h2 : Module.finrank K (Matrix (Fin q) (Fin q) K) = q * q := by
      rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
    have h3 := e'.toLinearEquiv.finrank_eq
    rw [h1, h2, ← hsize] at h3
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Nat.mul_ne_zero hp hp)) ?_
    rw [h3]; ring
  -- So the Wedderburn division algebra is one-dimensional, hence is `K`.
  have hD : Module.finrank K D = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero 2 (NeZero.ne r))) ?_
    rw [mul_one, ← hrank]
    exact hA
  exact (Algebra.isSplittingField_self_iff K A).2 ⟨r, ⟨f.trans (AlgEquiv.mapMatrix
    (AlgEquiv.ofBijective (_root_.Algebra.ofId K D)
      (_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hD)).symm)⟩⟩

/-- **Brauer triviality is exactly splitting by the base field.**

This is the `simp` normal form of `TauCeti.IsBrauerTrivial` for a general central simple algebra;
it is at low priority so that the sharper `TauCeti.isBrauerTrivial_iff_finrank_eq_one` wins on a
division algebra, whose `IsBrauerTrivial` hypothesis matches both. -/
@[simp low]
theorem isBrauerTrivial_iff_isSplittingField :
    IsBrauerTrivial (CSA.of K A) ↔ Algebra.IsSplittingField K A K :=
  ⟨Algebra.isSplittingField_self_of_isBrauerTrivial K A, isBrauerTrivial_of_isSplittingField K⟩

/-- **A Brauer class is the identity exactly when its algebras are split by the base field.** This
is the sharp form of `TauCeti.BrauerGroup.mk_eq_one_of_isSplittingField`.

Not a `simp` lemma: `TauCeti.BrauerGroup.mk_eq_one_iff` is one already, so `simp` reaches the
right-hand side through it. -/
theorem BrauerGroup.mk_eq_one_iff_isSplittingField :
    BrauerGroup.mk (CSA.of K A) = 1 ↔ Algebra.IsSplittingField K A K :=
  BrauerGroup.mk_eq_one_iff.trans (isBrauerTrivial_iff_isSplittingField K A)

end CentralSimple

/-! ### The Brauer class of a central division algebra -/

section DivisionRing

variable (K : Type u) [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- **A central division algebra is Brauer trivial exactly when it is the base field.**

This is the base case of the statement that every Brauer class has a unique division-algebra
representative, and it is what makes a Brauer group nontrivial in practice: exhibiting a central
division algebra of dimension greater than one exhibits a nonidentity class. -/
@[simp]
theorem isBrauerTrivial_iff_finrank_eq_one :
    IsBrauerTrivial (CSA.of K D) ↔ Module.finrank K D = 1 := by
  constructor
  · intro h
    obtain ⟨n, ⟨e⟩⟩ := (Algebra.isSplittingField_self_iff K D).1
      (Algebra.isSplittingField_self_of_isBrauerTrivial K D h)
    have hlen : Module.length D D = (Fintype.card (Fin n) : ℕ∞) :=
      length_eq_card_of_ringEquiv_matrix e.toRingEquiv
    rw [Module.length_eq_one, Fintype.card_fin] at hlen
    have hn : n = 1 := by exact_mod_cast hlen.symm
    subst hn
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
  · intro h
    exact IsBrauerEquivalent.of_algEquiv K (A := CSA.of K D) (B := CSA.base K)
      (AlgEquiv.ofBijective (_root_.Algebra.ofId K D)
        (_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)).symm

/-- **A Brauer-trivial central division algebra is the base field**, as an isomorphism of
`K`-algebras. This is the division-algebra companion of `TauCeti.baseFieldAlgEquivOfFinite`, with
the finiteness hypothesis there replaced by triviality of the Brauer class. -/
noncomputable def baseFieldAlgEquivOfIsBrauerTrivial (h : IsBrauerTrivial (CSA.of K D)) :
    D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (_root_.Algebra.ofId K D)
    (_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap.1
      ((isBrauerTrivial_iff_finrank_eq_one K D).1 h))).symm

/-- The inverse of `TauCeti.baseFieldAlgEquivOfIsBrauerTrivial` is the structure map. -/
@[simp]
theorem baseFieldAlgEquivOfIsBrauerTrivial_symm_apply (h : IsBrauerTrivial (CSA.of K D)) (a : K) :
    (baseFieldAlgEquivOfIsBrauerTrivial K D h).symm a = algebraMap K D a :=
  (rfl)

/-- `TauCeti.baseFieldAlgEquivOfIsBrauerTrivial` is a section of the structure map. -/
@[simp]
theorem algebraMap_baseFieldAlgEquivOfIsBrauerTrivial (h : IsBrauerTrivial (CSA.of K D)) (x : D) :
    algebraMap K D (baseFieldAlgEquivOfIsBrauerTrivial K D h x) = x := by
  rw [← baseFieldAlgEquivOfIsBrauerTrivial_symm_apply K D h, AlgEquiv.symm_apply_apply]

/-- **The Brauer class of a central division algebra is the identity exactly when the algebra is
one-dimensional.**

Not a `simp` lemma, for the same reason as `TauCeti.BrauerGroup.mk_eq_one_iff_isSplittingField`. -/
theorem BrauerGroup.mk_eq_one_iff_finrank_eq_one :
    BrauerGroup.mk (CSA.of K D) = 1 ↔ Module.finrank K D = 1 :=
  BrauerGroup.mk_eq_one_iff.trans (isBrauerTrivial_iff_finrank_eq_one K D)

end DivisionRing

end TauCeti
