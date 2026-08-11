/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.BrauerGroup.Group` is imported publicly: `TauCeti.BrauerGroup.mk` and the group
-- structure occur in the statements below, and `TauCeti.BrauerGroup.mk_eq_one_iff` together with
-- `TauCeti.BrauerGroup.orderOf_mk_dvd_two` are what the corollaries run on. It re-exports
-- `TauCeti.Algebra.BrauerGroup.Trivial`, hence `TauCeti.IsBrauerTrivial` and the splitting-side
-- implication `TauCeti.isBrauerTrivial_of_isSplittingField` this file converses, and with it `CSA`,
-- `IsBrauerEquivalent`, `BrauerGroup`, `TauCeti.CSA.of`, `TauCeti.CSA.base` and
-- `TauCeti.Algebra.IsSplittingField`; that is why none of those is imported again here.
public import TauCeti.Algebra.BrauerGroup.Group
-- `TauCeti.Algebra.CentralSimple.Wedderburn` is imported publicly for `Module.finrank`, which
-- occurs in the division-algebra statements below, through the
-- `Mathlib.LinearAlgebra.Dimension.Constructions` it re-exports; that module also supplies the
-- dimension count `Module.finrank_matrix` used in the proofs. Its own main theorem
-- `TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing` is the Wedderburn presentation
-- the argument runs on.
public import TauCeti.Algebra.CentralSimple.Wedderburn
-- Non-public: `TauCeti.wedderburn_data_unique` and `TauCeti.length_eq_card_of_ringEquiv_matrix`,
-- the invariance of the size of a matrix presentation, are the engine of the proofs and are
-- mentioned by no exported statement.
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing
-- Non-public: `orderOf` supports the order results at the end of the file, exactly as in
-- `TauCeti/Algebra/BrauerGroup/Group.lean`.
import Mathlib.GroupTheory.OrderOfElement

/-!
# A Brauer-trivial algebra is split

`TauCeti/Algebra/BrauerGroup/Trivial.lean` proves that an algebra **split** by its own base field
-- one isomorphic to a full matrix algebra `Mₙ(K)` -- has the identity Brauer class, and leaves the
converse open: nothing there rules out an algebra that becomes a matrix algebra only after passing
to matrices over it. This file closes that gap, and so identifies the identity class of
`BrauerGroup K` exactly.

The missing ingredient is the **uniqueness of the Wedderburn data**, proved in
`TauCeti/RingTheory/Semisimple/MatrixDivisionRing.lean`. Given
`Mₚ(A) ≃ₐ[K] M_q(K)`, write `A ≃ₐ[K] M_r(D)` for a central division algebra `D`
(`TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`). Then `Mₚ(A)` is presented as a
matrix ring over a division ring in two ways, of sizes `p * r` over `D` and `q` over `K`, so
`TauCeti.wedderburn_data_unique` forces `p * r = q`. Comparing dimensions,
`p² · dim_K A = q² = p² r²`, so `dim_K A = r²`, and the Wedderburn dimension count
`dim_K A = r² · dim_K D` collapses `D` to `K`. Hence `A ≃ₐ[K] M_r(K)` already.

Two consequences follow. A **central division algebra** has the identity Brauer class only if it
*is* the base field, since a division ring is a matrix ring only in size one (its regular module has
length one); this is the base case of the statement that each Brauer class has a unique
division-algebra representative. And an algebra isomorphic to its own opposite whose class is not
the identity has a class of order **exactly** `2`, sharpening
`TauCeti.BrauerGroup.orderOf_mk_dvd_two`; the real quaternions are the worked example, in
`TauCeti/Algebra/BrauerGroup/Quaternion.lean`.

## Main results

* `TauCeti.Algebra.isSplittingField_self_of_isBrauerTrivial`: **a Brauer-trivial algebra is split by
  its own base field**, the converse of `TauCeti.isBrauerTrivial_of_isSplittingField`, packaged as
  the equivalences `TauCeti.isBrauerTrivial_iff_isSplittingField` and
  `TauCeti.BrauerGroup.mk_eq_one_iff_isSplittingField`.
* `TauCeti.isBrauerTrivial_iff_finrank_eq_one`: **a central division algebra is Brauer trivial
  exactly when it is the base field**, with `TauCeti.baseFieldAlgEquivOfIsBrauerTrivial` the
  isomorphism this produces.
* `TauCeti.BrauerGroup.orderOf_mk_eq_two`: **a self-opposite class other than the identity has
  order exactly `2`.**

## Implementation notes

Only the size half of `TauCeti.wedderburn_data_unique` is used: the division ring is pinned here by
a dimension count instead, which keeps the argument inside `Module.finrank` and avoids having to
promote the ring isomorphism `D ≃+* K` that the other half supplies to an isomorphism of
`K`-algebras.

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
needs the uniqueness of the Wedderburn data. Writing `A ≃ₐ[K] M_r(D)` for a central division
algebra `D`, the ring `Mₚ(A)` acquires two presentations as a matrix ring over a division ring, of
sizes `p * r` over `D` and `q` over `K`, so `TauCeti.wedderburn_data_unique` gives `p * r = q`.
Comparing dimensions then gives `dim_K A = r ^ 2`, which against the Wedderburn count
`dim_K A = r ^ 2 * dim_K D` leaves `dim_K D = 1`, so `D` is `K` and the presentation of `A` is
already a matrix algebra over `K`. -/
theorem Algebra.isSplittingField_self_of_isBrauerTrivial (h : IsBrauerTrivial (CSA.of K A)) :
    Algebra.IsSplittingField K A K := by
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := h
  have e' : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin q) (Fin q) K := e
  obtain ⟨r, hr, D, _, _, _, _, hrank, ⟨f⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
  -- The second presentation of `Mₚ(A)`, of size `p * r` and over `D`.
  have g : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin (p * r)) (Fin (p * r)) D :=
    (f.mapMatrix (m := Fin p)).trans <| (Matrix.compAlgEquiv (Fin p) (Fin r) D K).trans <|
      Matrix.reindexAlgEquiv K D finProdFinEquiv
  have hpr : NeZero (p * r) := ⟨Nat.mul_ne_zero hp (NeZero.ne r)⟩
  have hq' : NeZero q := ⟨hq⟩
  have hsize : p * r = q := (wedderburn_data_unique g.toRingEquiv e'.toRingEquiv).1
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

/-- **Brauer triviality is exactly splitting by the base field.** -/
theorem isBrauerTrivial_iff_isSplittingField :
    IsBrauerTrivial (CSA.of K A) ↔ Algebra.IsSplittingField K A K :=
  ⟨Algebra.isSplittingField_self_of_isBrauerTrivial K A, isBrauerTrivial_of_isSplittingField K⟩

/-- **A Brauer class is the identity exactly when its algebras are split by the base field.** This
is the sharp form of `TauCeti.BrauerGroup.mk_eq_one_of_isSplittingField`. -/
theorem BrauerGroup.mk_eq_one_iff_isSplittingField :
    BrauerGroup.mk (CSA.of K A) = 1 ↔ Algebra.IsSplittingField K A K :=
  BrauerGroup.mk_eq_one_iff.trans (isBrauerTrivial_iff_isSplittingField K A)

end CentralSimple

/-! ### The Brauer class of a central division algebra -/

section DivisionRing

variable (K : Type u) [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- **A central division algebra is Brauer trivial exactly when it is the base field.**

A division ring is a matrix ring only in size one, because its regular module is simple and the size
of a matrix presentation is the length of the regular module
(`TauCeti.length_eq_card_of_ringEquiv_matrix`). So a split central division algebra is
one-dimensional; conversely a one-dimensional algebra *is* the base field, whose class is the
identity by definition.

This is the base case of the statement that every Brauer class has a unique division-algebra
representative, and it is what makes a Brauer group nontrivial in practice: exhibiting a central
division algebra of dimension greater than one exhibits a nonidentity class. -/
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

/-- **The Brauer class of a central division algebra is the identity exactly when the algebra is
one-dimensional.** -/
theorem BrauerGroup.mk_eq_one_iff_finrank_eq_one :
    BrauerGroup.mk (CSA.of K D) = 1 ↔ Module.finrank K D = 1 :=
  BrauerGroup.mk_eq_one_iff.trans (isBrauerTrivial_iff_finrank_eq_one K D)

end DivisionRing

/-! ### Classes of order two -/

namespace BrauerGroup

variable {K : Type u} [Field K]

/-- **A self-opposite Brauer class other than the identity has order exactly `2`.**

`TauCeti.BrauerGroup.orderOf_mk_dvd_two` bounds the order by `2`; since `2` is prime the only other
possibility is order `1`, which is the identity class. -/
theorem orderOf_mk_eq_two {A : CSA.{u, u} K} (h : IsBrauerEquivalent A (CSA.op A))
    (h1 : mk A ≠ 1) : orderOf (mk A) = 2 := by
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ (orderOf_mk_dvd_two h)) with h2 | h2
  · exact absurd (orderOf_eq_one_iff.1 h2) h1
  · exact h2

/-- **An algebra isomorphic to its own opposite, but not split, has a class of order exactly
`2`.** -/
theorem orderOf_mk_eq_two_of_algEquiv_op {A : CSA.{u, u} K}
    (e : (A : Type u) ≃ₐ[K] (A : Type u)ᵐᵒᵖ) (h1 : mk A ≠ 1) : orderOf (mk A) = 2 :=
  orderOf_mk_eq_two (IsBrauerEquivalent.of_algEquiv K e) h1

end BrauerGroup

end TauCeti
