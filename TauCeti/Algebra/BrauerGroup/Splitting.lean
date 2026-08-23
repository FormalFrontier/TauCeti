/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
-- Non-public: `TauCeti.wedderburn_data_unique_of_algEquiv`, the algebra-linear uniqueness of a
-- matrix presentation, is the engine of the proofs and is mentioned by no exported statement.
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing
-- Non-public: division-algebra uniqueness supplies the normalized Brauer-equivalence criterion
-- used to make the division-algebra recognition theorem simp-normal.
import TauCeti.Algebra.BrauerGroup.Division

/-!
# A Brauer-trivial algebra is split

`TauCeti/Algebra/BrauerGroup/Trivial.lean` proves that an algebra **split** by its own base field
-- one isomorphic to a full matrix algebra `Mₙ(K)` -- has the identity Brauer class, and leaves the
converse open: nothing there rules out an algebra that becomes a matrix algebra only after passing
to matrices over it. This file closes that gap, and so identifies the identity class of
`BrauerGroup K` exactly.

The missing ingredient is the **uniqueness of matrix presentations**, proved in
`TauCeti/RingTheory/Semisimple/MatrixDivisionRing.lean`. Given
`Mₚ(A) ≃ₐ[K] M_q(K)`, write `A ≃ₐ[K] M_r(D)` for a central division algebra `D`
(`TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`). Then `Mₚ(A)` is presented as a
matrix ring over a division ring in two ways, of sizes `p * r` over `D` and `q` over `K`, so
`TauCeti.wedderburn_data_unique_of_algEquiv` identifies `D` with `K` as a `K`-algebra. Hence
`A ≃ₐ[K] M_r(K)` already.

A consequence follows for division algebras: a **central division algebra** has the identity Brauer
class only if it *is* the base field, because algebra-level uniqueness identifies the coefficient
division algebras in a stabilized matrix equivalence. This is the base case of the statement that
each Brauer class has a unique division-algebra representative, and it is the standard source of
*nonidentity* classes,
hence of the equivalence `TauCeti.BrauerGroup.mk_eq_mk_iff_nonempty_algEquiv` and of the hypothesis
that `TauCeti.BrauerGroup.orderOf_mk_eq_two` needs to sharpen
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

The algebra-level Wedderburn uniqueness theorem
`TauCeti.wedderburn_data_unique_of_algEquiv` is used directly: it keeps the base field fixed and
removes the earlier need to recover the coefficient division algebra from a separate dimension
count.  The remaining `Module.finrank` criterion is obtained from the resulting linear equivalence.

For a general central simple algebra, `TauCeti.isBrauerTrivial_iff_isSplittingField` is the `simp`
normal form of `TauCeti.IsBrauerTrivial`. For a division algebra, simplification instead passes
through `TauCeti.BrauerGroup.isBrauerEquivalent_iff_nonempty_algEquiv` and
`TauCeti.nonempty_algEquiv_base_iff_finrank_eq_one`. The two `TauCeti.BrauerGroup.mk` forms are
deliberately *not* additional `simp` lemmas: `TauCeti.BrauerGroup.mk_eq_one_iff` is one already, so
`simp` normalizes `mk (CSA.of K A) = 1` through it and reaches the same right-hand sides.

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
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := h
  have e' : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin q) (Fin q) K := e
  obtain ⟨r, hr, D, _, _, _, _, -, ⟨f⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
  -- The second presentation of `Mₚ(A)`, of size `p * r` and over `D`.
  have g : Matrix (Fin p) (Fin p) A ≃ₐ[K] Matrix (Fin (p * r)) (Fin (p * r)) D :=
    (f.mapMatrix (m := Fin p)).trans <| (Matrix.compAlgEquiv (Fin p) (Fin r) D K).trans <|
      Matrix.reindexAlgEquiv K D finProdFinEquiv
  let _ : NeZero p := ⟨hp⟩
  let _ : NeZero q := ⟨hq⟩
  let _ : NeZero (p * r) := inferInstance
  obtain ⟨-, ⟨d⟩⟩ := wedderburn_data_unique_of_algEquiv g e'
  exact (Algebra.isSplittingField_self_iff K A).2 ⟨r, ⟨f.trans d.mapMatrix⟩⟩

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

omit [Algebra.IsCentral K D] in
/-- A finite-dimensional division algebra is isomorphic over `K` to `K` exactly when it
has dimension one over `K`. -/
@[simp]
theorem nonempty_algEquiv_base_iff_finrank_eq_one :
    Nonempty (D ≃ₐ[K] K) ↔ Module.finrank K D = 1 := by
  constructor
  · rintro ⟨e⟩
    simpa using e.toLinearEquiv.finrank_eq
  · intro h
    exact ⟨(AlgEquiv.ofBijective (_root_.Algebra.ofId K D)
      (_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h)).symm⟩

/-- **A central division algebra is Brauer trivial exactly when it is the base field.**

This is the base case of the statement that every Brauer class has a unique division-algebra
representative, and it is what makes a Brauer group nontrivial in practice: exhibiting a central
division algebra of dimension greater than one exhibits a nonidentity class. -/
theorem isBrauerTrivial_iff_finrank_eq_one :
    IsBrauerTrivial (CSA.of K D) ↔ Module.finrank K D = 1 :=
  BrauerGroup.isBrauerEquivalent_iff_nonempty_algEquiv.trans
    (nonempty_algEquiv_base_iff_finrank_eq_one K D)

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
