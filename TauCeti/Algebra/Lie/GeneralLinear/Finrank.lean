/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic

import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The dimension of the special linear Lie algebra

`sl n R` is the kernel of the trace on the `n × n` matrices, and it is free of rank
`(card n) ^ 2 - 1` over any commutative ring: after fixing an index `i₀`, the entries away from the
`(i₀, i₀)` place are free coordinates, and the trace-zero condition determines the `(i₀, i₀)` entry
as minus the sum of the other diagonal entries. Reading the rank off that coordinate system gives

`finrank R (sl n R) = (card n) ^ 2 - 1`.

The truncated subtraction is not a fudge. For an empty index type the matrix algebra is the zero
ring and both sides are `0`, since `0 - 1 = 0` in `ℕ`. The statement therefore carries no
nonemptiness hypothesis, and `TauCeti.finrank_sl_add_one` records the untruncated form
`finrank R (sl n R) + 1 = (card n) ^ 2` where nonemptiness is available.

No field, characteristic or algebraic closure hypothesis is used: the strong rank condition is all
that `finrank` needs in order to count the basis vectors, and over a commutative ring it is implied
by nontriviality. This is the only rank statement for `sl n R` in the repository: the rank-two case
is the instance `n = Fin 2`, and `TauCeti/Algebra/Lie/Sl2/Basic.lean` takes its rank `3` and its
`Module.Free`/`Module.Finite` instances from here rather than from its own named basis
`e`, `f`, `h` (`TauCeti.slFinTwoBasis`).

## Main results

* `TauCeti.finrank_sl`: `sl n R` has rank `(card n) ^ 2 - 1`.
* `TauCeti.finrank_sl_add_one`: the untruncated form, for a nonempty index type.

The same coordinate system also gives the `Module.Free` and `Module.Finite` instances for `sl n R`
that any rank computation involving it needs; over a commutative ring these do not come for free
from finiteness of the matrices.

## Implementation notes

The coordinate system above is a private linear equivalence, together with the private coordinate
map, the private matrix it inverts to and their two round-trip lemmas: they exist only to feed
`Basis.ofEquivFun`, and the public surface of the file is the two rank statements and the two
instances. The trace-zero reading of membership in `sl n R` is likewise a private lemma, obtained
from the located bridge `TauCeti.slIdeal_toLieSubalgebra_eq_sl` so that no proof here unfolds
Mathlib's `LieSubalgebra` wrapper by hand.
-/

public section

namespace TauCeti

open Matrix Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [Fintype n] [DecidableEq n]

section Coordinates

variable [CommRing R] (i₀ : n)

/-- The diagonal place `(k, k)`, for `k ≠ i₀`, as one of the free coordinates of a trace-zero
matrix. -/
private def diagIdx (k : {k : n // k ≠ i₀}) : {p : n × n // p ≠ (i₀, i₀)} :=
  ⟨(k.1, k.1), fun hk => k.2 (congrArg Prod.fst hk)⟩

/-- The coordinates of a matrix: its entries away from the `(i₀, i₀)` place. -/
private def offDiagCoords (A : Matrix n n R) (p : {p : n × n // p ≠ (i₀, i₀)}) : R :=
  A p.1.1 p.1.2

omit [Fintype n] [DecidableEq n] [CommRing R] in
private lemma offDiagCoords_apply (A : Matrix n n R) (p : {p : n × n // p ≠ (i₀, i₀)}) :
    offDiagCoords i₀ A p = A p.1.1 p.1.2 :=
  rfl

omit [Fintype n] [DecidableEq n] [CommRing R] in
private lemma offDiagCoords_diagIdx (A : Matrix n n R) (k : {k : n // k ≠ i₀}) :
    offDiagCoords i₀ A (diagIdx i₀ k) = A k.1 k.1 :=
  rfl

/-- The matrix with prescribed entries away from the `(i₀, i₀)` place, the entry there being the one
that makes the trace vanish. -/
private def ofOffDiag (g : {p : n × n // p ≠ (i₀, i₀)} → R) : Matrix n n R :=
  Matrix.of fun i j =>
    if h : (i, j) = (i₀, i₀) then -∑ k : {k : n // k ≠ i₀}, g (diagIdx i₀ k) else g ⟨(i, j), h⟩

private lemma ofOffDiag_apply_of_ne (g : {p : n × n // p ≠ (i₀, i₀)} → R) {i j : n}
    (h : (i, j) ≠ (i₀, i₀)) : ofOffDiag i₀ g i j = g ⟨(i, j), h⟩ :=
  dite_eq_right h

private lemma ofOffDiag_apply_self (g : {p : n × n // p ≠ (i₀, i₀)} → R) :
    ofOffDiag i₀ g i₀ i₀ = -∑ k : {k : n // k ≠ i₀}, g (diagIdx i₀ k) :=
  dite_eq_left rfl

private lemma trace_ofOffDiag (g : {p : n × n // p ≠ (i₀, i₀)} → R) :
    (ofOffDiag i₀ g).trace = 0 := by
  have hdiag : ∀ k : {k : n // k ≠ i₀}, ofOffDiag i₀ g k.1 k.1 = g (diagIdx i₀ k) :=
    fun k => ofOffDiag_apply_of_ne i₀ g (diagIdx i₀ k).2
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ofOffDiag_apply_self]
  simp only [hdiag]
  exact neg_add_cancel _

/-- Membership in `sl n R` is the vanishing of the trace.

Mathlib builds `LieAlgebra.SpecialLinear.sl` out of `LinearMap.ker (Matrix.traceLinearMap n R R)`,
so the two readings of membership are definitionally equal; that conversion is crossed once here,
through the named bridge `TauCeti.slIdeal_toLieSubalgebra_eq_sl`, rather than by unfolding the
`LieSubalgebra` wrapper at each use. -/
private lemma mem_sl_iff {A : Matrix n n R} : A ∈ SpecialLinear.sl n R ↔ A.trace = 0 := by
  rw [← slIdeal_toLieSubalgebra_eq_sl R n]
  exact mem_slIdeal_iff

private lemma ofOffDiag_mem_sl (g : {p : n × n // p ≠ (i₀, i₀)} → R) :
    ofOffDiag i₀ g ∈ SpecialLinear.sl n R :=
  mem_sl_iff.mpr (trace_ofOffDiag i₀ g)

/-- A trace-zero matrix is recovered from its coordinates: the entry it omits is forced. -/
private lemma ofOffDiag_offDiagCoords {A : Matrix n n R} (hA : A.trace = 0) :
    ofOffDiag i₀ (offDiagCoords i₀ A) = A := by
  refine Matrix.ext fun i j => ?_
  by_cases h : (i, j) = (i₀, i₀)
  · have hi : i = i₀ := congrArg Prod.fst h
    have hj : j = i₀ := congrArg Prod.snd h
    rw [hi, hj, ofOffDiag_apply_self]
    simp only [offDiagCoords_diagIdx]
    simp only [Matrix.trace, Matrix.diag_apply] at hA
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hA
    exact neg_eq_of_add_eq_zero_left hA
  · rw [ofOffDiag_apply_of_ne i₀ _ h, offDiagCoords_apply]

/-- The coordinates of the matrix built from a prescribed family are that family back again. -/
private lemma offDiagCoords_ofOffDiag (g : {p : n × n // p ≠ (i₀, i₀)} → R) :
    offDiagCoords i₀ (ofOffDiag i₀ g) = g := by
  funext p
  rw [offDiagCoords_apply]
  exact ofOffDiag_apply_of_ne i₀ g p.2

/-- **Coordinates on `sl n R`.** A trace-zero matrix is determined by its entries away from the
`(i₀, i₀)` place, and those entries are arbitrary: the trace-zero condition reads the remaining
entry off as minus the sum of the other diagonal ones. -/
private def slEquivFun : SpecialLinear.sl n R ≃ₗ[R] ({p : n × n // p ≠ (i₀, i₀)} → R) where
  toFun A := offDiagCoords i₀ A.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨ofOffDiag i₀ g, ofOffDiag_mem_sl i₀ g⟩
  left_inv A := Subtype.ext (ofOffDiag_offDiagCoords i₀ (mem_sl_iff.mp A.2))
  right_inv g := offDiagCoords_ofOffDiag i₀ g

end Coordinates

section FreeFinite

variable [CommRing R]

/-- **`sl n R` is a free module.** For a nonempty index type the coordinates above are a basis of
it; for an empty one it is the zero module. -/
instance : Module.Free R (SpecialLinear.sl n R) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · infer_instance
  · exact Module.Free.of_basis (Basis.ofEquivFun (slEquivFun i₀))

/-- **`sl n R` is a finite module**, the coordinates above being finite in number. -/
instance : Module.Finite R (SpecialLinear.sl n R) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · infer_instance
  · exact Module.Finite.of_basis (Basis.ofEquivFun (slEquivFun i₀))

end FreeFinite

section Finrank

variable (R n) [CommRing R] [StrongRankCondition R]

/-- **The rank of `sl n R`**: `finrank R (sl n R) = (card n) ^ 2 - 1`.

For an empty index type the matrix algebra is trivial and both sides are `0`, the truncated
subtraction `0 - 1` doing the work. -/
@[simp]
theorem finrank_sl :
    finrank R (SpecialLinear.sl n R) = Fintype.card n ^ 2 - 1 := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  -- With no indices at all the only matrix is `0`, and `0 - 1 = 0` in `ℕ`. `Subsingleton (sl n R)`
  -- is an instance there; `hnt` installs the other hypothesis of `finrank_zero_of_subsingleton`.
  · have hnt : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Module.finrank_zero_of_subsingleton, Fintype.card_eq_zero]
    simp
  -- Otherwise the free coordinates are the places other than `(i₀, i₀)`, and there are
  -- `(card n) ^ 2 - 1` of them.
  · rw [finrank_eq_card_basis (Basis.ofEquivFun (slEquivFun i₀))]
    have hcard := Fintype.card_congr (Equiv.optionSubtypeNe ((i₀, i₀) : n × n))
    simp only [Fintype.card_option, Fintype.card_prod] at hcard
    rw [sq, ← hcard]
    omega

variable [Nonempty n]

/-- The untruncated codimension-one statement: `sl n R` is a hyperplane in the matrices. -/
theorem finrank_sl_add_one :
    finrank R (SpecialLinear.sl n R) + 1 = Fintype.card n ^ 2 := by
  have hpos : 1 ≤ Fintype.card n ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  rw [finrank_sl]
  omega

end Finrank

end TauCeti
