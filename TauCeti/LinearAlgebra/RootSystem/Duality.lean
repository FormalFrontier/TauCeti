/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Flip

public section

/-!
# Duality of Dynkin types

Interchanging the roots and the coroots of a root pairing (`RootPairing.flip`) transposes every
pairing `⟨αᵢ, αⱼ^∨⟩`, hence transposes the Cartan matrix of a base
(`TauCeti.RootPairing.Base.cartanMatrix_flip`, proved in `TauCeti.LinearAlgebra.RootSystem.Flip`).
On the classification side that operation permutes the Dynkin types, and this file pins the
permutation: `TauCeti.DynkinType.dual` exchanges `Bₙ` with `Cₙ` and fixes every other type.
Duality is what makes the orientation carried by `TauCeti.HasCartanType` meaningful, since `Bₙ` and
`Cₙ` are exactly the pair of types that the orientation separates.

The dual type is not read off the transposed matrix on the nose. Transposing a Cartan matrix does
not merely relabel the diagram, it reverses every arrow, and for `F₄` and `G₂` the reversed diagram
is the original one read backwards. So duality carries a relabelling of the nodes as well as a
change of type, and `TauCeti.DynkinType.dualNodeEquiv` is that relabelling: the identity for the
classical families and the `E` types, and the reversal `Fin.revPerm` for `F₄` and `G₂`.

`TauCeti.DynkinType.Valid` is deliberately *not* preserved by duality, and the failure is exactly
the low-rank coincidence `B 2 = C 2`: `B 2` is valid and its dual `C 2` is not, because the two
name the same root system and the enumeration keeps only one of the names. Away from that pair
validity does transfer (`TauCeti.DynkinType.valid_dual_iff`). The last section shows that nothing
is lost there: at rank at most two a base has a Cartan type exactly when it has the dual type
(`TauCeti.hasCartanType_dual_iff_of_rank_le_two`), because transposing a matrix with constant
diagonal and at most two indices is itself a simultaneous relabelling.

## Main definitions

* `TauCeti.DynkinType.dual`: the dual Dynkin type, exchanging `Bₙ` and `Cₙ`.
* `TauCeti.DynkinType.dualNodeEquiv`: the relabelling of nodes that duality carries.

## Main results

* `TauCeti.DynkinType.cartanMatrix_dual`: the standard Cartan matrix of the dual type is the
  transpose of the standard Cartan matrix, read through `dualNodeEquiv`.
* `TauCeti.hasCartanType_flip_iff`: **the Cartan type of a base and the Cartan type of the flipped
  base are dual**. In particular a base is of type `Bₙ` exactly when the flipped base is of type
  `Cₙ` (`TauCeti.hasCartanType_flip_C_iff`, and `TauCeti.hasCartanType_flip_B_iff` for the other
  orientation).
* `TauCeti.DynkinType.valid_dual_iff`: validity transfers along duality except for the pair
  `B 2`, `C 2`.
* `TauCeti.hasCartanType_dual_iff_of_rank_le_two`: at rank at most two a type and its dual match
  the same bases, which is why dropping `C 2` from the valid types loses nothing.

## References

This file supplies the duality half of the `DynkinType` layer of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`: Layer 5 records that
`DynkinType.cartanMatrix (.B n)` is the transpose of `DynkinType.cartanMatrix (.C n)` and that the
two types are "identified only after `flip` (duality)", and Layer 6 asks for the adjoint root datum
to be `RootPairing.flip` of the dual type's datum. See Bourbaki, *Lie Groups and Lie Algebras,
Chapters 4-6*, plates I-IX, for the standard Cartan matrices and their duals.
-/

namespace TauCeti

namespace DynkinType

/-- **The dual Dynkin type.** Duality reverses the arrows of a diagram, which exchanges the types
`Bₙ` and `Cₙ` — the one pair whose standard Cartan matrices are transposes of one another without
being equal — and fixes all the others. It is realized on root systems by `RootPairing.flip`; see
`TauCeti.hasCartanType_flip_iff`.

This is `@[expose]`d because it occurs in the *type* of `TauCeti.DynkinType.dualNodeEquiv` below,
whose constructor equations do not even elaborate unless `(.A n).dual.rank` reduces to `n`. -/
@[expose] def dual : DynkinType → DynkinType
  | .A n => .A n
  | .B n => .C n
  | .C n => .B n
  | .D n => .D n
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .F4 => .F4
  | .G2 => .G2

@[simp] lemma dual_A (n : ℕ) : (A n).dual = A n := rfl
@[simp] lemma dual_B (n : ℕ) : (B n).dual = C n := rfl
@[simp] lemma dual_C (n : ℕ) : (C n).dual = B n := rfl
@[simp] lemma dual_D (n : ℕ) : (D n).dual = D n := rfl
@[simp] lemma dual_E6 : E6.dual = E6 := rfl
@[simp] lemma dual_E7 : E7.dual = E7 := rfl
@[simp] lemma dual_E8 : E8.dual = E8 := rfl
@[simp] lemma dual_F4 : F4.dual = F4 := rfl
@[simp] lemma dual_G2 : G2.dual = G2 := rfl

/-- Duality is an involution. -/
@[simp] lemma dual_dual (t : DynkinType) : t.dual.dual = t := by cases t <;> rfl

/-- Duality is injective, being an involution; so distinct types stay distinct after dualizing. -/
lemma dual_injective : Function.Injective dual :=
  Function.LeftInverse.injective dual_dual

/-- Duality preserves the rank: it reverses arrows without adding or removing nodes. -/
@[simp] lemma rank_dual (t : DynkinType) : t.dual.rank = t.rank := by cases t <;> rfl

/-- Duality preserves simple-lacedness: a diagram has an arrow to reverse exactly when its dual
does. -/
@[simp] lemma isSimplyLaced_dual (t : DynkinType) : t.dual.IsSimplyLaced ↔ t.IsSimplyLaced := by
  cases t <;> simp

/-- **Validity transfers along duality away from the pair `B 2`, `C 2`.** The excluded pair is the
low-rank coincidence `B 2 = C 2`: both names describe the same root system, and the enumeration
keeps only `B 2` valid. So both orientations of that pair genuinely fail — `B 2` is valid while its
dual `C 2` is not, and `C 2` is not valid while its dual `B 2` is (`simp` proves either from
`TauCeti.DynkinType.valid_B`, `TauCeti.DynkinType.valid_C` and `dual_B`, `dual_C`). No base is lost
by keeping only the first name; see `TauCeti.hasCartanType_dual_iff_of_rank_le_two`. -/
lemma valid_dual_iff {t : DynkinType} (hB : t ≠ B 2) (hC : t ≠ C 2) :
    t.dual.Valid ↔ t.Valid := by
  cases t with
  | B n =>
      have hn : n ≠ 2 := fun h ↦ hB (by rw [h])
      simp only [dual_B, valid_C, valid_B]
      omega
  | C n =>
      have hn : n ≠ 2 := fun h ↦ hC (by rw [h])
      simp only [dual_C, valid_B, valid_C]
      omega
  | _ => simp

/-- **The relabelling of nodes carried by duality.** Transposing a Cartan matrix reverses the
arrows of its diagram, and for the classical families and the `E` types the result is the standard
matrix of the dual type already in the Bourbaki numbering. For `F₄` and `G₂` — the two types that
are self-dual without being simply laced — the reversed diagram is the original one read backwards,
so the relabelling there is `Fin.revPerm`. -/
def dualNodeEquiv : (t : DynkinType) → Fin t.rank ≃ Fin t.dual.rank
  | .A _ => Equiv.refl _
  | .B _ => Equiv.refl _
  | .C _ => Equiv.refl _
  | .D _ => Equiv.refl _
  | .E6 => Equiv.refl _
  | .E7 => Equiv.refl _
  | .E8 => Equiv.refl _
  | .F4 => Fin.revPerm
  | .G2 => Fin.revPerm

-- Stated as equalities of equivalences rather than pointwise: the two sides of a pointwise
-- statement live in `Fin t.rank` and `Fin t.dual.rank`, so its left-hand side would carry a
-- dependent type that `simp` rewrites, leaving it out of simp-normal form. The proofs are
-- parenthesised because `dualNodeEquiv` is not `@[expose]`d, so a bare `rfl` body would demand
-- that its equations be checkable from the exported signature alone.
@[simp] lemma dualNodeEquiv_A (n : ℕ) : (A n).dualNodeEquiv = Equiv.refl (Fin n) := (rfl)
@[simp] lemma dualNodeEquiv_B (n : ℕ) : (B n).dualNodeEquiv = Equiv.refl (Fin n) := (rfl)
@[simp] lemma dualNodeEquiv_C (n : ℕ) : (C n).dualNodeEquiv = Equiv.refl (Fin n) := (rfl)
@[simp] lemma dualNodeEquiv_D (n : ℕ) : (D n).dualNodeEquiv = Equiv.refl (Fin n) := (rfl)
@[simp] lemma dualNodeEquiv_E6 : E6.dualNodeEquiv = Equiv.refl (Fin 6) := (rfl)
@[simp] lemma dualNodeEquiv_E7 : E7.dualNodeEquiv = Equiv.refl (Fin 7) := (rfl)
@[simp] lemma dualNodeEquiv_E8 : E8.dualNodeEquiv = Equiv.refl (Fin 8) := (rfl)
@[simp] lemma dualNodeEquiv_F4 : F4.dualNodeEquiv = Fin.revPerm := (rfl)
@[simp] lemma dualNodeEquiv_G2 : G2.dualNodeEquiv = Fin.revPerm := (rfl)

/-- **The standard Cartan matrix of the dual type is the transpose**, read through the node
relabelling `TauCeti.DynkinType.dualNodeEquiv`. For the simply-laced types the standard matrices
are symmetric and there is nothing to move; for `Bₙ` and `Cₙ` the transposition is
`CartanMatrix.B_transpose`; and for `F₄` and `G₂` the transpose is the matrix itself with its nodes
reversed. -/
@[simp] theorem cartanMatrix_dual (t : DynkinType) (i j : Fin t.rank) :
    t.dual.cartanMatrix (t.dualNodeEquiv i) (t.dualNodeEquiv j) = t.cartanMatrix j i := by
  -- Splitting on `t` leaves the dependent indices to be reduced by hand; `change` carries out that
  -- reduction inside this module, after which the standard matrices are named by the
  -- `cartanMatrix_*` equations.
  cases t with
  | A n =>
      change Fin n at i j
      change (A n).cartanMatrix i j = (A n).cartanMatrix j i
      rw [cartanMatrix_A]
      exact (CartanMatrix.A_isSymm n).apply j i
  | D n =>
      change Fin n at i j
      change (D n).cartanMatrix i j = (D n).cartanMatrix j i
      rw [cartanMatrix_D]
      exact (CartanMatrix.D_isSymm n).apply j i
  | E6 =>
      change E6.cartanMatrix i j = E6.cartanMatrix j i
      rw [cartanMatrix_E6]
      exact (CartanMatrix.E_isSymm 6).apply j i
  | E7 =>
      change E7.cartanMatrix i j = E7.cartanMatrix j i
      rw [cartanMatrix_E7]
      exact (CartanMatrix.E_isSymm 7).apply j i
  | E8 =>
      change E8.cartanMatrix i j = E8.cartanMatrix j i
      rw [cartanMatrix_E8]
      exact (CartanMatrix.E_isSymm 8).apply j i
  | B n =>
      change Fin n at i j
      change (C n).cartanMatrix i j = (B n).cartanMatrix j i
      rw [cartanMatrix_C, cartanMatrix_B, ← CartanMatrix.B_transpose, Matrix.transpose_apply]
  | C n =>
      change Fin n at i j
      change (B n).cartanMatrix i j = (C n).cartanMatrix j i
      rw [cartanMatrix_B, cartanMatrix_C, ← CartanMatrix.C_transpose, Matrix.transpose_apply]
  | F4 =>
      change F4.cartanMatrix i.rev j.rev = F4.cartanMatrix j i
      rw [cartanMatrix_F4]
      fin_cases i <;> fin_cases j <;> decide
  | G2 =>
      change G2.cartanMatrix i.rev j.rev = G2.cartanMatrix j i
      rw [cartanMatrix_G2]
      fin_cases i <;> fin_cases j <;> decide

/-- `TauCeti.DynkinType.cartanMatrix_dual` as an identity of matrices rather than of entries. -/
theorem cartanMatrix_dual_eq_reindex (t : DynkinType) :
    t.dual.cartanMatrix = t.cartanMatrix.transpose.reindex t.dualNodeEquiv t.dualNodeEquiv := by
  ext i j
  simpa using cartanMatrix_dual t (t.dualNodeEquiv.symm i) (t.dualNodeEquiv.symm j)

/-- **Reversing the nodes of a standard Cartan matrix of rank at most two transposes it.** With at
most two indices the only off-diagonal entries form a single transposed pair, which the reversal
swaps, while the diagonal is constant. This is why the orientation built into
`TauCeti.HasCartanType` carries no information at rank at most two. -/
lemma cartanMatrix_rev_of_rank_le_two {t : DynkinType} (ht : t.rank ≤ 2) (i j : Fin t.rank) :
    t.cartanMatrix j.rev i.rev = t.cartanMatrix i j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [cartanMatrix_apply_same, cartanMatrix_apply_same]
  -- Two distinct indices force the rank to be exactly two, and there the reversal is the swap.
  have hrev : ∀ k l : Fin t.rank, k ≠ l → k.rev = l := by
    intro k l hkl
    have hkl' : (k : ℕ) ≠ (l : ℕ) := fun h ↦ hkl (Fin.ext h)
    have hk := k.isLt
    have hl := l.isLt
    exact Fin.ext (by simp only [Fin.val_rev]; omega)
  rw [hrev j i hij.symm, hrev i j hij]

end DynkinType

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **The Cartan type of a flipped base is the dual type.** Flipping transposes the Cartan matrix
(`TauCeti.RootPairing.Base.cartanMatrix_flip`), and transposing a standard Cartan matrix is passing
to the dual type up to the node relabelling `TauCeti.DynkinType.dualNodeEquiv`. -/
theorem HasCartanType.flip {b : P.Base} {t : DynkinType} (h : HasCartanType P b t) :
    HasCartanType P.flip b.flip t.dual := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  refine (hasCartanType_iff _ _).mpr
    ⟨(RootPairing.Base.flipSupportEquiv b).trans (e.trans t.dualNodeEquiv), fun i j ↦ ?_⟩
  simp only [Equiv.trans_apply]
  rw [RootPairing.Base.cartanMatrix_flip b i j, he _ _, DynkinType.cartanMatrix_dual]

/-- **A base has Cartan type `t` exactly when the flipped base has the dual type.** This is what
gives `TauCeti.DynkinType.dual` its meaning: passing from a root system to its dual is passing from
a Dynkin type to its dual. -/
@[simp] theorem hasCartanType_flip_iff {b : P.Base} {t : DynkinType} :
    HasCartanType P.flip b.flip t.dual ↔ HasCartanType P b t := by
  refine ⟨fun h ↦ ?_, HasCartanType.flip⟩
  have h' := h.flip
  rw [DynkinType.dual_dual, RootPairing.Base.flip_flip] at h'
  exact h'

/-- **A base is of type `Bₙ` exactly when the flipped base is of type `Cₙ`.** This is the worked
instance of `TauCeti.hasCartanType_flip_iff`: `Bₙ` and `Cₙ` are the pair of types that the oriented
matching of `TauCeti.HasCartanType` keeps apart, and duality is what identifies them.

It is stated separately from `TauCeti.hasCartanType_flip_iff` because that lemma matches a flipped
type `t.dual` syntactically, so neither `simp` nor `rw` recovers this instance from it: doing so
would mean solving `.C n = ?t.dual` for `?t`. -/
@[simp] theorem hasCartanType_flip_C_iff {b : P.Base} {n : ℕ} :
    HasCartanType P.flip b.flip (.C n) ↔ HasCartanType P b (.B n) :=
  hasCartanType_flip_iff (t := .B n)

/-- The other orientation of `TauCeti.hasCartanType_flip_C_iff`: a base is of type `Cₙ` exactly
when the flipped base is of type `Bₙ`. -/
@[simp] theorem hasCartanType_flip_B_iff {b : P.Base} {n : ℕ} :
    HasCartanType P.flip b.flip (.B n) ↔ HasCartanType P b (.C n) :=
  hasCartanType_flip_iff (t := .C n)

end HasCartanType

section RankLeTwo

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **At rank at most two a base has a Cartan type exactly when it has the dual type.** The
enumeration keeps `B 2` valid and drops `C 2`, and this is what makes that choice harmless: the two
names match exactly the same bases. From rank three on the statement fails, since `Bₙ` and `Cₙ` are
then genuinely different root systems. -/
theorem hasCartanType_dual_iff_of_rank_le_two {b : P.Base} {t : DynkinType} (ht : t.rank ≤ 2) :
    HasCartanType P b t.dual ↔ HasCartanType P b t := by
  -- Both directions are the same computation, so prove the general step once and apply it twice.
  have key : ∀ s : DynkinType, s.rank ≤ 2 → HasCartanType P b s → HasCartanType P b s.dual := by
    intro s hs h
    obtain ⟨e, he⟩ := (hasCartanType_iff b s).mp h
    refine (hasCartanType_iff _ _).mpr ⟨e.trans (Fin.revPerm.trans s.dualNodeEquiv), fun i j ↦ ?_⟩
    rw [he i j]
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    rw [DynkinType.cartanMatrix_dual, DynkinType.cartanMatrix_rev_of_rank_le_two hs]
  refine ⟨fun h ↦ ?_, key t ht⟩
  simpa using key t.dual (by simpa using ht) h

/-- Types `B 2` and `C 2` match exactly the same bases, the low-rank coincidence that
`TauCeti.DynkinType.Valid` resolves by keeping only `B 2`. -/
@[simp] theorem hasCartanType_C_two_iff_B_two {b : P.Base} :
    HasCartanType P b (.C 2) ↔ HasCartanType P b (.B 2) :=
  hasCartanType_dual_iff_of_rank_le_two (t := .B 2) le_rfl

end RankLeTwo

end TauCeti
