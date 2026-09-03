/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic
public import TauCeti.RepresentationTheory.Symmetric.Standard

/-!
# The Young permutation module of the two-row shape `(n-1, 1)`

Among the Young permutation modules `M^μ` of the symmetric group, the shape `μ = (n-1, 1)` is
the one whose tabloids carry no information beyond a single label: a tabloid of that shape is a
splitting of the `n` labels into a row of `n-1` and a row of `1`, so it is named by the label sent
to the short row.  This file proves exactly that, in the form the rest of the theory uses it: the
Young subgroup of `(n-1, 1)` is the stabilizer of a point, so `M^{(n-1,1)}` is the natural
permutation module `ℚ[Fin n]` on the `n` labels.

The shape is written here as `TauCeti.twoRowPartition n`, the partition `(n+1, 1)` of `n+2`; the
offset keeps both parts positive without a hypothesis, and it is the only shape with two rows and
a single box in the second.  Its decreasingly sorted parts are the two-element list `[n+1, 1]`, so
the consecutive blocks that `TauCeti.youngSubgroup` cuts `Fin (n+2)` into are the first `n+1`
labels and the last one.  Only the *sizes* of those blocks enter: counting the labels lying in the
first block with `TauCeti.card_filter_youngBlock_lt` leaves exactly one label outside it, and the
block-coordinate equivalence puts `Fin.last (n+1)` there.  A permutation therefore preserves the
blocks exactly when it fixes that label, which is
`TauCeti.fiberSubgroup_eq_stabilizer` applied to the block map.

Everything else is transport.  The cosets of a point stabilizer of a transitive action are the
points (`TauCeti.quotientStabilizerEquiv`), equivariantly, and an equivariant equivalence of
`G`-sets induces an isomorphism of the permutation representations they carry
(`TauCeti.ofMulActionIsoCongr`).  Reading the two invariants of `M^{(n-1,1)}` through that
isomorphism replaces the multinomial dimension `n! / (n-1)!` by `n`, and the count of fixed
tabloids by the count of fixed points -- the natural permutation character.  Since `ℚ[Fin n]`
splits as the invariant line plus the standard representation
(`TauCeti.isCompl_invariantLine_augmentationSubrepresentation` and
`TauCeti.standardRepresentation`), this is the identification `M^{(n-1,1)} = triv ⊕ standard` that
the Schur-Weyl roadmap asks for, and it is recorded on characters as
`TauCeti.char_permutationModule_twoRowPartition_eq_one_add`.

The companion identification `S^{(n-1,1)} = standard` of the *Specht* module of this shape is a
further step and is not proved here: it needs the polytabloids of a two-row tableau, and the
tableau combinatorics is indexed by a Young diagram rather than by a partition, so it is stated in
the Specht files.

## Main definitions

* `TauCeti.twoRowPartition`: the partition `(n+1, 1)` of `n+2`.
* `TauCeti.twoRowTabloidEquiv`: its tabloids are the labels, the coset of `g` naming `g` applied to
  the last label.
* `TauCeti.permutationModuleTwoRowIso`: hence `M^{(n+1,1)}` is `ℚ[Fin (n+2)]`.

## Main results

* `TauCeti.youngSubgroup_twoRowPartition`: **the Young subgroup of `(n+1, 1)` is a point
  stabilizer**, the structural fact everything else follows from, with
  `TauCeti.youngBlock_twoRowPartition_last` and `TauCeti.youngBlock_twoRowPartition_eq_zero`
  identifying the two blocks it comes from.
* `TauCeti.finrank_permutationModule_twoRowPartition`: `M^{(n+1,1)}` has dimension `n+2`.
* `TauCeti.char_permutationModule_twoRowPartition`: its character counts fixed points, and
  `TauCeti.char_permutationModule_twoRowPartition_eq_one_add`: that character is `1` plus the
  character of the standard representation, which is the decomposition `triv ⊕ standard`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4, where
  `M^{(n-1,1)}` is the permutation module on the `n` labels.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles", which asks for `M^{(n-1,1)} = triv ⊕ standard`.
-/

public section

namespace TauCeti

/-! ### The shape `(n+1, 1)` and its blocks -/

/-- The **two-row partition** `(n+1, 1)` of `n+2`: the unique shape with two rows whose second row
is a single box.  Writing it at `n+2` rather than as `(n-1, 1)` at `n` keeps both parts positive
with no hypothesis on `n`. -/
def twoRowPartition (n : ℕ) : (n + 2).Partition where
  parts := {n + 1, 1}
  parts_pos := by
    intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> omega
  parts_sum := by simp

/-- The parts of the two-row partition. -/
@[simp]
theorem twoRowPartition_parts (n : ℕ) : (twoRowPartition n).parts = {n + 1, 1} := (rfl)

/-- The decreasingly sorted parts of `(n+1, 1)`, which are what cut `Fin (n+2)` into the two
consecutive Young blocks. -/
theorem sort_parts_twoRowPartition (n : ℕ) :
    (twoRowPartition n).parts.sort (· ≥ ·) = [n + 1, 1] := by
  rw [twoRowPartition_parts, Multiset.insert_eq_cons,
    Multiset.sort_cons _ _ _ (by simp), Multiset.sort_singleton]

/-- The two-row shape has two blocks. -/
theorem length_sort_parts_twoRowPartition (n : ℕ) :
    ((twoRowPartition n).parts.sort (· ≥ ·)).length = 2 := by
  rw [sort_parts_twoRowPartition]
  rfl

/-- Entries of the sorted parts of `(n+1, 1)`, in a form whose index is a bare natural number, so
that rewriting the sorted list does not disturb the bound on the index. -/
private theorem getElem_sort_parts_twoRowPartition (n i : ℕ)
    (h : i < ((twoRowPartition n).parts.sort (· ≥ ·)).length) :
    ((twoRowPartition n).parts.sort (· ≥ ·))[i] = [n + 1, 1].getD i 0 := by
  rw [← List.getD_eq_getElem _ (0 : ℕ) h, sort_parts_twoRowPartition]

/-- **The last label lies in the second block of the two-row shape.**  The blocks are consecutive
with sizes `n+1` and `1`, so the block-coordinate equivalence sends the single coordinate of the
second block to `Fin.last (n+1)`. -/
theorem youngBlock_twoRowPartition_last (n : ℕ) :
    ((youngBlock (twoRowPartition n) (Fin.last (n + 1))) : ℕ) = 1 := by
  have hlen := length_sort_parts_twoRowPartition n
  have h1 : (1 : ℕ) < ((twoRowPartition n).parts.sort (· ≥ ·)).length := by omega
  have h0 : (0 : ℕ) < ((twoRowPartition n).parts.sort (· ≥ ·)).get ⟨1, h1⟩ := by
    rw [List.get_eq_getElem, getElem_sort_parts_twoRowPartition]
    norm_num
  have hlast : youngBlocksEquiv (twoRowPartition n) ⟨⟨1, h1⟩, ⟨0, h0⟩⟩ = Fin.last (n + 1) := by
    refine Fin.ext ?_
    rw [youngBlocksEquiv_apply, Fin.sum_univ_one, List.get_eq_getElem,
      getElem_sort_parts_twoRowPartition]
    norm_num
  rw [← hlast, youngBlock_youngBlocksEquiv]

/-- **Every other label lies in the first block of the two-row shape.**  The first block has `n+1`
of the `n+2` labels, so its complement is the single label already located by
`TauCeti.youngBlock_twoRowPartition_last`. -/
theorem youngBlock_twoRowPartition_eq_zero (n : ℕ) {x : Fin (n + 2)} (hx : x ≠ Fin.last (n + 1)) :
    ((youngBlock (twoRowPartition n) x) : ℕ) = 0 := by
  classical
  have hcard : (Finset.univ.filter fun y : Fin (n + 2) =>
      ((youngBlock (twoRowPartition n) y : ℕ) < 1)).card = n + 1 := by
    rw [card_filter_youngBlock_lt, sort_parts_twoRowPartition]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2))))
    (p := fun y => ((youngBlock (twoRowPartition n) y : ℕ) < 1))
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hsum
  by_contra hne
  have hx' : ¬ ((youngBlock (twoRowPartition n) x : ℕ) < 1) := by omega
  have hl' : ¬ ((youngBlock (twoRowPartition n) (Fin.last (n + 1)) : ℕ) < 1) := by
    rw [youngBlock_twoRowPartition_last]; omega
  have hlt : 1 < (Finset.univ.filter fun y : Fin (n + 2) =>
      ¬ ((youngBlock (twoRowPartition n) y : ℕ) < 1)).card :=
    Finset.one_lt_card.mpr ⟨x, by simpa using hx', Fin.last (n + 1), by simpa using hl', hx⟩
  omega

/-- **The Young subgroup of the two-row shape is a point stabilizer.**  Its blocks are the last
label alone and all the others, so a permutation preserves them exactly when it fixes the last
label. -/
theorem youngSubgroup_twoRowPartition (n : ℕ) :
    youngSubgroup (twoRowPartition n) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)) := by
  rw [youngSubgroup_eq_fiberSubgroup]
  refine fiberSubgroup_eq_stabilizer (fun x hx h => ?_) (fun x y hx hy => Fin.ext ?_)
  · have hv := congrArg Fin.val h
    rw [youngBlock_twoRowPartition_eq_zero n hx, youngBlock_twoRowPartition_last] at hv
    exact absurd hv (by omega)
  · rw [youngBlock_twoRowPartition_eq_zero n hx, youngBlock_twoRowPartition_eq_zero n hy]

/-! ### The permutation module of the two-row shape -/

/-- **The tabloids of the two-row shape are the points.**  The Young subgroup of `(n+1, 1)` is the
stabilizer of the last label, so the coset of `g` names the point `g` sends that label to. -/
noncomputable def twoRowTabloidEquiv (n : ℕ) :
    (Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (twoRowPartition n)) ≃ Fin (n + 2) :=
  (Subgroup.quotientEquivOfEq (youngSubgroup_twoRowPartition n)).trans
    (quotientStabilizerEquiv (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)))

/-- The tabloid named by `g` is the point `g` sends the last label to. -/
@[simp]
theorem twoRowTabloidEquiv_mk (n : ℕ) (g : Equiv.Perm (Fin (n + 2))) :
    twoRowTabloidEquiv n (g : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (twoRowPartition n)) =
      g (Fin.last (n + 1)) := by
  rw [twoRowTabloidEquiv, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
    quotientStabilizerEquiv_mk, Equiv.Perm.smul_def]

/-- The identification of the two-row tabloids with the points is equivariant. -/
theorem twoRowTabloidEquiv_smul (n : ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (q : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (twoRowPartition n)) :
    twoRowTabloidEquiv n (σ • q) = σ • twoRowTabloidEquiv n q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, twoRowTabloidEquiv_mk, twoRowTabloidEquiv_mk,
      Equiv.Perm.smul_def, Equiv.Perm.mul_apply]

/-- **The two-row Young permutation module is the natural permutation module.**  Since the
`(n+1, 1)`-tabloids are the points of `Fin (n+2)`, the module `M^{(n+1,1)}` is `ℚ[Fin (n+2)]` with
the symmetric group permuting the standard basis. -/
noncomputable def permutationModuleTwoRowIso (n : ℕ) :
    permutationModule (twoRowPartition n) ≅
      Rep.ofMulAction ℚ (Equiv.Perm (Fin (n + 2))) (Fin (n + 2)) :=
  ofMulActionIsoCongr ℚ (twoRowTabloidEquiv n) (twoRowTabloidEquiv_smul n)

/-- The isomorphism sends the tabloid named by `g` to the point `g` moves the last label to. -/
@[simp]
theorem permutationModuleTwoRowIso_hom_hom_single (n : ℕ) (g : Equiv.Perm (Fin (n + 2))) (r : ℚ) :
    (permutationModuleTwoRowIso n).hom.hom
        (MonoidAlgebra.single (g : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (twoRowPartition n))
          r) =
      MonoidAlgebra.single (g (Fin.last (n + 1))) r := by
  rw [permutationModuleTwoRowIso, ofMulActionIsoCongr_hom_hom_single, twoRowTabloidEquiv_mk]

/-- The inverse isomorphism sends a point back to the tabloid naming it. -/
@[simp]
theorem permutationModuleTwoRowIso_inv_hom_single (n : ℕ) (x : Fin (n + 2)) (r : ℚ) :
    (permutationModuleTwoRowIso n).inv.hom (MonoidAlgebra.single x r) =
      MonoidAlgebra.single ((twoRowTabloidEquiv n).symm x) r := by
  rw [permutationModuleTwoRowIso, ofMulActionIsoCongr_inv_hom_single]

/-- **The two-row Young permutation module has dimension `n+2`**, the number of points, rather
than the multinomial coefficient `(n+2)! / (n+1)!` in the shape it is presented by. -/
theorem finrank_permutationModule_twoRowPartition (n : ℕ) :
    Module.finrank ℚ (permutationModule (twoRowPartition n)).V = n + 2 := by
  rw [finrank_permutationModule, twoRowPartition_parts]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, Nat.factorial_one, mul_one]
  rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ]
  exact Nat.mul_div_cancel _ (Nat.factorial_pos _)

/-- **The character of `M^{(n+1,1)}` counts fixed points.**  In the tabloid presentation the
character counts fixed tabloids; for the two-row shape those are the points of `Fin (n+2)`, so it
is the natural permutation character. -/
theorem char_permutationModule_twoRowPartition (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationModule (twoRowPartition n)).ρ.character σ =
      (Nat.card {x : Fin (n + 2) // σ x = x} : ℚ) := by
  rw [char_permutationModule]
  refine congrArg _ (Nat.card_congr (Equiv.subtypeEquiv (twoRowTabloidEquiv n) fun q => ?_))
  rw [← Equiv.apply_eq_iff_eq (twoRowTabloidEquiv n) (x := σ • q) (y := q),
    twoRowTabloidEquiv_smul, Equiv.Perm.smul_def]

/-- **`M^{(n+1,1)}` is the trivial representation plus the standard representation**, read on
characters: its character is `1` plus the character of the standard representation of `Sₙ₊₂`.  The
underlying decomposition is the splitting of `ℚ[Fin (n+2)]` into the invariant line and the
standard subrepresentation. -/
theorem char_permutationModule_twoRowPartition_eq_one_add (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationModule (twoRowPartition n)).ρ.character σ =
      1 + (standardRepresentation ℚ (Fin (n + 2))).character σ := by
  rw [char_permutationModule_twoRowPartition, char_standardRepresentation, char_ofMulAction]
  simp [Equiv.Perm.smul_def]

end TauCeti
