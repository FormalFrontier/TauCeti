/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.RepresentationTheory.Induction.PointStabilizer
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic

/-!
# The Young permutation module of the shape `(n-1, 1)`

Among the Young permutation modules `M^μ` of the symmetric group, the shape `μ = (n-1, 1)` is
the one whose tabloids carry no information beyond a single label: a tabloid of that shape is a
splitting of the `n` labels into a row of `n-1` and a row of `1`, so it is named by the label sent
to the short row.  This file proves exactly that, in the form the rest of the theory uses it: the
Young subgroup of `(n-1, 1)` is the stabilizer of a point, so `M^{(n-1,1)}` is the natural
permutation module `ℚ[Fin n]` on the `n` labels.

The shape is `TauCeti.Nat.Partition.singletonSecondRow n`, the partition `(n+1, 1)` of `n+2`; the
offset keeps both parts positive without a hypothesis on `n`.  Its decreasingly sorted parts are
the two-element list `[n+1, 1]`, so the consecutive blocks that `TauCeti.youngSubgroup` cuts
`Fin (n+2)` into are the first `n+1` labels and the last one.  Only the *sizes* of those blocks
enter: counting the labels lying in the first block with `TauCeti.card_filter_youngBlock_lt`
leaves exactly one label outside it, and the block-coordinate equivalence puts `Fin.last (n+1)`
there.  A permutation therefore preserves the blocks exactly when it fixes that label, which is
`TauCeti.fiberSubgroup_eq_stabilizer` applied to the block map.

Everything else is transport.  The cosets of a point stabilizer of a transitive action are the
points (`TauCeti.quotientStabilizerEquiv`), equivariantly, and an equivariant equivalence of
`G`-sets induces an isomorphism of the permutation representations they carry
(`TauCeti.ofMulActionIsoCongr`).  Reading the two invariants of `M^{(n-1,1)}` through that
isomorphism replaces the multinomial dimension `n! / (n-1)!` by `n`, and the count of fixed
tabloids by the count of fixed points -- the natural permutation character.  The permutation
character of a point stabilizer is `1` plus the character of the standard representation, by
`TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`, so the same holds
for `M^{(n-1,1)}`.

## Main definitions

* `TauCeti.singletonSecondRowTabloidEquiv`: the tabloids of `(n+1, 1)` are the labels, the coset
  of `g` naming `g` applied to the last label.
* `TauCeti.permutationModuleSingletonSecondRowIso`: hence `M^{(n+1,1)}` is `ℚ[Fin (n+2)]`.

## Main results

* `TauCeti.youngSubgroup_singletonSecondRow`: **the Young subgroup of `(n+1, 1)` is a point
  stabilizer**, the structural fact everything else follows from, with
  `TauCeti.youngBlock_singletonSecondRow_last` and
  `TauCeti.youngBlock_singletonSecondRow_eq_zero` identifying the two blocks it comes from.
* `TauCeti.finrank_permutationModule_singletonSecondRow`: `M^{(n+1,1)}` has dimension `n+2`.
* `TauCeti.char_permutationModule_singletonSecondRow`: its character counts fixed points, and
  `TauCeti.char_permutationModule_singletonSecondRow_eq_one_add_char_standardRepresentation`:
  that character is `1` plus the character of the standard representation.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4, where
  `M^{(n-1,1)}` is the permutation module on the `n` labels.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
-/

public section

namespace TauCeti

/-! ### The blocks of the shape `(n+1, 1)` -/

/-- Entries of the sorted parts of `(n+1, 1)`, in a form whose index is a bare natural number, so
that rewriting the sorted list does not disturb the bound on the index. -/
private theorem getElem_sort_parts_singletonSecondRow (n i : ℕ)
    (h : i < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length) :
    ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·))[i] = [n + 1, 1].getD i 0 := by
  rw [← List.getD_eq_getElem _ (0 : ℕ) h, Nat.Partition.sort_parts_singletonSecondRow]

/-- **The last label lies in the second block of the shape `(n+1, 1)`.**  The blocks are
consecutive with sizes `n+1` and `1`, so the block-coordinate equivalence sends the single
coordinate of the second block to `Fin.last (n+1)`. -/
theorem youngBlock_singletonSecondRow_last (n : ℕ) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) (Fin.last (n + 1))) : ℕ) = 1 := by
  have hlen := Nat.Partition.length_sort_parts_singletonSecondRow n
  have h1 : (1 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length := by omega
  have h0 : (0 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).get ⟨1, h1⟩ := by
    rw [List.get_eq_getElem, getElem_sort_parts_singletonSecondRow]
    norm_num
  have hlast : youngBlocksEquiv (Nat.Partition.singletonSecondRow n) ⟨⟨1, h1⟩, ⟨0, h0⟩⟩ =
      Fin.last (n + 1) := by
    refine Fin.ext ?_
    rw [youngBlocksEquiv_apply, Fin.sum_univ_one, List.get_eq_getElem,
      getElem_sort_parts_singletonSecondRow]
    norm_num
  rw [← hlast, youngBlock_youngBlocksEquiv]

/-- **Every other label lies in the first block of the shape `(n+1, 1)`.**  The first block has
`n+1` of the `n+2` labels, so its complement is the single label already located by
`TauCeti.youngBlock_singletonSecondRow_last`. -/
theorem youngBlock_singletonSecondRow_eq_zero (n : ℕ) {x : Fin (n + 2)}
    (hx : x ≠ Fin.last (n + 1)) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) x) : ℕ) = 0 := by
  classical
  have hcard : (Finset.univ.filter fun y : Fin (n + 2) =>
      ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card = n + 1 := by
    rw [card_filter_youngBlock_lt, Nat.Partition.sort_parts_singletonSecondRow]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2))))
    (p := fun y => ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1))
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hsum
  by_contra hne
  have hx' : ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) x : ℕ) < 1) := by omega
  have hl' : ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) (Fin.last (n + 1)) : ℕ) < 1) := by
    rw [youngBlock_singletonSecondRow_last]; omega
  have hlt : 1 < (Finset.univ.filter fun y : Fin (n + 2) =>
      ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card :=
    Finset.one_lt_card.mpr ⟨x, by simpa using hx', Fin.last (n + 1), by simpa using hl', hx⟩
  omega

/-- **The Young subgroup of the shape `(n+1, 1)` is a point stabilizer.**  Its blocks are the last
label alone and all the others, so a permutation preserves them exactly when it fixes the last
label. -/
theorem youngSubgroup_singletonSecondRow (n : ℕ) :
    youngSubgroup (Nat.Partition.singletonSecondRow n) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)) := by
  rw [youngSubgroup_eq_fiberSubgroup]
  refine fiberSubgroup_eq_stabilizer (fun x hx h => ?_) (fun x y hx hy => Fin.ext ?_)
  · have hv := congrArg Fin.val h
    rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_last] at hv
    exact absurd hv (by omega)
  · rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_eq_zero n hy]

/-! ### The permutation module of the shape `(n+1, 1)` -/

/-- **The tabloids of the shape `(n+1, 1)` are the points.**  The Young subgroup of `(n+1, 1)` is
the stabilizer of the last label, so the coset of `g` names the point `g` sends that label to. -/
noncomputable def singletonSecondRowTabloidEquiv (n : ℕ) :
    (Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (Nat.Partition.singletonSecondRow n)) ≃
      Fin (n + 2) :=
  (Subgroup.quotientEquivOfEq (youngSubgroup_singletonSecondRow n)).trans
    (quotientStabilizerEquiv (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)))

/-- The tabloid named by `g` is the point `g` sends the last label to. -/
@[simp]
theorem singletonSecondRowTabloidEquiv_mk (n : ℕ) (g : Equiv.Perm (Fin (n + 2))) :
    singletonSecondRowTabloidEquiv n
        (g : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (Nat.Partition.singletonSecondRow n)) =
      g (Fin.last (n + 1)) := by
  rw [singletonSecondRowTabloidEquiv, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
    quotientStabilizerEquiv_mk, Equiv.Perm.smul_def]

/-- The identification of the `(n+1, 1)`-tabloids with the points is equivariant. -/
theorem singletonSecondRowTabloidEquiv_smul (n : ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (q : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (Nat.Partition.singletonSecondRow n)) :
    singletonSecondRowTabloidEquiv n (σ • q) = σ • singletonSecondRowTabloidEquiv n q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, singletonSecondRowTabloidEquiv_mk,
      singletonSecondRowTabloidEquiv_mk, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]

/-- **The Young permutation module of `(n+1, 1)` is the natural permutation module.**  Since the
`(n+1, 1)`-tabloids are the points of `Fin (n+2)`, the module `M^{(n+1,1)}` is `ℚ[Fin (n+2)]` with
the symmetric group permuting the standard basis. -/
noncomputable def permutationModuleSingletonSecondRowIso (n : ℕ) :
    permutationModule (Nat.Partition.singletonSecondRow n) ≅
      Rep.ofMulAction ℚ (Equiv.Perm (Fin (n + 2))) (Fin (n + 2)) :=
  ofMulActionIsoCongr ℚ (singletonSecondRowTabloidEquiv n) (singletonSecondRowTabloidEquiv_smul n)

/-- The isomorphism sends the tabloid named by `g` to the point `g` moves the last label to. -/
@[simp]
theorem permutationModuleSingletonSecondRowIso_hom_hom_single (n : ℕ)
    (g : Equiv.Perm (Fin (n + 2))) (r : ℚ) :
    (permutationModuleSingletonSecondRowIso n).hom.hom
        (MonoidAlgebra.single
          (g : Equiv.Perm (Fin (n + 2)) ⧸ youngSubgroup (Nat.Partition.singletonSecondRow n)) r) =
      MonoidAlgebra.single (g (Fin.last (n + 1))) r := by
  rw [permutationModuleSingletonSecondRowIso, ofMulActionIsoCongr_hom_hom_single,
    singletonSecondRowTabloidEquiv_mk]

/-- The inverse isomorphism sends a point back to the tabloid naming it. -/
@[simp]
theorem permutationModuleSingletonSecondRowIso_inv_hom_single (n : ℕ) (x : Fin (n + 2)) (r : ℚ) :
    (permutationModuleSingletonSecondRowIso n).inv.hom (MonoidAlgebra.single x r) =
      MonoidAlgebra.single ((singletonSecondRowTabloidEquiv n).symm x) r := by
  rw [permutationModuleSingletonSecondRowIso, ofMulActionIsoCongr_inv_hom_single]

/-- **The Young permutation module of `(n+1, 1)` has dimension `n+2`**, the number of points,
rather than the multinomial coefficient `(n+2)! / (n+1)!` in the shape it is presented by. -/
theorem finrank_permutationModule_singletonSecondRow (n : ℕ) :
    Module.finrank ℚ (permutationModule (Nat.Partition.singletonSecondRow n)).V = n + 2 := by
  rw [(Representation.equivOfIso
      (permutationModuleSingletonSecondRowIso n)).toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis (Fin (n + 2)) ℚ), Fintype.card_fin]

/-- **The character of `M^{(n+1,1)}` counts fixed points.**  In the tabloid presentation the
character counts fixed tabloids; for the shape `(n+1, 1)` those are the points of `Fin (n+2)`, so
it is the natural permutation character. -/
theorem char_permutationModule_singletonSecondRow (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationModule (Nat.Partition.singletonSecondRow n)).ρ.character σ =
      (Nat.card {x : Fin (n + 2) // σ x = x} : ℚ) := by
  rw [Representation.char_iso
      (Representation.equivOfIso (permutationModuleSingletonSecondRowIso n)), char_ofMulAction]
  simp only [Equiv.Perm.smul_def]

/-- **The character of `M^{(n+1,1)}` is `1` plus the character of the standard representation.**
This is the character-level form of `M^{(n-1,1)} = triv ⊕ standard`, and it is a specialization of
the point-stabilizer identity
`TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`.  The underlying
splitting of representations is the complementarity of the invariant line and the standard
subrepresentation of `ℚ[Fin (n+2)]`,
`TauCeti.isCompl_invariantLine_augmentationSubrepresentation`, read through
`TauCeti.permutationModuleSingletonSecondRowIso`. -/
theorem char_permutationModule_singletonSecondRow_eq_one_add_char_standardRepresentation (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationModule (Nat.Partition.singletonSecondRow n)).ρ.character σ =
      1 + (standardRepresentation ℚ (Fin (n + 2))).character σ := by
  rw [char_permutationModule_singletonSecondRow, ← char_ind_trivial_stabilizer ℚ (Fin.last (n + 1))]
  exact char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation ℚ _ σ

end TauCeti
