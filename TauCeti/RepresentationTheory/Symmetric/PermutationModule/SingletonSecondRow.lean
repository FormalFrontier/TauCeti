/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.PointStabilizer
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic

/-!
# The Young permutation module of the shape `(n-1, 1)`

Among the Young permutation modules `M^μ` of the symmetric group, the shape `μ = (n-1, 1)` is
the one whose tabloids carry no information beyond a single label: a tabloid of that shape is a
splitting of the `n` labels into a row of `n-1` and a row of `1`, so it is named by the label sent
to the short row.  This file records exactly that, in the form the rest of the theory uses it:
the Young subgroup of `(n-1, 1)` is the stabilizer of a point, so `M^{(n-1,1)}` is the natural
permutation module `ℚ[Fin n]` on the `n` labels, and hence the trivial representation plus the
standard one.

The shape is `TauCeti.Nat.Partition.singletonSecondRow n`, the partition `(n+1, 1)` of `n+2`; the
offset keeps both parts positive without a hypothesis on `n`.  The structural fact this file rests
on is proved with the rest of the Young-subgroup theory, in
`TauCeti.RepresentationTheory.Symmetric.YoungSubgroup`: the two blocks of `(n+1, 1)` are all the
labels but the last one and the last one alone, so
`TauCeti.youngSubgroup_singletonSecondRow` identifies the Young subgroup with the stabilizer of
`Fin.last (n+1)`.

Everything here is transport.  The cosets of a point stabilizer of a transitive action are the
points (`TauCeti.quotientStabilizerEquiv`), equivariantly, and an equivariant equivalence of
`G`-sets induces an isomorphism of the permutation representations they carry
(`TauCeti.ofMulActionIsoCongr`).  Reading the two invariants of `M^{(n-1,1)}` through that
isomorphism replaces the multinomial dimension `n! / (n-1)!` by `n`, and the count of fixed
tabloids by the count of fixed points -- the natural permutation character.  Splitting
`ℚ[Fin (n+2)]` into the invariant line and the augmentation subrepresentation
(`TauCeti.ofMulActionEquivProdAugmentation`) then decomposes `M^{(n-1,1)}` as the trivial
representation plus the standard representation.  On characters that decomposition is the
point-stabilizer identity
`TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`.

## Main definitions

* `TauCeti.singletonSecondRowTabloidEquiv`: the tabloids of `(n+1, 1)` are the labels, the coset
  of `g` naming `g` applied to the last label.
* `TauCeti.permutationModuleSingletonSecondRowIso`: hence `M^{(n+1,1)}` is `ℚ[Fin (n+2)]`.
* `TauCeti.permutationModuleSingletonSecondRowEquivProd`: **`M^{(n-1,1)} = triv ⊕ standard`**, an
  equivalence of representations onto the product of the trivial representation on `ℚ` and the
  standard representation, computed by
  `TauCeti.permutationModuleSingletonSecondRowEquivProd_apply` as the splitting of `ℚ[Fin (n+2)]`
  at the transported vector.

## Main results

* `TauCeti.finrank_permutationModule_singletonSecondRow`: `M^{(n+1,1)}` has dimension `n+2`.
* `TauCeti.char_permutationModule_singletonSecondRow`: its character counts fixed points, and
  `TauCeti.char_permutationModule_singletonSecondRow_eq_one_add_char_standardRepresentation`:
  that character is `1` plus the character of the standard representation.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4, where
  `M^{(n-1,1)}` is the permutation module on the `n` labels.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "The named small irreducibles", which asks for `M^{(n-1,1)} = triv ⊕ standard`.
-/

public section

namespace TauCeti

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
@[simp]
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
@[simp]
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

/-! ### The decomposition `M^{(n+1,1)} = triv ⊕ standard` -/

/-- **The Young permutation module of `(n+1, 1)` is the trivial representation plus the standard
representation.**  Transporting `M^{(n+1,1)}` to `ℚ[Fin (n+2)]` along
`TauCeti.permutationModuleSingletonSecondRowIso` and splitting the latter along
`TauCeti.ofMulActionEquivProdAugmentation` -- the invariant line, which carries the trivial
representation on `ℚ` itself, is a complement of the augmentation subrepresentation, `n+2` being
invertible in `ℚ` -- decomposes it as a product of two representations, the second being the
standard representation by `TauCeti.toRepresentation_augmentationSubrepresentation`.  In short,
`M^{(n-1,1)} = triv ⊕ standard`. -/
noncomputable def permutationModuleSingletonSecondRowEquivProd (n : ℕ) :
    (permutationModule (Nat.Partition.singletonSecondRow n)).ρ.Equiv
      ((Representation.trivial ℚ (Equiv.Perm (Fin (n + 2))) ℚ).prod
        (standardRepresentation ℚ (Fin (n + 2)))) :=
  (Representation.equivOfIso (permutationModuleSingletonSecondRowIso n)).trans
    ((ofMulActionEquivProdAugmentation ℚ (Equiv.Perm (Fin (n + 2))) (Fin (n + 2))
        (by rw [Fintype.card_fin]; positivity)).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℚ _) fun g => by
        rw [toRepresentation_augmentationSubrepresentation]
        simp))

/-- **The decomposition is the splitting of `ℚ[Fin (n+2)]`, read through the identification of the
tabloids with the labels.**  The two components of a vector are therefore computed by
`TauCeti.ofMulActionEquivProdAugmentation_apply_fst` and
`TauCeti.coe_ofMulActionEquivProdAugmentation_apply_snd` at the vector of `ℚ[Fin (n+2)]` that
`TauCeti.permutationModuleSingletonSecondRowIso` transports it to, which for the tabloid named by
`g` is the standard basis vector of `g (Fin.last (n+1))`. -/
@[simp]
theorem permutationModuleSingletonSecondRowEquivProd_apply (n : ℕ)
    (v : (permutationModule (Nat.Partition.singletonSecondRow n)).V) :
    permutationModuleSingletonSecondRowEquivProd n v =
      ofMulActionEquivProdAugmentation ℚ (Equiv.Perm (Fin (n + 2))) (Fin (n + 2))
        (by rw [Fintype.card_fin]; positivity)
        ((permutationModuleSingletonSecondRowIso n).hom.hom v) :=
  -- `(rfl)`, not `rfl`: the body of `permutationModuleSingletonSecondRowEquivProd` is not
  -- `@[expose]`d, so this must not be inferred `@[defeq]`.
  (rfl)

/-- **The character of `M^{(n+1,1)}` is `1` plus the character of the standard representation.**
This is the character-level form of the decomposition
`TauCeti.permutationModuleSingletonSecondRowEquivProd`, and it is a specialization of the
point-stabilizer identity
`TauCeti.char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation`. -/
theorem char_permutationModule_singletonSecondRow_eq_one_add_char_standardRepresentation (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    (permutationModule (Nat.Partition.singletonSecondRow n)).ρ.character σ =
      1 + (standardRepresentation ℚ (Fin (n + 2))).character σ := by
  rw [char_permutationModule_singletonSecondRow, ← char_ind_trivial_stabilizer ℚ (Fin.last (n + 1))]
  exact char_ind_trivial_stabilizer_eq_one_add_char_standardRepresentation ℚ _ σ

end TauCeti
