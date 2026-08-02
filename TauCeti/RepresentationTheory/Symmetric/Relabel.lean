/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Symmetric.SpechtIdeal

/-!
# Relabeling a Young tableau conjugates its Young symmetrizer

A Young symmetrizer, and with it the left ideal `ℚ[Sₙ] c_t` it generates, is built from a
`μ`-tableau `t`, while the Specht module it presents is meant to depend only on the shape `μ`.
This file supplies that independence.

Relabeling the labels of `t` by a permutation `σ` conjugates the row group and the column group
of `t`, hence conjugates the row symmetrizer, the column antisymmetrizer, and the Young
symmetrizer:

`c_{σt} = σ c_t σ⁻¹`.

Consequently `ℚ[Sₙ] c_{σt} = (ℚ[Sₙ] c_t) σ⁻¹`, and right multiplication by `σ` is an isomorphism
of representations from `ℚ[Sₙ] c_{σt}` to `ℚ[Sₙ] c_t`.  Since any two tableaux of the same shape
differ by a relabeling, the representation `ℚ[Sₙ] c_t`, and in particular its dimension and its
character, depend only on the shape of `t`.

## Main results

* `YoungTableau.youngSymmetrizer_relabel`: the Young symmetrizer of a relabeled tableau is the
  conjugate of the Young symmetrizer, and `YoungTableau.youngSymmetrizerOver_relabel` says the
  same for its transport to a `ℚ`-algebra.
* `YoungTableau.spechtIdealRelabelRepEquiv`: right multiplication by `σ` as an isomorphism of
  representations `ℚ[Sₙ] c_{σt} ≅ ℚ[Sₙ] c_t`.
* `YoungTableau.spechtIdealRepIso`, `YoungTableau.finrank_spechtIdeal_eq` and
  `YoungTableau.character_spechtIdealRep_eq`: the representation, its dimension, and its character
  depend only on the shape of the tableau.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layers 2 and 3: the Layer 3 Specht module `spechtModule μ` is indexed by the shape `μ` alone,
  while the Layer 2 Young symmetrizer and its left ideal are built from a tableau, so the
  tableau-independence proved here is what makes the Layer 3 indexing legitimate.
-/

public section

namespace TauCeti

namespace YoungTableau

section GroupAlgebra

variable {G : Type*} [Group G]

/-- The group-algebra basis element of `g`, as a unit whose inverse is the basis element of `g⁻¹`.
Private: this is the group-algebra plumbing for the conjugation computations and for the
right-translation equivalence below. -/
private noncomputable def singleUnit (g : G) : (MonoidAlgebra ℚ G)ˣ :=
  Units.map (MonoidAlgebra.of ℚ G) (toUnits g)

@[simp]
private theorem coe_singleUnit (g : G) :
    ((singleUnit g : (MonoidAlgebra ℚ G)ˣ) : MonoidAlgebra ℚ G) = MonoidAlgebra.single g 1 :=
  rfl

@[simp]
private theorem coe_inv_singleUnit (g : G) :
    (((singleUnit g)⁻¹ : (MonoidAlgebra ℚ G)ˣ) : MonoidAlgebra ℚ G) =
      MonoidAlgebra.single g⁻¹ 1 :=
  rfl

/-- Conjugating in the group algebra conjugates the indices of the coefficients.  Private: this is
group-algebra plumbing for the conjugation computations below. -/
private theorem coeff_conj (g h : G) (x : MonoidAlgebra ℚ G) :
    (MonoidAlgebra.single g (1 : ℚ) * x * MonoidAlgebra.single g⁻¹ 1).coeff h =
      x.coeff (g⁻¹ * h * g) := by
  simp [mul_assoc]

end GroupAlgebra

variable {μ : YoungDiagram} (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)

/-! ## The row and column groups of a relabeled tableau -/

/-- Relabeling by `σ` conjugates the row group by `σ`. -/
theorem rowSubgroup_relabel :
    rowSubgroup (relabel σ t) = (rowSubgroup t).map (MulAut.conj σ).toMonoidHom := by
  rw [rowSubgroup_def, rowSubgroup_def]
  exact (fiberSubgroup_map_conj σ fun _ _ => by simp).symm

/-- Relabeling by `σ` conjugates the column group by `σ`. -/
theorem colSubgroup_relabel :
    colSubgroup (relabel σ t) = (colSubgroup t).map (MulAut.conj σ).toMonoidHom := by
  rw [colSubgroup_def, colSubgroup_def]
  exact (fiberSubgroup_map_conj σ fun _ _ => by simp).symm

/-- A permutation preserves the rows of the relabeled tableau exactly when its conjugate preserves
the rows of the original one.

Not a `simp` lemma: `mem_rowSubgroup` and `rowIndex_relabel` already simplify the left-hand side
past this normal form, to the pointwise condition on rows. -/
theorem mem_rowSubgroup_relabel {τ : Equiv.Perm (Fin μ.card)} :
    τ ∈ rowSubgroup (relabel σ t) ↔ σ⁻¹ * τ * σ ∈ rowSubgroup t := by
  rw [rowSubgroup_relabel, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- A permutation preserves the columns of the relabeled tableau exactly when its conjugate
preserves the columns of the original one.

Not a `simp` lemma: `mem_colSubgroup` and `colIndex_relabel` already simplify the left-hand side
past this normal form, to the pointwise condition on columns. -/
theorem mem_colSubgroup_relabel {τ : Equiv.Perm (Fin μ.card)} :
    τ ∈ colSubgroup (relabel σ t) ↔ σ⁻¹ * τ * σ ∈ colSubgroup t := by
  rw [colSubgroup_relabel, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-! ## The symmetrizers of a relabeled tableau -/

/-- Relabeling by `σ` conjugates the row symmetrizer by `σ`. -/
@[simp]
theorem rowSymmetrizer_relabel :
    rowSymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * rowSymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  ext τ
  rw [coeff_conj, rowSymmetrizer_coeff, rowSymmetrizer_coeff]
  by_cases h : σ⁻¹ * τ * σ ∈ rowSubgroup t
  · rw [if_pos h, if_pos ((mem_rowSubgroup_relabel σ t).mpr h)]
  · rw [if_neg h, if_neg fun hτ => h ((mem_rowSubgroup_relabel σ t).mp hτ)]

/-- Relabeling by `σ` conjugates the column antisymmetrizer by `σ`; the signs are unchanged,
conjugate permutations having equal signs. -/
@[simp]
theorem columnAntisymmetrizer_relabel :
    columnAntisymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * columnAntisymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  ext τ
  rw [coeff_conj, columnAntisymmetrizer_coeff, columnAntisymmetrizer_coeff]
  have hsign : Equiv.Perm.sign (σ⁻¹ * τ * σ) = Equiv.Perm.sign τ := by
    rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]
  by_cases h : σ⁻¹ * τ * σ ∈ colSubgroup t
  · rw [if_pos h, if_pos ((mem_colSubgroup_relabel σ t).mpr h), hsign]
  · rw [if_neg h, if_neg fun hτ => h ((mem_colSubgroup_relabel σ t).mp hτ)]

/-- Relabeling by `σ` conjugates the Young symmetrizer by `σ`: `c_{σt} = σ c_t σ⁻¹`. -/
@[simp]
theorem youngSymmetrizer_relabel :
    youngSymmetrizer (relabel σ t) =
      MonoidAlgebra.single σ 1 * youngSymmetrizer t * MonoidAlgebra.single σ⁻¹ 1 := by
  have hσ : MonoidAlgebra.single σ⁻¹ (1 : ℚ) * MonoidAlgebra.single σ 1 = 1 := by
    simpa using (singleUnit σ).inv_mul
  rw [youngSymmetrizer_def, youngSymmetrizer_def, rowSymmetrizer_relabel,
    columnAntisymmetrizer_relabel]
  simp only [mul_assoc]
  rw [← mul_assoc (MonoidAlgebra.single σ⁻¹ (1 : ℚ)), hσ, one_mul]

/-- Relabeling by `σ` conjugates the transported Young symmetrizer, as it does the rational
one. -/
theorem youngSymmetrizerOver_relabel (k : Type*) [CommSemiring k] [Algebra ℚ k] :
    youngSymmetrizerOver k (relabel σ t) =
      MonoidAlgebra.single σ 1 * youngSymmetrizerOver k t * MonoidAlgebra.single σ⁻¹ 1 := by
  rw [youngSymmetrizerOver_def, youngSymmetrizerOver_def, youngSymmetrizer_relabel, map_mul,
    map_mul, MonoidAlgebra.mapAlgHom_single, MonoidAlgebra.mapAlgHom_single, map_one]

/-! ## The Young-symmetrizer left ideal of a relabeled tableau -/

/-- Membership in the left ideal generated by `c_{σt}` is membership in the right translate by
`σ⁻¹` of the left ideal generated by `c_t`. -/
theorem mem_spechtIdeal_relabel_iff {x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))} :
    x ∈ spechtIdeal (relabel σ t) ↔ x * MonoidAlgebra.single σ 1 ∈ spechtIdeal t := by
  have hσ : MonoidAlgebra.single σ⁻¹ (1 : ℚ) * MonoidAlgebra.single σ 1 = 1 := by
    simpa using (singleUnit σ).inv_mul
  have hσ' : MonoidAlgebra.single σ (1 : ℚ) * MonoidAlgebra.single σ⁻¹ 1 = 1 := by
    simpa using (singleUnit σ).mul_inv
  rw [mem_spechtIdeal_iff, mem_spechtIdeal_iff]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a * MonoidAlgebra.single σ 1, ?_⟩
    rw [youngSymmetrizer_relabel]
    simp only [mul_assoc, hσ, mul_one]
  · rintro ⟨b, hb⟩
    refine ⟨b * MonoidAlgebra.single σ⁻¹ 1, ?_⟩
    rw [youngSymmetrizer_relabel]
    simp only [mul_assoc]
    rw [← mul_assoc (MonoidAlgebra.single σ⁻¹ (1 : ℚ)), hσ, one_mul,
      ← mul_assoc, hb, mul_assoc, hσ', mul_one]

noncomputable section

/-- Right multiplication by `σ` as an equivalence of left `ℚ[Sₙ]`-modules from `ℚ[Sₙ] c_{σt}` to
`ℚ[Sₙ] c_t`: it is right multiplication by the unit `σ` of the group algebra, restricted to the
two ideals. -/
def spechtIdealRelabelEquiv :
    spechtIdeal (relabel σ t) ≃ₗ[MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))] spechtIdeal t :=
  (Units.mulRightLinearEquiv (MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
      (singleUnit σ)).ofSubmodules _ _ <| by
    refine Submodule.ext fun x => ?_
    rw [Submodule.mem_map_equiv, Units.symm_mulRightLinearEquiv_apply,
      mem_spechtIdeal_relabel_iff, ← coe_singleUnit σ, Units.inv_mul_cancel_right]

@[simp]
theorem spechtIdealRelabelEquiv_apply_coe (x : spechtIdeal (relabel σ t)) :
    (spechtIdealRelabelEquiv σ t x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelEquiv, LinearEquiv.ofSubmodules_apply,
    Units.mulRightLinearEquiv_apply, coe_singleUnit]

@[simp]
theorem spechtIdealRelabelEquiv_symm_apply_coe (y : spechtIdeal t) :
    ((spechtIdealRelabelEquiv σ t).symm y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (y : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ⁻¹ 1 := by
  rw [spechtIdealRelabelEquiv, LinearEquiv.ofSubmodules_symm_apply,
    Units.symm_mulRightLinearEquiv_apply, coe_inv_singleUnit]

/-- Right multiplication by `σ` is an isomorphism of representations from `ℚ[Sₙ] c_{σt}` to
`ℚ[Sₙ] c_t`: being a map of left modules over the group algebra, it commutes with the action. -/
def spechtIdealRelabelRepEquiv :
    (spechtIdealRep (relabel σ t)).ρ.Equiv (spechtIdealRep t).ρ :=
  Representation.Equiv.mk ((spechtIdealRelabelEquiv σ t).restrictScalars ℚ) fun g =>
    -- the action of `g` is the scalar action of `single g 1`, which a map of left modules over the
    -- group algebra respects
    LinearMap.ext fun x => (spechtIdealRelabelEquiv σ t).map_smul (MonoidAlgebra.single g 1) x

@[simp]
theorem spechtIdealRelabelRepEquiv_apply_coe (x : spechtIdeal (relabel σ t)) :
    (spechtIdealRelabelRepEquiv σ t x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelRepEquiv, Representation.Equiv.mk_apply,
    LinearEquiv.restrictScalars_apply, spechtIdealRelabelEquiv_apply_coe]

/-- The left ideals of the Young symmetrizers of a tableau and of its relabelings are isomorphic
representations. -/
def spechtIdealRelabelRepIso : spechtIdealRep (relabel σ t) ≅ spechtIdealRep t :=
  Rep.mkIso (spechtIdealRelabelRepEquiv σ t)

@[simp]
theorem spechtIdealRelabelRepIso_hom_hom_apply_coe (x : spechtIdeal (relabel σ t)) :
    ((spechtIdealRelabelRepIso σ t).hom.hom x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) =
      (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) * MonoidAlgebra.single σ 1 := by
  rw [spechtIdealRelabelRepIso, Rep.mkIso_hom_hom_apply, Representation.Equiv.coe_toLinearMap,
    spechtIdealRelabelRepEquiv_apply_coe]

end

/-- Relabeling does not change the dimension of the Young-symmetrizer left ideal. -/
@[simp]
theorem finrank_spechtIdeal_relabel :
    Module.finrank ℚ (spechtIdeal (relabel σ t)) = Module.finrank ℚ (spechtIdeal t) :=
  ((spechtIdealRelabelEquiv σ t).restrictScalars ℚ).finrank_eq

/-- Relabeling does not change the character of the Young-symmetrizer left ideal. -/
@[simp]
theorem character_spechtIdealRep_relabel :
    (spechtIdealRep (relabel σ t)).ρ.character = (spechtIdealRep t).ρ.character :=
  Representation.char_iso (spechtIdealRelabelRepEquiv σ t)

/-- Relabeling does not change the character of the bundled Young-symmetrizer representation. -/
@[simp]
theorem character_spechtIdealFDRep_relabel :
    (spechtIdealFDRep (relabel σ t)).character = (spechtIdealFDRep t).character :=
  -- bundling leaves both the module and the action alone, so the two characters are the same
  -- function, as in `char_permutationModuleFDRep`
  character_spechtIdealRep_relabel σ t

/-! ## Independence of the tableau -/

variable (t' : YoungTableau μ)

/-- The Young-symmetrizer left ideals of two tableaux of the same shape are isomorphic
representations: up to isomorphism the representation depends only on the shape. -/
noncomputable def spechtIdealRepIso : spechtIdealRep t ≅ spechtIdealRep t' :=
  -- `t'` is the relabeling of `t` by `relabelPerm t t'`, and `eqToIso` transports along that
  (spechtIdealRelabelRepIso (relabelPerm t t') t).symm ≪≫
    CategoryTheory.eqToIso (congrArg spechtIdealRep (relabel_relabelPerm t t'))

/-- The dimension of the Young-symmetrizer left ideal depends only on the shape of the tableau. -/
theorem finrank_spechtIdeal_eq :
    Module.finrank ℚ (spechtIdeal t) = Module.finrank ℚ (spechtIdeal t') := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
  exact (finrank_spechtIdeal_relabel σ t).symm

/-- The character of the Young-symmetrizer left ideal depends only on the shape of the tableau. -/
theorem character_spechtIdealRep_eq :
    (spechtIdealRep t).ρ.character = (spechtIdealRep t').ρ.character := by
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t t'
  exact (character_spechtIdealRep_relabel σ t).symm

/-- The character of the bundled Young-symmetrizer representation depends only on the shape of the
tableau. -/
theorem character_spechtIdealFDRep_eq :
    (spechtIdealFDRep t).character = (spechtIdealFDRep t').character :=
  character_spechtIdealRep_eq t t'

end YoungTableau

end TauCeti
