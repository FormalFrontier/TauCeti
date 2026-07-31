/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic

/-!
# The two extreme Young permutation modules

The Young permutation module `M^μ` of a partition `μ` of `n` interpolates between two extremes.
For the one-part partition `(n)` there is a single `μ`-tabloid and `M^{(n)}` is the trivial
representation; for the all-ones partition `(1ⁿ)` the tabloids are the permutations themselves
and `M^{(1ⁿ)}` is the regular representation `ℚ[Sₙ]`.

The proofs go through the Young subgroups: `youngSubgroup (n) = ⊤` and `youngSubgroup (1ⁿ) = ⊥`,
so the two modules are the permutation representations of `Sₙ` on the cosets of the whole group
and of the trivial subgroup respectively.

## Main definitions

* `TauCeti.permutationModuleIndiscreteIsoTrivial`: `M^{(n)} ≅ ℚ` with the trivial action.
* `TauCeti.permutationModuleOnesIsoLeftRegular`: `M^{(1ⁿ)} ≅ ℚ[Sₙ]` with the left regular action.

Both isomorphisms come with the lemmas reading them, and their inverses, on the tabloid basis.

## Main statements

* `TauCeti.finrank_permutationModule_indiscrete` and
  `TauCeti.finrank_permutationModule_ones`: the two dimensions, `1` and `n !`.
* `TauCeti.char_permutationModule_indiscrete` and `TauCeti.char_permutationModule_ones`: the two
  characters, the constant `1` and the regular character supported at the identity.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, §4.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1, “the base cases `M^{(n)} = S^{(n)}` (trivial) and `M^{(1ⁿ)} = ℚ[Sₙ]` (regular)”.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ## The one-part partition `(n)` -/

/-- The Young permutation module of the one-part partition `(n)` is the trivial representation:
there is only one `(n)`-tabloid. -/
noncomputable def permutationModuleIndiscreteIsoTrivial (n : ℕ) :
    permutationModule (Nat.Partition.indiscrete n) ≅
      Rep.trivial ℚ (Equiv.Perm (Fin n)) ℚ :=
  quotientIsoCongr ℚ (youngSubgroup_indiscrete n) ≪≫ quotientTopIsoTrivial ℚ

/-- Every `(n)`-tabloid is sent to `1`. -/
@[simp]
theorem permutationModuleIndiscreteIsoTrivial_hom_hom_single (n : ℕ)
    (t : Equiv.Perm (Fin n) ⧸ youngSubgroup (Nat.Partition.indiscrete n)) (r : ℚ) :
    (permutationModuleIndiscreteIsoTrivial n).hom.hom (MonoidAlgebra.single t r) = r := by
  simp only [permutationModuleIndiscreteIsoTrivial, Iso.trans_hom, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [quotientIsoCongr_hom_hom_single, quotientTopIsoTrivial_hom_hom_single]

/-- The inverse sends `r` to `r` times the unique `(n)`-tabloid. -/
@[simp]
theorem permutationModuleIndiscreteIsoTrivial_inv_hom_apply (n : ℕ) (r : ℚ) :
    (permutationModuleIndiscreteIsoTrivial n).inv.hom r =
      MonoidAlgebra.single
        ((1 : Equiv.Perm (Fin n)) :
          Equiv.Perm (Fin n) ⧸ youngSubgroup (Nat.Partition.indiscrete n)) r := by
  simp only [permutationModuleIndiscreteIsoTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [quotientTopIsoTrivial_inv_hom_apply, quotientIsoCongr_inv_hom_single_mk]

/-- The Young permutation module of the one-part partition `(n)` is one-dimensional. -/
@[simp]
theorem finrank_permutationModule_indiscrete (n : ℕ) :
    Module.finrank ℚ (permutationModule (Nat.Partition.indiscrete n)).V = 1 := by
  rw [finrank_permutationModule, Nat.Partition.prod_map_factorial_indiscrete,
    Nat.div_self n.factorial_pos]

/-- The character of the Young permutation module of `(n)` is constantly `1`.

Not a `simp` lemma: `char_ofMulAction` already rewrites the left-hand side to the fixed-tabloid
count. -/
theorem char_permutationModule_indiscrete (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationModule (Nat.Partition.indiscrete n)).ρ.character σ = 1 := by
  rw [char_permutationModule, youngSubgroup_indiscrete]
  haveI := QuotientGroup.subsingleton_quotient_top (G := Equiv.Perm (Fin n))
  haveI : Unique {q : Equiv.Perm (Fin n) ⧸ (⊤ : Subgroup (Equiv.Perm (Fin n))) // σ • q = q} :=
    ⟨⟨⟨1, Subsingleton.elim _ _⟩⟩, fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  rw [Nat.card_unique, Nat.cast_one]

/-! ## The all-ones partition `(1ⁿ)` -/

/-- The Young permutation module of the all-ones partition `(1ⁿ)` is the regular representation
`ℚ[Sₙ]`: the `(1ⁿ)`-tabloids are the permutations themselves. -/
noncomputable def permutationModuleOnesIsoLeftRegular (n : ℕ) :
    permutationModule (Nat.Partition.ones n) ≅ Rep.leftRegular ℚ (Equiv.Perm (Fin n)) :=
  quotientIsoCongr ℚ (youngSubgroup_ones n) ≪≫ quotientBotIsoLeftRegular ℚ

/-- A `(1ⁿ)`-tabloid is sent to the permutation it names. -/
@[simp]
theorem permutationModuleOnesIsoLeftRegular_hom_hom_single (n : ℕ)
    (t : Equiv.Perm (Fin n) ⧸ youngSubgroup (Nat.Partition.ones n)) (r : ℚ) :
    (permutationModuleOnesIsoLeftRegular n).hom.hom (MonoidAlgebra.single t r) =
      MonoidAlgebra.single
        (QuotientGroup.quotientBot (Subgroup.quotientEquivOfEq (youngSubgroup_ones n) t)) r := by
  simp only [permutationModuleOnesIsoLeftRegular, Iso.trans_hom, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [quotientIsoCongr_hom_hom_single, quotientBotIsoLeftRegular_hom_hom_single]

/-- The `(1ⁿ)`-tabloid of a permutation is sent to that permutation. -/
@[simp]
theorem permutationModuleOnesIsoLeftRegular_hom_hom_single_mk (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (r : ℚ) :
    (permutationModuleOnesIsoLeftRegular n).hom.hom
        (MonoidAlgebra.single
          (σ : Equiv.Perm (Fin n) ⧸ youngSubgroup (Nat.Partition.ones n)) r) =
      MonoidAlgebra.single σ r :=
  permutationModuleOnesIsoLeftRegular_hom_hom_single n _ r

/-- The inverse sends a permutation back to its `(1ⁿ)`-tabloid. -/
@[simp]
theorem permutationModuleOnesIsoLeftRegular_inv_hom_single (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (r : ℚ) :
    (permutationModuleOnesIsoLeftRegular n).inv.hom (MonoidAlgebra.single σ r) =
      MonoidAlgebra.single
        (σ : Equiv.Perm (Fin n) ⧸ youngSubgroup (Nat.Partition.ones n)) r := by
  simp only [permutationModuleOnesIsoLeftRegular, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [quotientBotIsoLeftRegular_inv_hom_single, quotientIsoCongr_inv_hom_single_mk]

/-- The Young permutation module of the all-ones partition `(1ⁿ)` has dimension `n !`. -/
@[simp]
theorem finrank_permutationModule_ones (n : ℕ) :
    Module.finrank ℚ (permutationModule (Nat.Partition.ones n)).V = n.factorial := by
  rw [finrank_permutationModule, Nat.Partition.prod_map_factorial_ones, Nat.div_one]

/-- The character of the Young permutation module of `(1ⁿ)` is the regular character: it is `n !`
at the identity and vanishes elsewhere.

Not a `simp` lemma: `char_ofMulAction` already rewrites the left-hand side to the fixed-tabloid
count. -/
theorem char_permutationModule_ones (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationModule (Nat.Partition.ones n)).ρ.character σ =
      if σ = 1 then (n.factorial : ℚ) else 0 := by
  rw [char_permutationModule, youngSubgroup_ones]
  rcases eq_or_ne σ 1 with rfl | hσ
  · have hcard :
        Nat.card {q : Equiv.Perm (Fin n) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin n))) //
            (1 : Equiv.Perm (Fin n)) • q = q} = n.factorial := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun q => one_smul _ q),
        ← Subgroup.index_eq_card, Subgroup.index_bot, Nat.card_perm, Nat.card_fin]
    rw [hcard, if_pos rfl]
  · haveI : IsEmpty {q : Equiv.Perm (Fin n) ⧸ (⊥ : Subgroup (Equiv.Perm (Fin n))) //
        σ • q = q} :=
      ⟨fun q => hσ ((quotientBot_smul_eq_self_iff σ q.1).mp q.2)⟩
    rw [Nat.card_of_isEmpty, if_neg hσ, Nat.cast_zero]

end TauCeti
