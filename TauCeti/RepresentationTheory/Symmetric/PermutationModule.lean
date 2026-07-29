/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup

/-!
# Young permutation modules

For a partition `μ` of `n`, the Young permutation module `M^μ` is the rational permutation
representation of `Equiv.Perm (Fin n)` on the left cosets of the Young subgroup associated to
`μ`. These cosets are the `μ`-tabloids.

This file records the tabloid basis and its action, identifies `M^μ` with the representation
induced from the trivial representation of the Young subgroup, and computes its dimension and
character. In particular, the dimension is the multinomial coefficient
`n! / ∏ i, μᵢ!`, while the character at a permutation is the number of fixed tabloids.

## Main definitions

* `TauCeti.permutationModule` is the Young permutation module `M^μ`.
* `TauCeti.permutationModuleBasis` is its basis indexed by `μ`-tabloids.
* `TauCeti.permutationModuleIsoIndTrivial` identifies `M^μ` with an induced trivial
  representation.
* `TauCeti.permutationModuleFDRep` is the finite-dimensional bundled form of `M^μ`.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, for Young permutation
  modules and tabloids.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1, “The permutation module”.
-/

public section

open CategoryTheory

namespace TauCeti

/-! ## The tabloid model -/

/-- The Young permutation module `M^μ` over `ℚ`.

Its standard basis is indexed by the left cosets of `youngSubgroup μ`; these cosets are the
`μ`-tabloids, and the symmetric group acts on them by left multiplication. -/
noncomputable abbrev permutationModule {n : ℕ} (μ : n.Partition) :
    Rep ℚ (Equiv.Perm (Fin n)) :=
  Rep.ofMulAction ℚ (Equiv.Perm (Fin n))
    (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)

/-- The standard basis of `M^μ`, indexed by the `μ`-tabloids. -/
noncomputable abbrev permutationModuleBasis {n : ℕ} (μ : n.Partition) :
    Module.Basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ
      (permutationModule μ).V :=
  MonoidAlgebra.basis (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) ℚ

/-- The symmetric-group action permutes the tabloid basis by left multiplication. -/
@[simp]
theorem permutationModule_ρ_basis {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n))
    (q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) :
    (permutationModule μ).ρ σ (permutationModuleBasis μ q) =
      permutationModuleBasis μ (σ • q) := by
  rw [MonoidAlgebra.basis_apply, MonoidAlgebra.basis_apply]
  exact Representation.ofMulAction_single σ q 1

/-! ## Induction, dimension, and character -/

/-- The Young permutation module is induction of the trivial representation of the Young
subgroup. -/
noncomputable def permutationModuleIsoIndTrivial {n : ℕ} (μ : n.Partition) :
    permutationModule μ ≅
      Rep.ind (youngSubgroup μ).subtype
        (Rep.trivial ℚ (youngSubgroup μ) ℚ) :=
  (indTrivialIso ℚ (youngSubgroup μ)).symm

/-- The dimension of `M^μ` is the index of its Young subgroup. -/
theorem finrank_permutationModule_eq_index {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModule μ).V = (youngSubgroup μ).index := by
  letI : Fintype (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (permutationModuleBasis μ)]
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]

/-- The dimension of `M^μ` is the multinomial coefficient
`n! / ∏ i, μᵢ!`. -/
@[simp]
theorem finrank_permutationModule {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModule μ).V =
      n.factorial / (μ.parts.map Nat.factorial).prod := by
  rw [finrank_permutationModule_eq_index, youngSubgroup_index]

/-- The character of `M^μ` at `σ` is the number of `μ`-tabloids fixed by `σ`. -/
@[simp]
theorem char_permutationModule {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModule μ).ρ.character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : ℚ) := by
  letI : Finite (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := inferInstance
  exact char_ofMulAction ℚ _ σ

/-- The Young permutation module bundled as a finite-dimensional representation. -/
noncomputable abbrev permutationModuleFDRep {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of (permutationModule μ).ρ

/-- The bundled Young permutation module has the same multinomial dimension. -/
@[simp]
theorem finrank_permutationModuleFDRep {n : ℕ} (μ : n.Partition) :
    Module.finrank ℚ (permutationModuleFDRep μ) =
      n.factorial / (μ.parts.map Nat.factorial).prod :=
  finrank_permutationModule μ

/-- The character of the bundled Young permutation module counts fixed tabloids. -/
@[simp]
theorem char_permutationModuleFDRep {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModuleFDRep μ).character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : ℚ) :=
  char_permutationModule μ σ

end TauCeti
