/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement
public import TauCeti.RepresentationTheory.Irreducible

/-!
# The orthogonal decomposition of a unitary representation into irreducibles

A finite-dimensional unitary continuous representation of a group is an **orthogonal internal
direct sum of irreducible subrepresentations**. This is the geometric — as opposed to
lattice-theoretic — form of complete reducibility: not merely that every subrepresentation has a
complement, but that the whole space is cut into finitely many mutually orthogonal irreducible
blocks.

The proof is the classical descent. A nonzero subrepresentation of a finite-dimensional
representation contains an atom of the lattice of subrepresentations
(`TauCeti.Representation.exists_isAtom_le`), and an atom carries an irreducible representation
(`TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom`). Unitarity enters exactly
once, to split off that atom orthogonally: the orthogonal complement of an invariant subspace is
again invariant (`TauCeti.ContRepresentation.IsUnitary.orthogonal_mem_invtSubmodule`), so the
remainder is a strictly smaller subrepresentation and the descent recurses on it.

No measure, no compactness, and no continuity of the representation are used: the argument runs on
a `ContRepresentation` only because that is where `TauCeti.ContRepresentation.IsUnitary` lives, and
the acting group may be arbitrary. For a compact group the unitarity hypothesis is what Weyl's
unitarian trick in `TauCeti.RepresentationTheory.Compact.Unitarizable` is there to supply.

## Main results

* `TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition`: complete
  reducibility in orthogonal internal form, with the dimension count that goes with it.

## Implementation notes

Invariant subspaces are carried as `Subrepresentation π.toRepresentation` rather than as bare
submodules with an invariance side condition: the lattice operations, the atoms, and the
`toRepresentation` needed to say "irreducible" are then all Mathlib's, and the translation to
submodules is `Subrepresentation.toSubmodule_le_toSubmodule` and its relatives.

Orthogonality of the resulting family is stated as Mathlib's `OrthogonalFamily`, which unfolds to
the pairwise vanishing of inner products between distinct blocks and is the form the orthogonal
projection API consumes; `DirectSum.IsInternal` is then read off it through
`OrthogonalFamily.isInternal_iff`.

## References

This is the target `exists_orthogonal_irreducible_decomposition` of Layer 2 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- Splitting the supremum of a family indexed by `Fin (n + 1)` off its first member. -/
private theorem iSup_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 1) → α) :
    ⨆ i, f i = f 0 ⊔ ⨆ i : Fin n, f i.succ := by
  refine le_antisymm (iSup_le fun i ↦ ?_)
    (sup_le (le_iSup f 0) (iSup_le fun j ↦ le_iSup f j.succ))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun j : Fin n ↦ f j.succ) j)

namespace ContRepresentation

namespace IsUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

omit [FiniteDimensional 𝕜 V] in
/-- Inside a nonzero subrepresentation `σ` there is an atom `τ` whose orthogonal complement in
`σ` is a subrepresentation `ω` with `τ ⊔ ω = σ` and strictly smaller dimension. Only `σ` itself
need be finite-dimensional; the ambient space may not be. -/
private theorem exists_isAtom_sup_eq_and_lt (hπ : IsUnitary π)
    {σ : Subrepresentation π.toRepresentation} [FiniteDimensional 𝕜 σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ ω : Subrepresentation π.toRepresentation, IsAtom τ ∧ τ ⊔ ω = σ ∧
      ω.toSubmodule = τ.toSubmoduleᗮ ⊓ σ.toSubmodule ∧ ω.toSubmodule < σ.toSubmodule := by
  obtain ⟨τ, hτσ, hτ⟩ := Representation.exists_isAtom_le hσ
  -- The atom sits inside `σ`, so it inherits finite-dimensionality, hence a projection.
  have : FiniteDimensional 𝕜 τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  have hτbot : τ.toSubmodule ≠ ⊥ := fun hc ↦ hτ.1 (Subrepresentation.toSubmodule_injective
    (hc.trans Subrepresentation.toSubmodule_bot.symm))
  refine ⟨τ, hπ.orthogonalSubrepresentation τ ⊓ σ, hτ,
    hπ.sup_orthogonalSubrepresentation_inf hτσ, ?_, ?_⟩
  · rw [Subrepresentation.toSubmodule_inf, toSubmodule_orthogonalSubrepresentation]
  · have hωsub : (hπ.orthogonalSubrepresentation τ ⊓ σ).toSubmodule
        = τ.toSubmoduleᗮ ⊓ σ.toSubmodule := by
      rw [Subrepresentation.toSubmodule_inf, toSubmodule_orthogonalSubrepresentation]
    refine lt_of_le_of_ne (hωsub ▸ inf_le_right) fun heq ↦ hτbot (le_bot_iff.mp ?_)
    refine Submodule.orthogonal_disjoint τ.toSubmodule le_rfl ?_
    calc τ.toSubmodule ≤ σ.toSubmodule := Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ
      _ = (hπ.orthogonalSubrepresentation τ ⊓ σ).toSubmodule := heq.symm
      _ ≤ τ.toSubmoduleᗮ := hωsub ▸ inf_le_left

omit [FiniteDimensional 𝕜 V] in
/-- An orthogonal family of atoms spanning `ω` extends by an atom `τ` orthogonal to all of it to
an orthogonal family of atoms spanning `τ ⊔ ω`. -/
private theorem exists_atom_family_of_sup_eq {τ : Subrepresentation π.toRepresentation}
    (hτ : IsAtom τ) {n : ℕ} {U : Fin n → Subrepresentation π.toRepresentation}
    (hatom : ∀ i, IsAtom (U i)) {σ ω : Subrepresentation π.toRepresentation}
    (hiSup : ⨆ i, (U i).toSubmodule = ω.toSubmodule)
    (horth : Pairwise fun i j ↦
      ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0)
    (hmix : ∀ j : Fin n, ∀ v ∈ τ.toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0)
    (hsup : τ ⊔ ω = σ) :
    ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      (∀ i, IsAtom (U i)) ∧ ⨆ i, (U i).toSubmodule = σ.toSubmodule ∧
        Pairwise fun i j ↦
          ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0 := by
  refine ⟨n + 1, Fin.cons τ U, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simpa using hτ
    · simpa using hatom j
  · rw [iSup_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hiSup, ← Subrepresentation.toSubmodule_sup, hsup]
  · rw [pairwise_fin_succ_iff]
    refine ⟨fun i v hv w hw ↦ ?_, fun j ↦ ?_, ?_⟩
    · simp only [Fin.cons_succ, Fin.cons_zero] at hv hw
      exact inner_eq_zero_symm.mp (hmix i w hw v hv)
    · simpa using hmix j
    · simpa using horth

/-- The descent behind `exists_orthogonal_irreducible_decomposition`: every subrepresentation of a
finite-dimensional unitary representation is the supremum of a finite, pairwise orthogonal family
of atoms. The extra numeral `m` is a bound on the dimension, giving the induction something to
decrease. -/
private theorem exists_atom_family_aux (hπ : IsUnitary π) :
    ∀ (m : ℕ) (σ : Subrepresentation π.toRepresentation),
      Module.finrank 𝕜 σ.toSubmodule ≤ m →
      ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
        (∀ i, IsAtom (U i)) ∧ ⨆ i, (U i).toSubmodule = σ.toSubmodule ∧
          Pairwise fun i j ↦
            ∀ v ∈ (U i).toSubmodule, ∀ w ∈ (U j).toSubmodule, ⟪v, w⟫_𝕜 = 0 := by
  intro m
  induction m with
  | zero =>
    intro σ hle
    refine ⟨0, Fin.elim0, fun i ↦ i.elim0, ?_, fun i ↦ i.elim0⟩
    rw [iSup_of_empty, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)]
  | succ m ih =>
    intro σ hle
    rcases eq_or_ne σ ⊥ with rfl | hσ
    · exact ⟨0, Fin.elim0, fun i ↦ i.elim0, by rw [iSup_of_empty,
        Subrepresentation.toSubmodule_bot], fun i ↦ i.elim0⟩
    obtain ⟨τ, ω, hτ, hsup, hωsub, hωlt⟩ := exists_isAtom_sup_eq_and_lt hπ hσ
    have hωle : Module.finrank 𝕜 ω.toSubmodule ≤ m := by
      have := Submodule.finrank_lt_finrank_of_lt hωlt
      omega
    obtain ⟨n, U, hatom, hiSup, horth⟩ := ih ω hωle
    -- every block of the recursive decomposition lands in the orthogonal complement of the atom
    have hUorth : ∀ j : Fin n, (U j).toSubmodule ≤ τ.toSubmoduleᗮ := fun j ↦
      le_trans (hiSup ▸ le_iSup (fun i ↦ (U i).toSubmodule) j) (hωsub ▸ inf_le_left)
    exact exists_atom_family_of_sup_eq hτ hatom hiSup horth
      (fun j v hv w hw ↦ (Submodule.mem_orthogonal _ w).mp (hUorth j hw) v hv) hsup

/-- **Complete reducibility, orthogonal internal form.** A finite-dimensional unitary continuous
representation of a group decomposes as an orthogonal internal direct sum of finitely many
irreducible subrepresentations, and its dimension is the sum of theirs.

The four conclusions say, in order: each block is irreducible; distinct blocks are orthogonal;
the blocks decompose the space as an internal direct sum; and the dimensions add up. Unitarity is
essential: a general finite-dimensional representation need not decompose into irreducible
subrepresentations at all, since an invariant subspace need not have an invariant complement.
Unitarity supplies one, and supplies it orthogonally, which is what makes the descent go through
and the resulting family orthogonal. -/
theorem exists_orthogonal_irreducible_decomposition (hπ : IsUnitary π) :
    ∃ (n : ℕ) (U : Fin n → Subrepresentation π.toRepresentation),
      (∀ i, (U i).toRepresentation.IsIrreducible) ∧
      OrthogonalFamily 𝕜 (fun i ↦ (U i).toSubmodule) (fun i ↦ ((U i).toSubmodule).subtypeₗᵢ) ∧
      DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) ∧
      Module.finrank 𝕜 V = ∑ i, Module.finrank 𝕜 (U i).toSubmodule := by
  classical
  obtain ⟨n, U, hatom, hiSup, horth⟩ :=
    hπ.exists_atom_family_aux (Module.finrank 𝕜 V) ⊤
      (le_of_eq (by rw [Subrepresentation.toSubmodule_top, finrank_top]))
  have hfamily :
      OrthogonalFamily 𝕜 (fun i ↦ (U i).toSubmodule) (fun i ↦ ((U i).toSubmodule).subtypeₗᵢ) :=
    fun i j hij v w ↦ horth hij v v.2 w w.2
  have htop : ⨆ i, (U i).toSubmodule = ⊤ := by
    rw [hiSup, Subrepresentation.toSubmodule_top]
  have hinternal : DirectSum.IsInternal (fun i ↦ (U i).toSubmodule) :=
    hfamily.isInternal_iff.mpr (by rw [htop, Submodule.top_orthogonal_eq_bot])
  refine ⟨n, U, fun i ↦ Representation.isIrreducible_toRepresentation_of_isAtom (hatom i),
    hfamily, hinternal, ?_⟩
  exact finrank_eq_sum_finrank_of_isInternal hinternal

end FiniteDimensional

end IsUnitary

end ContRepresentation

end TauCeti
