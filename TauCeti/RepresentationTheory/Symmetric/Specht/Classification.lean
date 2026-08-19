/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.FDRep.Simple
public import TauCeti.RepresentationTheory.Symmetric.Partitions
public import TauCeti.RepresentationTheory.Symmetric.Specht.AbsoluteIrreducibility
public import TauCeti.RepresentationTheory.Symmetric.Specht.Distinctness

/-!
# The classification of the rational representations of the symmetric group

The Specht modules `S^μ`, one for each partition `μ` of `n`, are a complete and irredundant list of
the simple `ℚ[Sₙ]`-modules.  This file assembles that statement out of the three properties proved
separately elsewhere in the library.

*Irreducibility* is James's submodule theorem
(`TauCeti.isIrreducible_spechtModule`), transported into the categorical language by
`FDRep.simple_iff_isIrreducible`.

*Absolute irreducibility* is `TauCeti.spechtModuleIntertwiningEndAlgEquiv`, proved in
`TauCeti/RepresentationTheory/Symmetric/Specht/AbsoluteIrreducibility.lean`: the endomorphism
algebra of `S^μ` is `ℚ` and not some larger division ring.  It is used below through
`FDRep.finrank_hom_eq_finrank_intertwiningMap`, which reads it off as a dimension.  Over a field
that is not algebraically closed this does not follow from irreducibility, and it is what makes
the character of `S^μ` have self-pairing exactly `1`.

*Distinctness* is `TauCeti.spechtModule_iso_iff`, proved by the dominance-order comparison.

Together the three give an orthonormal family of `p(n)` class functions, and `p(n)` is the number of
conjugacy classes of `Sₙ` (`TauCeti.partitionEquivConjClasses`), which is the dimension of the space
of class functions.  So the Specht characters are a basis of the class functions, and a simple
representation orthogonal to all of them would be orthogonal to its own character — impossible,
since that self-pairing is the dimension of its (nonzero) endomorphism space.  This is
*completeness*, and it is proved here without passing to `ℂ`: the usual algebraically closed
hypothesis is replaced by the absolute irreducibility of the Specht modules.

## Main results

* `TauCeti.spechtModule_simple`: **irreducibility**, `S^μ` is a simple object of `FDRep ℚ Sₙ`.
* `TauCeti.spechtModule_iso_iff`: **distinctness** (proved in
  `TauCeti/RepresentationTheory/Symmetric/Specht/Distinctness.lean`).
* `TauCeti.exists_spechtModule_iso`: **completeness**, every simple object of `FDRep ℚ Sₙ` is
  isomorphic to a Specht module.
* `TauCeti.span_range_spechtCharacter`: the Specht characters span the class functions of `Sₙ`
  over `ℚ`, with `TauCeti.linearIndependent_spechtCharacter` for their independence.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapters 3--4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4: completeness and irreducibility (the classification)
-/

public section

namespace TauCeti

open CategoryTheory ClassFunction

variable {n : ℕ}

/-- The order of `Sₙ` is invertible in `ℚ`, as the characteristic is zero. -/
noncomputable local instance invertibleCardPermRat :
    Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℚ)) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- **The Specht modules are irreducible.**  This is the categorical repackaging of James's
submodule theorem. -/
instance spechtModule_simple (μ : n.Partition) : Simple (spechtModule μ) :=
  (FDRep.simple_iff_isIrreducible _).mpr (isIrreducible_spechtModule μ)

/-- The character of the Specht module `S^μ`, as a class function on `Sₙ`. -/
@[expose]
noncomputable def spechtCharacter (μ : n.Partition) : ClassFunction ℚ (Equiv.Perm (Fin n)) :=
  ofFDRep (spechtModule μ)

/-- The defining equation of `TauCeti.spechtCharacter`, so that consumers can rewrite with it
instead of unfolding the definition. -/
@[simp]
theorem spechtCharacter_def (μ : n.Partition) :
    spechtCharacter μ = ofFDRep (spechtModule μ) := rfl

/-- **The Specht characters are orthonormal** for the pairing of class functions: the diagonal
values are `1` by absolute irreducibility, and the off-diagonal ones vanish by distinctness. -/
theorem characterPairing_spechtCharacter (μ ν : n.Partition) :
    characterPairing (spechtCharacter μ) (spechtCharacter ν) = if μ = ν then 1 else 0 := by
  rcases eq_or_ne μ ν with rfl | hne
  · have hone : Module.finrank ℚ (spechtModule μ ⟶ spechtModule μ) = 1 := by
      rw [FDRep.finrank_hom_eq_finrank_intertwiningMap]
      simpa using (spechtModuleIntertwiningEndAlgEquiv μ).toLinearEquiv.finrank_eq
    rw [ite_eq_left rfl, spechtCharacter_def, characterPairing_ofFDRep_eq_finrank, hone,
      Nat.cast_one]
  · rw [ite_eq_right hne]
    refine characterPairing_ofFDRep_eq_zero _ _ (not_nonempty_iff.mp ?_)
    rw [spechtModule_iso_iff]
    exact hne

/-- The Specht characters are linearly independent, being orthonormal. -/
theorem linearIndependent_spechtCharacter (n : ℕ) :
    LinearIndependent ℚ (spechtCharacter (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ν
  have hflip := congrArg (characterPairing.flip (spechtCharacter ν)) hg
  rw [map_sum, map_zero] at hflip
  have h : ∑ i : n.Partition,
      g i * characterPairing (spechtCharacter i) (spechtCharacter ν) = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hflip
    rw [map_smul, smul_eq_mul]
    rfl
  simp only [characterPairing_spechtCharacter] at h
  simpa using h

/-- **The Specht characters are a basis of the class functions of `Sₙ` over `ℚ`**, in the form of
the spanning statement: they are `p(n)` linearly independent class functions, and `p(n)` is the
number of conjugacy classes of `Sₙ`, which is the dimension of the space of class functions. -/
theorem span_range_spechtCharacter (n : ℕ) :
    Submodule.span ℚ (Set.range (spechtCharacter (n := n))) = ⊤ := by
  refine (linearIndependent_spechtCharacter n).span_eq_top_of_card_eq_finrank ?_
  rw [ClassFunction.finrank_eq_card_conjClasses, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (partitionEquivConjClasses n)

/-- **Completeness of the Specht modules**: every simple rational representation of `Sₙ` is
isomorphic to a Specht module.  Were `V` isomorphic to no `S^μ`, its character would be orthogonal
to every Specht character, hence to every class function, hence to itself; but its self-pairing is
the dimension of its endomorphism space, which is nonzero. -/
theorem exists_spechtModule_iso (V : FDRep ℚ (Equiv.Perm (Fin n))) [Simple V] :
    ∃ μ : n.Partition, Nonempty (V ≅ spechtModule μ) := by
  by_contra hcon
  rw [not_exists] at hcon
  have hzero : ∀ μ : n.Partition, characterPairing (spechtCharacter μ) (ofFDRep V) = 0 := by
    intro μ
    refine characterPairing_ofFDRep_eq_zero _ _ (not_nonempty_iff.mp ?_)
    rintro ⟨i⟩
    exact hcon μ ⟨i.symm⟩
  have hker : Submodule.span ℚ (Set.range (spechtCharacter (n := n))) ≤
      LinearMap.ker (characterPairing.flip (ofFDRep V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact hzero μ
  rw [span_range_spechtCharacter] at hker
  have hself : characterPairing (ofFDRep V) (ofFDRep V) = 0 := hker Submodule.mem_top
  rw [characterPairing_ofFDRep_eq_finrank, Nat.cast_eq_zero] at hself
  have : Nontrivial (V ⟶ V) := ⟨⟨𝟙 V, 0, id_nonzero V⟩⟩
  exact absurd hself (Module.finrank_pos (R := ℚ) (M := (V ⟶ V))).ne'

end TauCeti
