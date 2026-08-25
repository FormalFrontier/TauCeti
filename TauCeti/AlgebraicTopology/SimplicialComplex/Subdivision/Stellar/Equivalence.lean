/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Basic

/-!
# Stellar equivalence of simplicial complexes

Starring a face at a fresh vertex (`PreAbstractSimplicialComplex.stellarSubdivision`) is one
*stellar move*. Two complexes are **stellar equivalent** when a finite sequence of stellar moves
and inverse stellar moves carries one to the other. This is the combinatorial relation that
layer 11 of the geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`) needs
in order to say that a complex is a combinatorial ball or sphere, namely that it becomes the
standard simplex, respectively the boundary of the standard simplex, *after subdivision*.

The relation is built as `Relation.ReflTransGen` of the symmetrisation of the one-move relation,
so a proof of `StellarEquivalent K L` is literally a finite chain of moves and inverse moves, and
induction along that chain is how every invariance result below is proved.

## What this relation is, and what it is not

Newman's and Alexander's theorem is that stellar equivalence coincides with the existence of a
common subdivision, hence — once realizations are available — with PL homeomorphism. That
theorem is *not* proved here, and nothing below asserts it: the definition is taken as the
combinatorial one, following Lickorish, *Simplicial moves on complexes and manifolds*, Geom.
Topol. Monogr. 2 (1999), 299-320, and Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 2. Naming the relation after the moves that generate it, rather than after
that theorem, keeps the two apart.

A stellar move demands a *fresh* vertex, one spanning no face of the complex yet. That
hypothesis is what makes the move honest, and it also means the relation on a fixed vertex type
`ι` is only the intended one when `ι` has room left over: on a finite `ι` that a complex already
exhausts, no move is available at all. Statements downstream that need moves to exist say so, by
assuming `Infinite ι` or by exhibiting the vertices they use.

## Main definitions

* `PreAbstractSimplicialComplex.IsStellarMove`: one starring of a face at a fresh vertex.
* `PreAbstractSimplicialComplex.IsStellarMoveOrInverse`: such a move in either direction.
* `PreAbstractSimplicialComplex.StellarEquivalent`: a finite chain of such moves.

## Main results

* `PreAbstractSimplicialComplex.equivalence_stellarEquivalent`: stellar equivalence is an
  equivalence relation.
* `PreAbstractSimplicialComplex.StellarEquivalent.dimension_eq`: stellar equivalent complexes
  have the same dimension.
* `PreAbstractSimplicialComplex.StellarEquivalent.finite_faces_iff`: stellar equivalence
  preserves and reflects finiteness of the face collection.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L M : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v : ι}

/-- `L` is obtained from `K` by one **stellar move**: `L` is the starring of `K` at a face `σ`
using a vertex `v` that `K` does not already use. -/
def IsStellarMove (K L : PreAbstractSimplicialComplex ι) : Prop :=
  ∃ σ : Finset ι, ∃ v : ι, σ ∈ K ∧ ({v} : Finset ι) ∉ K ∧ L = stellarSubdivision K σ v

/-- Starring a face at a fresh vertex is a stellar move. -/
theorem isStellarMove_stellarSubdivision (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    IsStellarMove K (stellarSubdivision K σ v) :=
  ⟨σ, v, hσ, hv, rfl⟩

/-- A stellar move preserves the dimension: this is `dimension_stellarSubdivision` read along the
move. -/
theorem IsStellarMove.dimension_eq (h : IsStellarMove K L) : dimension L = dimension K := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := h
  exact dimension_stellarSubdivision hv (K.isRelLowerSet_faces hσ).1

/-- A stellar move out of a complex with finitely many faces lands in a complex with finitely
many faces. -/
theorem IsStellarMove.finite_faces (h : IsStellarMove K L) (hK : K.faces.Finite) :
    L.faces.Finite := by
  obtain ⟨σ, v, -, -, rfl⟩ := h
  exact finite_faces_stellarSubdivision hK

/-- The face of the starring `stellarSubdivision K σ v` that records a face `τ` of `K`: a face
containing the starred face `σ` is recorded as the new vertex adjoined to its complement, and any
other face survives unchanged. This is the injection behind
`PreAbstractSimplicialComplex.IsStellarMove.finite_faces_of_finite`. -/
private def starRecord (σ : Finset ι) (v : ι) (τ : Finset ι) : Finset ι :=
  if σ ⊆ τ then insert v (τ \ σ) else τ

private theorem starRecord_of_subset (h : σ ⊆ τ) :
    starRecord σ v τ = insert v (τ \ σ) := by
  simp [starRecord, h]

private theorem starRecord_of_not_subset (h : ¬ σ ⊆ τ) : starRecord σ v τ = τ := by
  simp [starRecord, h]

private theorem starRecord_mem (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) (hτ : τ ∈ K) :
    starRecord σ v τ ∈ stellarSubdivision K σ v := by
  have hvτ : v ∉ τ := notMem_of_singleton_notMem hv hτ
  by_cases hsub : σ ⊆ τ
  · have hvsdiff : v ∉ τ \ σ := fun h => hvτ (Finset.mem_sdiff.mp h).1
    rw [starRecord_of_subset hsub]
    refine (insert_mem_stellarSubdivision_iff hvsdiff).mpr ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (K.isRelLowerSet_faces hσ).1
      exact fun h => (Finset.mem_sdiff.mp (h hx)).2 hx
    · rwa [Finset.sdiff_union_of_subset hsub]
  · rw [starRecord_of_not_subset hsub]
    exact (mem_stellarSubdivision_iff_of_notMem hvτ).mpr ⟨hτ, hsub⟩

private theorem starRecord_injOn (hv : ({v} : Finset ι) ∉ K) :
    Set.InjOn (starRecord σ v) K.faces := by
  intro τ₁ h₁ τ₂ h₂ heq
  have hv₁ : v ∉ τ₁ := notMem_of_singleton_notMem hv h₁
  have hv₂ : v ∉ τ₂ := notMem_of_singleton_notMem hv h₂
  by_cases hs₁ : σ ⊆ τ₁ <;> by_cases hs₂ : σ ⊆ τ₂
  · have hd₁ : v ∉ τ₁ \ σ := fun h => hv₁ (Finset.mem_sdiff.mp h).1
    have hd₂ : v ∉ τ₂ \ σ := fun h => hv₂ (Finset.mem_sdiff.mp h).1
    rw [starRecord_of_subset hs₁, starRecord_of_subset hs₂] at heq
    have hsdiff : τ₁ \ σ = τ₂ \ σ := by
      have := congrArg (fun s => Finset.erase s v) heq
      rwa [Finset.erase_insert hd₁, Finset.erase_insert hd₂] at this
    rw [← Finset.sdiff_union_of_subset hs₁, ← Finset.sdiff_union_of_subset hs₂, hsdiff]
  · rw [starRecord_of_subset hs₁, starRecord_of_not_subset hs₂] at heq
    exact absurd (heq ▸ Finset.mem_insert_self v (τ₁ \ σ)) hv₂
  · rw [starRecord_of_not_subset hs₁, starRecord_of_subset hs₂] at heq
    exact absurd (heq ▸ Finset.mem_insert_self v (τ₂ \ σ)) hv₁
  · rwa [starRecord_of_not_subset hs₁, starRecord_of_not_subset hs₂] at heq

/-- A stellar move into a complex with finitely many faces starts at a complex with finitely many
faces. Faces of the source containing the starred face are recorded in the target as the new
vertex adjoined to their complement, and all other faces survive, so the source injects into the
target. -/
theorem IsStellarMove.finite_faces_of_finite (h : IsStellarMove K L) (hL : L.faces.Finite) :
    K.faces.Finite := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := h
  refine Set.Finite.of_finite_image (hL.subset ?_) (starRecord_injOn (σ := σ) hv)
  rintro ω ⟨ρ, hρ, rfl⟩
  exact starRecord_mem hσ hv hρ

/-- One stellar move, in either direction. Stellar equivalence is generated by this relation. -/
def IsStellarMoveOrInverse (K L : PreAbstractSimplicialComplex ι) : Prop :=
  IsStellarMove K L ∨ IsStellarMove L K

instance : Std.Symm (IsStellarMoveOrInverse (ι := ι)) where
  symm _ _ h := Or.symm h

/-- **Stellar equivalence**: `K` and `L` are joined by a finite sequence of stellar moves and
inverse stellar moves. -/
def StellarEquivalent (K L : PreAbstractSimplicialComplex ι) : Prop :=
  Relation.ReflTransGen IsStellarMoveOrInverse K L

namespace StellarEquivalent

@[refl]
theorem refl (K : PreAbstractSimplicialComplex ι) : StellarEquivalent K K :=
  Relation.ReflTransGen.refl

theorem trans (h : StellarEquivalent K L) (h' : StellarEquivalent L M) : StellarEquivalent K M :=
  Relation.ReflTransGen.trans h h'

theorem symm (h : StellarEquivalent K L) : StellarEquivalent L K :=
  Std.Symm.symm (r := Relation.ReflTransGen IsStellarMoveOrInverse) K L h

end StellarEquivalent

/-- A single stellar move is a stellar equivalence. -/
theorem IsStellarMove.stellarEquivalent (h : IsStellarMove K L) : StellarEquivalent K L :=
  Relation.ReflTransGen.single (Or.inl h)

/-- A complex is stellar equivalent to any of its starrings at a fresh vertex. -/
theorem stellarEquivalent_stellarSubdivision (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K) :
    StellarEquivalent K (stellarSubdivision K σ v) :=
  (isStellarMove_stellarSubdivision hσ hv).stellarEquivalent

/-- Stellar equivalence is an equivalence relation. -/
theorem equivalence_stellarEquivalent : Equivalence (StellarEquivalent (ι := ι)) :=
  ⟨StellarEquivalent.refl, StellarEquivalent.symm, StellarEquivalent.trans⟩

namespace StellarEquivalent

/-- Stellar equivalent complexes have the same dimension. -/
theorem dimension_eq (h : StellarEquivalent K L) : dimension L = dimension K := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rcases hstep with hstep | hstep
    · exact hstep.dimension_eq.trans ih
    · exact hstep.dimension_eq.symm.trans ih

/-- Stellar equivalence preserves and reflects finiteness of the face collection. -/
theorem finite_faces_iff (h : StellarEquivalent K L) : K.faces.Finite ↔ L.faces.Finite := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rcases hstep with hstep | hstep
    · exact ih.trans ⟨hstep.finite_faces, hstep.finite_faces_of_finite⟩
    · exact ih.trans ⟨hstep.finite_faces_of_finite, hstep.finite_faces⟩

/-- A complex stellar equivalent to a complex with a face has a face itself. -/
theorem ne_bot (h : StellarEquivalent K L) (hL : L ≠ ⊥) : K ≠ ⊥ := by
  rintro rfl
  exact hL (dimension_eq_bot_iff.mp (h.dimension_eq.trans dimension_bot))

end StellarEquivalent

end PreAbstractSimplicialComplex
