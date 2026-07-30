/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic

/-!
# The projectives at a vertex of an acyclic quiver

Over an acyclic quiver the only path `i → i` is the trivial one, so the path count that
`TauCeti.finrank_hom_indecProjRep_indecProjRep` computes collapses to `1` on the endomorphisms of
`Pᵢ`: the projective `Pᵢ` is a brick.

## Main results

* `TauCeti.finrank_end_indecProjRep_of_isAcyclic`: `dim End(Pᵢ) = 1` over an acyclic quiver.

## References

This implements the indecomposable projectives of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- Over an acyclic quiver the endomorphism algebra of `Pᵢ` is one-dimensional, the trivial path at
`i` being the only path `i → i`: the projective `Pᵢ` is a brick. -/
theorem finrank_end_indecProjRep_of_isAcyclic (h : Quiver.IsAcyclic Q) (i : Q) :
    Module.finrank k (indecProjRep k Q i ⟶ indecProjRep k Q i) = 1 := by
  letI : Subsingleton (Quiver.Path i i) := h.subsingleton_path_self i
  letI : Unique (Quiver.Path i i) := uniqueOfSubsingleton Quiver.Path.nil
  rw [finrank_hom_indecProjRep_indecProjRep, Nat.card_unique]

end TauCeti
