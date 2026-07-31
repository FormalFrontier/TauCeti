/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.EulerForm

/-!
# The projectives at a vertex of an acyclic quiver

Over an acyclic quiver the only path `i → i` is the trivial one, so the path counts that
`TauCeti.finrank_hom_indecProjRep_indecProjRep` and `TauCeti.titsForm_dimVector_indecProjRep`
compute collapse to `1` on the endomorphisms of `Pᵢ` and on the Tits norm of its dimension vector:
the projective `Pᵢ` is a brick, and `dim Pᵢ` is a root.

## Main results

* `TauCeti.finrank_end_indecProjRep_of_isAcyclic`: `dim End(Pᵢ) = 1` over an acyclic quiver.
* `TauCeti.titsForm_dimVector_indecProjRep_of_isAcyclic`: `titsForm (dim Pᵢ) = 1` over an acyclic
  quiver, acyclicity supplying the finiteness of the paths out of `i` as well.

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

/-- **Over an acyclic quiver the dimension vector of `Pᵢ` is a root of the Tits form**: its Tits
norm is `1`, the trivial path being the only closed path at `i`. Acyclicity also supplies the
finiteness of the paths out of `i`, by `TauCeti.finite_paths_of_isAcyclic`, so no path-finiteness
hypothesis is needed. -/
theorem titsForm_dimVector_indecProjRep_of_isAcyclic [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
    (h : Quiver.IsAcyclic Q) (i : Q) :
    titsForm Q (fun v ↦ (dimVector (indecProjRep k Q i) v : ℤ)) = 1 := by
  haveI := finite_paths_of_isAcyclic h
  haveI : ∀ a : Q, Finite (Quiver.Path i a) := fun a ↦
    Finite.of_injective (fun p : Quiver.Path i a ↦ (⟨i, a, p⟩ : Σ x y : Q, Quiver.Path x y))
      fun p q hpq ↦ by simpa using hpq
  letI : Subsingleton (Quiver.Path i i) := h.subsingleton_path_self i
  letI : Unique (Quiver.Path i i) := uniqueOfSubsingleton Quiver.Path.nil
  rw [titsForm_dimVector_indecProjRep, Nat.card_unique, Nat.cast_one]

end TauCeti
