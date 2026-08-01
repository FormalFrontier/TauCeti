/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.Injective
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Acyclic

/-!
# The vertex representations of an acyclic quiver: indecomposability and distinctness

Three representations are attached to a vertex `i` of a quiver `Q`: the simple `Sᵢ`, the projective
`Pᵢ` and the injective `Iᵢ`. The names `TauCeti.indecProjRep` and `TauCeti.indecInjRep` record the
expectation that the last two are indecomposable, but neither file proves it. This file does, for
an **acyclic** quiver, and it needs no Krull-Schmidt theory to do so: over an acyclic quiver the
trivial path is the only closed path at `i`, so `Pᵢ` and `Iᵢ` are *bricks*, their endomorphism
spaces are one-dimensional, and `TauCeti.indecomposable_of_finrank_end_eq_one` applies.

The same path count makes the list irredundant: `Pᵢ ≅ Pⱼ` forces paths `i → j` and `j → i`, which
over an acyclic quiver forces `i = j`, and dually for the injectives. So over an acyclic quiver the
vertices index the projectives and the injectives without repetition, the property that lets them
label the rows and columns of a Cartan matrix.

Acyclicity is genuinely needed. Over the loop quiver, `Pᵢ` is the regular representation of
`k[X]`, whose endomorphism algebra is `k[X]` itself; the statements below therefore carry
`Quiver.IsAcyclic Q` rather than being unconditional. What is *not* needed is any finiteness
assumption on `Q`, nor an algebraically closed base field.

## Main results

* `TauCeti.finrank_end_indecInjRep_of_isAcyclic`: `dim End(Iᵢ) = 1` over an acyclic quiver, the
  injective counterpart of `TauCeti.finrank_end_indecProjRep_of_isAcyclic`.
* `TauCeti.indecomposable_indecProjRep_of_isAcyclic` and
  `TauCeti.indecomposable_indecInjRep_of_isAcyclic`: `Pᵢ` and `Iᵢ` are indecomposable over an
  acyclic quiver.
* `TauCeti.not_nonempty_indecProjRep_iso_of_isAcyclic` and
  `TauCeti.not_nonempty_indecInjRep_iso_of_isAcyclic`: over an acyclic quiver those
  indecomposables at distinct vertices are not isomorphic, the counterpart for `Pᵢ` and `Iᵢ` of
  `TauCeti.not_nonempty_simpleRep_iso`.

## Implementation notes

`Sᵢ` needs nothing from this file: it is a simple object of the category of representations by the
instance `TauCeti.simpleRep_simple`, so `CategoryTheory.indecomposable_of_simple (simpleRep k Q i)`
already proves it indecomposable, over any quiver. `Pᵢ` and `Iᵢ` are almost never simple — `Pᵢ`
surjects onto `Sᵢ` with a kernel spanned by the nontrivial paths out of `i` — so that route is
unavailable for them, and the brick criterion is what replaces it.

`finrank_end_indecInjRep_of_isAcyclic` is stated here, next to its single consumer, rather than
beside `TauCeti.finrank_hom_indecInjRep_indecInjRep`, which it specializes: the file holding that
lemma is deliberately free of any acyclicity hypothesis, exactly as
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic` is, its acyclic consequences
living in a separate file. The two non-isomorphism results are here for the same reason, while
`TauCeti.not_nonempty_simpleRep_iso` can stay with the simples because it needs no hypothesis on
the quiver at all.

The non-isomorphism results are stated as `¬ Nonempty (… ≅ …)` rather than as an inequality of
objects, matching `TauCeti.not_nonempty_simpleRep_iso`: representations are compared up to
isomorphism, never by equality.

The count of closed paths in an acyclic quiver is `Quiver.IsAcyclic.card_path_self`, stated with
the rest of the acyclic path API. A private helper turns a path count of `1` in each direction
between two vertices into their equality; it is private because it is a `Nat.card` repackaging of
`Quiver.IsAcyclic.eq_of_paths`, which is the public statement of that fact.

## References

This proves the indecomposability asserted by the names of the vertex projectives and injectives in
Layer 1, by the brick route that Layer 4 identifies, of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- Two vertices of an acyclic quiver joined by a path in each direction coincide, in the form the
path counts below produce. -/
private theorem eq_of_card_path_eq_one (h : Quiver.IsAcyclic Q) {i j : Q}
    (hij : Nat.card (Quiver.Path i j) = 1) (hji : Nat.card (Quiver.Path j i) = 1) : i = j := by
  obtain ⟨p, -⟩ := Nat.card_eq_one_iff_exists.mp hij
  obtain ⟨q, -⟩ := Nat.card_eq_one_iff_exists.mp hji
  exact h.eq_of_paths p q

/-- Over an acyclic quiver the endomorphism algebra of `Iᵢ` is one-dimensional, the trivial path at
`i` being the only path `i → i`: the injective `Iᵢ` is a brick. This is the injective counterpart
of `TauCeti.finrank_end_indecProjRep_of_isAcyclic`. -/
theorem finrank_end_indecInjRep_of_isAcyclic (h : Quiver.IsAcyclic Q) (i : Q) :
    Module.finrank k (indecInjRep k Q i ⟶ indecInjRep k Q i) = 1 := by
  rw [finrank_hom_indecInjRep_indecInjRep, h.card_path_self]

/-- **The vertex projective `Pᵢ` of an acyclic quiver is indecomposable.** Its endomorphism space
is spanned by the identity, so it admits no nontrivial idempotent and hence no nontrivial
decomposition. -/
theorem indecomposable_indecProjRep_of_isAcyclic (h : Quiver.IsAcyclic Q) (i : Q) :
    Indecomposable (indecProjRep k Q i) :=
  indecomposable_of_finrank_end_eq_one (finrank_end_indecProjRep_of_isAcyclic h i)

/-- **The vertex injective `Iᵢ` of an acyclic quiver is indecomposable**, by the same brick
argument as for `Pᵢ`. -/
theorem indecomposable_indecInjRep_of_isAcyclic (h : Quiver.IsAcyclic Q) (i : Q) :
    Indecomposable (indecInjRep k Q i) :=
  indecomposable_of_finrank_end_eq_one (finrank_end_indecInjRep_of_isAcyclic h i)

/-- **The vertex projectives of an acyclic quiver at distinct vertices are not isomorphic.** An
isomorphism `Pᵢ ≅ Pⱼ` equates their dimension vectors, so the single closed path at each of `i` and
`j` is matched by a path `j → i` and a path `i → j`; an acyclic quiver admits paths in both
directions only between equal vertices. -/
theorem not_nonempty_indecProjRep_iso_of_isAcyclic (h : Quiver.IsAcyclic Q) {i j : Q}
    (hij : i ≠ j) : ¬ Nonempty (indecProjRep k Q i ≅ indecProjRep k Q j) := by
  rintro ⟨e⟩
  have hd := congrFun (dimVector_eq_of_iso e)
  have hji : Nat.card (Quiver.Path j i) = 1 := by
    have h' := hd i
    rwa [dimVector_indecProjRep, dimVector_indecProjRep, h.card_path_self i, eq_comm] at h'
  have hij' : Nat.card (Quiver.Path i j) = 1 := by
    have h' := hd j
    rwa [dimVector_indecProjRep, dimVector_indecProjRep, h.card_path_self j] at h'
  exact hij (eq_of_card_path_eq_one h hij' hji)

/-- **The vertex injectives of an acyclic quiver at distinct vertices are not isomorphic**, by the
same path count as for the projectives, read in the other variable. -/
theorem not_nonempty_indecInjRep_iso_of_isAcyclic (h : Quiver.IsAcyclic Q) {i j : Q}
    (hij : i ≠ j) : ¬ Nonempty (indecInjRep k Q i ≅ indecInjRep k Q j) := by
  rintro ⟨e⟩
  have hd := congrFun (dimVector_eq_of_iso e)
  have hij' : Nat.card (Quiver.Path i j) = 1 := by
    have h' := hd i
    rwa [dimVector_indecInjRep, dimVector_indecInjRep, h.card_path_self i, eq_comm] at h'
  have hji : Nat.card (Quiver.Path j i) = 1 := by
    have h' := hd j
    rwa [dimVector_indecInjRep, dimVector_indecInjRep, h.card_path_self j] at h'
  exact hij (eq_of_card_path_eq_one h hij' hji)

end TauCeti
