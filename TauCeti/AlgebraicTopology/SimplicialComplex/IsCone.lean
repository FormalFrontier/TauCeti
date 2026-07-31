/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Complexes that are cones

A simplicial complex is a *cone with apex `v`* when `v` is one of its vertices and adjoining `v`
to a face gives a face again.  This file carries that condition as the predicate `IsCone K v`,
stated for an apex `v` of the vertex type of `K` itself, so that a complex can be recognised as a
cone without changing its vertex type.

The predicate sits upstream of every construction that satisfies it, so that each construction
records its own recognition lemma in its own file: `isCone_simplex` for an abstract simplex
(`TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic`), `isCone_closedStar` for the closed
star of a face and `isCone_deletion` for the deletion of a face missing the apex
(`TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar`), and `isCone_cone` for the cone
construction (`TauCeti.AlgebraicTopology.SimplicialComplex.Cone`), which is what identifies the
two accounts of a cone.  The point of the predicate is the basic collapsing theorem of
piecewise-linear topology, that a finite cone collapses to its apex
(`TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cone`).

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.IsCone`: a complex is a cone with a given apex.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {v : ι}

/-- `K` is a **cone with apex `v`** when `v` is a vertex of `K` and adjoining `v` to a face of
`K` again gives a face of `K`.

This is the internal form of the cone condition: the apex is a vertex of the ambient type of
`K` itself, so a complex can be recognised as a cone without changing its vertex type.  The
`cone` construction satisfies it at its apex (`isCone_cone`). -/
structure IsCone (K : PreAbstractSimplicialComplex ι) (v : ι) : Prop where
  /-- The apex is a vertex of the complex. -/
  apex_mem : ({v} : Finset ι) ∈ K
  /-- Adjoining the apex to a face gives a face. -/
  insert_mem : ∀ ⦃σ : Finset ι⦄, σ ∈ K → insert v σ ∈ K

/-- A cone with apex `v` is nonempty. -/
theorem IsCone.ne_bot {K : PreAbstractSimplicialComplex ι} (h : IsCone K v) : K ≠ ⊥ := fun hK =>
  (hK ▸ h.apex_mem : ({v} : Finset ι) ∈ (⊥ : PreAbstractSimplicialComplex ι)).elim

end PreAbstractSimplicialComplex

end TauCeti
