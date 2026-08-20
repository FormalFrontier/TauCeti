/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Representations of a quiver

A representation of a quiver over a field assigns a vector space to every vertex and a linear map
to every arrow, compatibly with path composition. This is precisely a functor from Mathlib's free
path category to its category of modules.

This file introduces the standard abbreviation, and the one structural fact that the trivial path
acts as the identity. It also names the vertex spaces of a representation as a family
`TauCeti.QuiverRep.vertexSpace` indexed by the vertices, with `TauCeti.QuiverRep.mapₗ` the
structure maps between them; that is what a construction indexed by the vertices — a direct sum, a
product — needs, since instance search does not see the objects of `CategoryTheory.Paths Q` as
vertices when it is asked for a *family* of instances over `Q` (see the implementation notes). The
equivalence with modules over the path algebra is `TauCeti.quiverRepEquivalence`, built in
`TauCeti.RepresentationTheory.Quiver.Representation.AsModule`.

## Implementation notes

A representation is a functor out of `CategoryTheory.Paths Q`, whose objects are vertices only
after unfolding the semireducible `CategoryTheory.Paths`. Instance search does not see through
that when it is asked for the *family* `∀ v : Q, AddCommMonoid (M.obj v)`, although it succeeds at
each individual vertex; naming the family as `TauCeti.QuiverRep.vertexSpace` and giving it its two
instances by `inferInstanceAs` is what makes such a family usable.

## References

This implements the category-of-representations part of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

/-- The category of representations of a quiver `Q` over a field `k`. -/
abbrev QuiverRep (k : Type u) (Q : Type v) [Field k] [Quiver Q] :=
  Paths Q ⥤ ModuleCat k

/-- **The trivial path acts as the identity.** In the free path category `Quiver.Path.nil` is the
identity morphism, so a representation carries it to the identity map. Stated separately because
`Quiver.Path.nil` is what appears when a path is taken apart, while `CategoryTheory.Functor.map_id`
is phrased in terms of `𝟙`: the two agree only by unfolding the semireducible
`CategoryTheory.Paths`, so `simp only [Functor.map_id]` makes no progress on a goal about
`Quiver.Path.nil`, and `simp` cannot compute the action of the trivial path without this lemma.
Mathlib states the same restatement for
functors of the form `CategoryTheory.Paths.lift φ`, as `CategoryTheory.Paths.lift_nil`; that lemma
does not apply to a general representation. -/
@[simp]
theorem QuiverRep.map_nil {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] (M : QuiverRep k Q)
    (a : Q) : M.map (Quiver.Path.nil : Quiver.Path a a) = 𝟙 (M.obj a) :=
  M.map_id a

-- Not `@[simp]`: `simp` already rewrites through `QuiverRep.map_nil` and `ModuleCat.hom_id`, so
-- tagging this is a simp-normal-form violation (`simpNF`). It is stated because a *term* naming
-- the action of the trivial path on a vector is what proofs about `CategoryTheory.Paths` need:
-- an element of `M.obj a` there usually carries the type `M.obj ((Paths.of Q).obj a)`, which is
-- not type-correct at the transparency `rw` and `simp` use to build a motive, so they cannot
-- rewrite it in place.
/-- The element-level form of `TauCeti.QuiverRep.map_nil`: the trivial path fixes every vector. -/
theorem QuiverRep.map_nil_apply {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
    (M : QuiverRep k Q) (a : Q) (x : M.obj a) :
    M.map (Quiver.Path.nil : Quiver.Path a a) x = x := by
  rw [QuiverRep.map_nil]
  rfl

namespace QuiverRep

section Vertex

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- The vertex space, as a bare type indexed by the vertices. -/
@[expose]
def vertexSpace (v : Q) : Type t := M.obj v

instance instAddCommGroupVertexSpace (v : Q) : AddCommGroup (vertexSpace k Q M v) :=
  inferInstanceAs (AddCommGroup (M.obj v))

instance instModuleVertexSpace (v : Q) : Module k (vertexSpace k Q M v) :=
  inferInstanceAs (Module k (M.obj v))

/-- The structure map of a representation along a path, retyped between vertex spaces.

`@[expose]` is load-bearing rather than a leak: a goal about a vertex-indexed construction that has
been unfolded to the underlying `ModuleCat` morphisms — as the naturality square of
`TauCeti.QuiverRep.asModuleIso` is — only matches this once the body is visible. -/
@[expose]
noncomputable def mapₗ {a b : Q} (p : Quiver.Path a b) :
    vertexSpace k Q M a →ₗ[k] vertexSpace k Q M b := (M.map p).hom

-- Not `@[simp]`: `TauCeti.QuiverRep.mapₗ` is the simp-normal form of a structure map, since it is
-- the retyping that lets a vertex-indexed construction see the vertex spaces; rewriting with this
-- would undo that everywhere.
/-- The retyped structure map is the structure map. -/
theorem mapₗ_apply {a b : Q} (p : Quiver.Path a b) (z : vertexSpace k Q M a) :
    mapₗ k Q M p z = (M.map p) z := (rfl)

/-- **The trivial path acts as the identity**, the element-level
`TauCeti.QuiverRep.map_nil_apply` read as an equation of linear maps. -/
@[simp]
theorem mapₗ_nil (a : Q) : mapₗ k Q M (Quiver.Path.nil : Quiver.Path a a) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  rw [mapₗ_apply, LinearMap.id_apply]
  exact QuiverRep.map_nil_apply M a z

/-- **Concatenation of paths composes the structure maps**, the functoriality of a representation
read on the retyped maps. -/
theorem mapₗ_comp {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    mapₗ k Q M (p.comp q) = (mapₗ k Q M q).comp (mapₗ k Q M p) := by
  refine LinearMap.ext fun z => ?_
  have h : M.map (p.comp q) = M.map p ≫ M.map q := M.map_comp p q
  rw [mapₗ_apply, h, LinearMap.comp_apply, mapₗ_apply, mapₗ_apply]
  -- `rw` cannot use this: its motive retypes the vertex `a` as an object of
  -- `CategoryTheory.Paths Q`, which `M.obj` does not accept, so the rewrite is applied by hand
  exact ModuleCat.comp_apply (M.map p) (M.map q) z

end Vertex

end QuiverRep

end TauCeti
