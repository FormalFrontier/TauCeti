/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
acts as the identity. The equivalence with modules over the path algebra is planned for separate
development.

## References

This implements the category-of-representations part of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

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

end TauCeti
