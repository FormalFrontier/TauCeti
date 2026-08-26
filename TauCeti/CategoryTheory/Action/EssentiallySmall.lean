/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Actions on an essentially small category are essentially small

An object of `CategoryTheory.Action V G` is an object of `V` together with an action of `G` on it,
so the objects of `Action V G` form a type one universe above `V` even when `V` itself is only
essentially small. This file records that the size does not really grow: if `V` is equivalent to a
small category, then so is `Action V G`.

The proof is a transport, not a construction. Mathlib's
`CategoryTheory.Action.functorCategoryEquivalence` identifies `Action V G` with the functor
category `SingleObj G ⥤ V`, whose source category has a *single* object; replacing `V` by
`CategoryTheory.SmallModel V` along `CategoryTheory.equivSmallModel` therefore leaves a functor
category which is literally small, one functor being no more data than its single value together
with the induced monoid homomorphism on endomorphisms. Smallness then transports back along
`CategoryTheory.essentiallySmall_congr`.

The bound `max v w` is the honest one, `w` being the universe of the morphisms of `V`: the group
contributes its own universe `v`, since a functor out of `SingleObj G` carries a map defined on
the morphisms `G`, and that map is data.

The small model of `V` is asked for in that same universe `w`. That is the case that occurs — a
category essentially small at all is normally so at its own morphism universe, `FGModuleCat.{u} k`
for `k : Type u` being the instance used here — and taking the two universes to be equal is what
keeps the universe of the conclusion determined by `V` alone, so that instance search does not
have to solve `max v ? = max u v` for an unknown universe.

This supplies the smallness hypothesis that
`TauCeti/CategoryTheory/GrothendieckGroup/Split.lean` asks of a category before its split
Grothendieck group is defined, in the case of `FDRep k G`, whose representation-ring
instantiation is `TauCeti/RepresentationTheory/RepresentationRing.lean`.

## Main statements

* `CategoryTheory.Action.essentiallySmall`: actions of a monoid on an essentially small category
  form an essentially small category.
-/

public section

universe u v w

namespace CategoryTheory

namespace Action

/-- **Actions on an essentially small category are essentially small.** The equivalence with the
functor category out of `CategoryTheory.SingleObj G` turns an action into a single object of a
small model of `V` together with a monoid homomorphism from `G` into its endomorphisms, which is
data of size `max v w`. -/
instance essentiallySmall {V : Type u} [Category.{w} V] [EssentiallySmall.{w} V] (G : Type v)
    [Monoid G] : EssentiallySmall.{max v w} (Action V G) :=
  (essentiallySmall_congr ((Action.functorCategoryEquivalence V G).trans
    (Equivalence.congrRight (equivSmallModel V)))).2 inferInstance

end Action

end CategoryTheory
