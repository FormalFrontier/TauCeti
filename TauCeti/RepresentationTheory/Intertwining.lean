/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Basic

/-!
# Intertwining maps commute with the whole group algebra

An intertwining map of representations of `G` commutes with the action of every group element by
definition. It therefore commutes with the action of every element of the group algebra, since
that action is the linear extension of the action of the group elements: this is
`TauCeti.Representation.IntertwiningMap.map_asAlgebraHom`, the statement that an intertwining map
is a homomorphism of `k[G]`-modules in the form that mentions `Representation.asAlgebraHom` rather
than the module synonym `Representation.asModule`.

## Implementation notes

The declaration lives in `TauCeti.Representation.IntertwiningMap`, not in the root
`Representation.IntertwiningMap` namespace, so dot notation on an intertwining map does not reach
it.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

variable {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module k V] [Module k W] {ρ : _root_.Representation k G V} {σ : _root_.Representation k G W}

namespace IntertwiningMap

/-- **An intertwining map commutes with the action of the group algebra**, not just with the
action of the group elements: both sides are linear in the group-algebra element and agree on the
group elements, where the statement is the intertwining property itself. -/
theorem map_asAlgebraHom (f : ρ.IntertwiningMap σ) (x : k[G]) (v : V) :
    f (ρ.asAlgebraHom x v) = σ.asAlgebraHom x (f v) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using _root_.Representation.IntertwiningMap.isIntertwining ρ σ f g v
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, map_add, hx, hy]
  | smul r x hx => simp only [map_smul, LinearMap.smul_apply, map_smul, hx]

end IntertwiningMap

end Representation

end TauCeti
