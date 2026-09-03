/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Finiteness of the components of an affine group scheme

An affine group scheme of finite type over a Noetherian commutative ring has finitely many
connected components. This is the scheme-side form of the corresponding coordinate-ring fact:
its structural morphism is locally of finite type over the Noetherian scheme `Spec R`, so its
source is locally Noetherian; affineness makes the source compact, hence Noetherian.

## Main declaration

* `TauCeti.FiniteTypeAffineGroupSchemeCat.instFiniteConnectedComponents`: the connected
  components of the underlying scheme form a finite type.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
* The Stacks Project, Tag 01T6, *Properties of schemes, more on morphisms*.

This is the scheme-side finiteness prerequisite for the identity component and component group
in Layer 3 of the ReductiveGroups roadmap. Constructing the finite group scheme `π₀` and proving
it étale under the roadmap's smoothness hypotheses remain later steps.
-/

public section

namespace TauCeti.FiniteTypeAffineGroupSchemeCat

open AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The underlying scheme of a finite-type affine group scheme over a Noetherian commutative ring
has finitely many connected components. -/
instance instFiniteConnectedComponents
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of R)) :
    Finite (ConnectedComponents G.obj.obj.X.left) := by
  let _ : IsLocallyNoetherian G.obj.obj.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.obj.obj.X.hom
  let _ : IsNoetherian G.obj.obj.X.left :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact TauCeti.finite_connectedComponents_of_noetherianSpace

end TauCeti.FiniteTypeAffineGroupSchemeCat
