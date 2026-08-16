/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# Connected components of finite-type affine groups

The prime spectrum of the coordinate ring of a finite-type affine group over a Noetherian
commutative ring has finitely many connected components, and each component is clopen. The Hopf
structure is not needed for this finiteness statement: finite type over a Noetherian ring makes
the coordinate ring Noetherian, and a Noetherian topological space has finitely many connected
components.

## Main declaration

* `TauCeti.FiniteTypeCommHopfAlgCat.instFiniteConnectedComponents`: the connected components of
  the spectrum of a finite-type commutative Hopf algebra form a finite type.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
* The Stacks Project, Tag 0052, *Noetherian topological spaces*.

This is the finiteness prerequisite for Layer 3 of the ReductiveGroups roadmap. The later
component-group construction will put a finite group-scheme structure on these components; this
file establishes the underlying finiteness and clopen decomposition.
-/

public section

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The spectrum of the coordinate ring of a finite-type affine group over a Noetherian
commutative ring has finitely many connected components. -/
instance instFiniteConnectedComponents (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    Finite (ConnectedComponents (PrimeSpectrum H)) :=
  TauCeti.finite_connectedComponents_of_noetherianSpace

end TauCeti.FiniteTypeCommHopfAlgCat
