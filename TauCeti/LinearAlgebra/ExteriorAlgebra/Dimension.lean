/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Freeness and dimension of an exterior algebra

Mathlib records the graded pieces of an exterior algebra in full: `exteriorPower.instFree` says
that `⋀[R]^n M` is free when `M` is, and `exteriorPower.finrank_eq` computes its rank as
`(finrank R M).choose n`. It also builds the basis `Module.Basis.ExteriorAlgebra` of the whole
algebra, indexed by the *finite subsets* of the index set of a basis of `M`. What it does not
record is the consequence: `ExteriorAlgebra R M` is itself a free module, of rank `2 ^ finrank R M`
when `M` is finite free.

This file supplies that. Nothing here is new mathematics — the basis does all the work, and the
rank count is `Fintype.card_finset`, the observation that a finite set with `n` elements has `2 ^ n`
subsets, which is the same `∑ₖ (n choose k) = 2 ^ n` that summing `exteriorPower.finrank_eq` over
the graded pieces would give. The point is to have the statement, because it is what the dimension
count for a Clifford algebra rests on: over a ring in which `2` is invertible,
`CliffordAlgebra.equivExterior` identifies `CliffordAlgebra Q` with `ExteriorAlgebra R M` as a
module, so every rank statement about the Clifford algebra is a rank statement about the exterior
algebra transported along that isomorphism. See
`TauCeti/LinearAlgebra/CliffordAlgebra/Dimension.lean`.

The hypotheses are the weakest the basis needs: a commutative ring `R` and a free `R`-module `M`,
with no invertibility of `2` anywhere, since the exterior algebra has a basis over any commutative
ring.

## Main results

* `TauCeti.ExteriorAlgebra.instFree`: the exterior algebra of a free module is free.
* `TauCeti.ExteriorAlgebra.instFinite`: the exterior algebra of a finite free module is a finite
  module.
* `TauCeti.ExteriorAlgebra.finrank_eq_two_pow`: `finrank R (ExteriorAlgebra R M) = 2 ^ finrank R M`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The associated graded is the exterior algebra (a PBW-type theorem)".
-/

public section

open Module

universe u v w

namespace TauCeti

namespace ExteriorAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The exterior algebra of a free module is free, on the finite subsets of a basis index set. -/
instance instFree [Module.Free R M] : Module.Free R (ExteriorAlgebra R M) := by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis b.ExteriorAlgebra

/-- The exterior algebra of a finite free module is a finite module: its basis is indexed by the
finite subsets of a finite basis index set. -/
instance instFinite [Module.Free R M] [Module.Finite R M] :
    Module.Finite R (ExteriorAlgebra R M) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  exact Module.Finite.of_basis (Module.Free.chooseBasis R M).ExteriorAlgebra

/-- The exterior algebra of a finite free module of rank `n` has rank `2 ^ n`: a basis of it is
indexed by the subsets of a basis index set of `M`. -/
theorem finrank_eq_two_pow [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (ExteriorAlgebra R M) = 2 ^ finrank R M := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  rw [finrank_eq_card_basis (Module.Free.chooseBasis R M).ExteriorAlgebra,
    finrank_eq_card_basis (Module.Free.chooseBasis R M), Fintype.card_finset]

end ExteriorAlgebra

end TauCeti
