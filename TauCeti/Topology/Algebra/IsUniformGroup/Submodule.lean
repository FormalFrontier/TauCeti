/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The uniform structure on a submodule

A submodule carries the subspace uniformity, and both facts one needs about it hold for the
underlying subobject: `Subgroup.isUniformGroup` gives the additive version for an `AddSubgroup`,
and the countably generated uniformity is inherited by any subtype. Neither is keyed on
`Submodule`, so typeclass search does not find either at `↥p`.

Mathlib works around the first by hand: `Topology/Algebra/Module/FiniteDimension.lean` installs
`s.toAddSubgroup.isUniformAddGroup` locally at two separate proofs, once with `let` and once with
`haveI`.

## Main results

* `Submodule.isUniformAddGroup`: `↥p` is a uniform additive group.
* `Submodule.isCountablyGenerated_uniformity`: `↥p` inherits a countably generated uniformity.

## The consumer: Layer 0.6's own unfinished half

`TauCetiRoadmap/AdicSpaces/README.md` §0.6 asks for "Wedhorn Theorem 6.16 **and Propositions
6.17–6.18**". Theorem 6.16 has landed, as `TauCeti.Huber.IsTateRing.isOpenMap`; Propositions
6.17–6.18 have not, and two module docstrings on `main` already record them as outstanding
(`Huber/ZeroSequenceOfUnits.lean` and `Topology/Algebra/OpenMapping/Basic.lean`, both under
References).

Proposition 6.18(2) is "`u` is continuous and **open onto its image**", and that is a statement
about the corestriction `u.rangeRestrict : M → ↥(LinearMap.range u)`. Its target is a *submodule*,
so applying `IsTateRing.isOpenMap` there needs the four hypotheses that theorem puts on its target:
`CompleteSpace` and `T0Space`, which come free from `IsClosed.completeSpace_coe` and the subspace
topology, and `IsUniformAddGroup` and a countably generated uniformity, which are exactly these two
instances and which nothing else supplies. Without them 6.18(2) cannot be stated in the form 6.16
would discharge.

Layer 4.1 is where 6.18(2) is eventually spent — its text says to "use Layer 0's open mapping
theorem to show that the relevant images are closed" — but the target these instances unblock is
Layer 0's own.
-/

public section

open scoped Uniformity

namespace Submodule

/-- **A submodule of a uniform additive group is a uniform additive group.** This is
`AddSubgroup.isUniformAddGroup` at `p.toAddSubgroup`, which typeclass search does not reach from a
`Submodule`; Mathlib's `Topology/Algebra/Module/FiniteDimension.lean` supplies it by hand twice. -/
instance isUniformAddGroup {A M : Type*} [Ring A] [AddCommGroup M] [UniformSpace M]
    [IsUniformAddGroup M] [Module A M] (p : Submodule A M) : IsUniformAddGroup p :=
  inferInstanceAs (IsUniformAddGroup p.toAddSubgroup)

/-- **A submodule inherits a countably generated uniformity**, since its uniformity is the one
comapped along the inclusion. This is the hypothesis the open mapping theorem states
metrisability as. -/
instance isCountablyGenerated_uniformity {A M : Type*} [Semiring A] [AddCommMonoid M]
    [UniformSpace M] [(𝓤 M).IsCountablyGenerated] [Module A M] (p : Submodule A M) :
    (𝓤 p).IsCountablyGenerated :=
  inferInstanceAs ((𝓤 (p : Set M)).IsCountablyGenerated)

end Submodule
