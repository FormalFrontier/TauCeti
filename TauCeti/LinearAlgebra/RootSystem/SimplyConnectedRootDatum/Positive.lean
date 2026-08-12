/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2

/-!
# Positive roots in the pinned root data

This file computes the number of positive roots in the pinned simply connected root data of types
`Aₙ` and `G₂`. These are the positive-root-count clauses of the two worked examples in the
root-systems roadmap: type `Aₙ` has `(n + 1).choose 2` positive roots and type `G₂` has six.

Both results are consequences of the general fact that root negation exchanges the positive and
negative roots. The pinned data make the total number of roots explicit, so the count is obtained by
halving `n * (n + 1)` or `12`; no classification theorem is used.

## Main results

* `TauCeti.DynkinType.ncard_posRoots_typeASimplyConnectedRootDatum` computes the positive roots of
  the pinned type `Aₙ` datum.
* `TauCeti.DynkinType.ncard_posRoots_g2SimplyConnectedRootDatum` computes the positive roots of the
  pinned type `G₂` datum.

## References

This implements the positive-root-count acceptance criteria in the `Aₙ` and `G₂` worked examples
of Layer 6 in `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The counts agree with
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I and IX.
-/

public section

namespace TauCeti

namespace DynkinType

/-- **The pinned root datum of type `Aₙ` has `(n + 1).choose 2` positive roots.** -/
theorem ncard_posRoots_typeASimplyConnectedRootDatum (n : ℕ) :
    (posRoots (typeASimplyConnectedRootDatum n) (typeASimplyConnectedBase n)).ncard =
      (n + 1).choose 2 := by
  rw [ncard_posRoots_eq_natCard_div_two]
  simp [Nat.choose_two_right, Nat.mul_comm]

/-- **The pinned root datum of type `G₂` has six positive roots.** -/
theorem ncard_posRoots_g2SimplyConnectedRootDatum :
    (posRoots g2SimplyConnectedRootDatum g2SimplyConnectedBase).ncard = 6 := by
  rw [ncard_posRoots_eq_natCard_div_two]
  norm_num

end DynkinType

end TauCeti
