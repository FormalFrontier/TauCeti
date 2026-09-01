/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Powers of the ideal defining an adic topology

For an ideal `I` of a commutative ring `R`, Mathlib's `Ideal.openAddSubgroup` records that each
power `I ^ n` is an open additive subgroup **of `R` carried with the topology `I.adicTopology`**.
A ring is usually met the other way round: it comes with a topology already, and `IsAdic I` is
the statement that this topology *is* the `I`-adic one. The results here transport such facts
across that equation — the openness, the complementary closedness, and the topological
nilpotence of the elements of `I` — so that a ring satisfying `IsAdic I` may be used directly.

Closedness is the form these are wanted in: an infinite sum all of whose terms lie in `I ^ n`
again lies in `I ^ n`, because `I ^ n` is closed and `tsum_mem` applies. That is how a power
series evaluated at arguments of `I ^ n` is confined to `I ^ n`, in
`TauCeti.RingTheory.MvPowerSeries.Evaluation`.

## Main results

* `IsAdic.isOpen_pow` : in a ring whose topology is `I`-adic, every power of `I` is open.
* `IsAdic.isClosed_pow` : in a ring whose topology is `I`-adic, every power of `I` is closed —
  an open additive subgroup of a topological group being closed.
* `IsAdic.isTopologicallyNilpotent_of_mem` : in a ring whose topology is `I`-adic, every element
  of `I` is topologically nilpotent.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/Mathlib/Chabauty/AdicTopology.lean`, where these appear under the same names
among that development's Mathlib-bound material. That file describes its contents as the
`IsAdic` counterparts of `Ideal.isLinearTopology` and `WithIdeal.isTopologicallyNilpotent_of_mem`,
which is the reading taken here.
-/

public section

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}

/-- In a ring whose topology is the `I`-adic one, every power of `I` is open. -/
theorem isOpen_pow (hI : IsAdic I) (n : ℕ) : IsOpen ((I ^ n : Ideal R) : Set R) := by
  simp only [IsAdic] at hI
  subst hI
  let : TopologicalSpace R := I.adicTopology
  exact (I.openAddSubgroup n).isOpen'

/-- In a ring whose topology is the `I`-adic one, every power of `I` is closed: it is an open
additive subgroup, and an open subgroup of a topological group is closed. -/
theorem isClosed_pow (hI : IsAdic I) (n : ℕ) : IsClosed ((I ^ n : Ideal R) : Set R) := by
  have hopen := hI.isOpen_pow n
  simp only [IsAdic] at hI
  subst hI
  let : TopologicalSpace R := I.adicTopology
  have : NonarchimedeanRing R := I.nonarchimedean
  exact AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen

/-- In a ring whose topology is the `I`-adic one, every element of `I` is topologically
nilpotent. -/
-- Mathlib proves this for its `WithIdeal` class, whose topology is adic by construction. A ring
-- that merely satisfies `IsAdic I` already carries a topology of its own, so it cannot take that
-- instance without a second one; the argument is therefore run against
-- `IsAdic.hasBasis_nhds_zero`.
theorem isTopologicallyNilpotent_of_mem (hI : IsAdic I) {a : R} (ha : a ∈ I) :
    IsTopologicallyNilpotent a := by
  suffices ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → a ^ n ∈ I ^ m by
    simpa [IsTopologicallyNilpotent, hI.hasBasis_nhds_zero.tendsto_right_iff]
  exact fun m ↦ ⟨m, fun n hn ↦ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

end IsAdic
