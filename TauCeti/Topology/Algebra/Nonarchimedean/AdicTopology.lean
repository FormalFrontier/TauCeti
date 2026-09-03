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
* `IsAdic.tendsto_zero_of_mem_pow` : a family whose members lie in growing powers of `I` tends to
  zero, provided the exponents tend to infinity.
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
theorem isOpen_pow (hI : IsAdic I) (n : ℕ) : IsOpen ((I ^ n : Ideal R) : Set R) :=
  letI := I.adicTopology
  hI ▸ (I.openAddSubgroup n).isOpen

/-- In a ring whose topology is the `I`-adic one, every power of `I` is closed: it is an open
additive subgroup, and an open subgroup of a topological group is closed. -/
theorem isClosed_pow (hI : IsAdic I) (n : ℕ) : IsClosed ((I ^ n : Ideal R) : Set R) :=
  have : NonarchimedeanRing R := hI ▸ I.nonarchimedean
  AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup (hI.isOpen_pow n)

open Filter Topology in
/-- In a ring whose topology is the `I`-adic one, a family whose members lie in growing powers of
`I` tends to zero, provided the exponents tend to infinity. Only eventual membership is needed,
since convergence along `l` cannot see failures outside an `l`-large set; a pointwise caller
supplies `Filter.Eventually.of_forall`. The index filter is arbitrary: `atTop` for a sequence,
`cofinite` for the decay condition of `MvPowerSeries.HasEval`. For the powers of a single element
of `I` use `IsAdic.isTopologicallyNilpotent_of_mem` instead. -/
theorem tendsto_zero_of_mem_pow (hI : IsAdic I) {γ : Type*} {l : Filter γ} {g : γ → R} {e : γ → ℕ}
    (hg : ∀ᶠ i in l, g i ∈ I ^ e i) (he : Tendsto e l atTop) : Tendsto g l (𝓝 0) :=
  hI.hasBasis_nhds_zero.tendsto_right_iff.2 fun k _ ↦ by
    filter_upwards [hg, he.eventually_ge_atTop k] with i hi hik
    exact Ideal.pow_le_pow_right hik hi

/-- In a ring whose topology is the `I`-adic one, every element of `I` is topologically
nilpotent. -/
theorem isTopologicallyNilpotent_of_mem (hI : IsAdic I) {a : R} (ha : a ∈ I) :
    IsTopologicallyNilpotent a :=
  hI.tendsto_zero_of_mem_pow (.of_forall (Ideal.pow_mem_pow ha)) Filter.tendsto_id

end IsAdic
