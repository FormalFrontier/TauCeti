/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA

/-!
# The weak Mordell–Weil theorem: `E(K)/2E(K)` is finite

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, and let `R` be a Dedekind domain with fraction field `K`. **Step 7**, and
with it the weak Mordell–Weil theorem, is `finiteIndex_range_nsmulAddMonoidHom_two`: the subgroup
`2E(K)` has finite index in `E(K)`.

Everything hard is already done. Step 4 (`ker_μ_eq`) says the kernel of the descent map `μ` is
exactly `2E(K)`, so `E(K)/2E(K)` embeds into the image of `μ`; Step 6
(`range_μ_le_selmerGroupA`) confines that image to `A(S,2)`. All that remains is that `A(S,2)` is
finite, and that is `finite_selmerGroupA`, proved beside `selmerGroupA` itself.

The finiteness hypotheses are carried as instances on the factors: each factor's ring of integers
has finite class group and finitely generated unit group. For `K` a number field these are the
class number theorem and Dirichlet's unit theorem; they are hypotheses here because this file is
about an arbitrary Dedekind domain.

## Main results

* `WeierstrassCurve.Affine.finiteIndex_range_nsmulAddMonoidHom_two_iff`: the criterion — `2E(K)`
  has finite index exactly when the image of `μ` is finite.
* `WeierstrassCurve.Affine.finiteIndex_range_nsmulAddMonoidHom_two`: **the weak Mordell–Weil
  theorem.**

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil), lines 790–838: Step 7 of the
weak Mordell–Weil theorem. It is the input to the descent argument in the Mordell–Weil theorem
proper.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean`, the criterion at `:799` and section `Step7`. The source is
written against Lean `v4.32.0`; this is a forward port.

The source proves `A(S,2)` finite by hand, through two `Subgroup` finiteness facts of its own
(`Subgroup.instFinitePi` and `Subgroup.finite_comap_of_injective`) and a per-factor
`finite_selmerGroupFactor`. None of those are needed here: this repository states `selmerGroupA` as
`IsDedekindDomain.selmerGroupOfEquiv`, whose finiteness is already
`IsDedekindDomain.finite_selmerGroupOfEquiv`.
-/

public section

namespace WeierstrassCurve.Affine

open IsDedekindDomain

variable {K : Type*} [Field K] (W : Affine K) [W.IsElliptic] [W.IsCharNeTwoNF]

section Criterion

variable [DecidableEq K]

/-- **The criterion behind the weak Mordell–Weil theorem**: `2E(K)` has finite index in `E(K)`
exactly when the image of the descent map is finite.

`E(K)/2E(K)` and the image of `μ` are the same group, so finiteness of either is finiteness of
the other. -/
lemma finiteIndex_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

end Criterion

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
  [(p : W.f.Factors) → Monoid.FG (W.ringOfIntegersFactor R p)ˣ]

variable [DecidableEq K]

include R in
/-- **The weak Mordell–Weil theorem**: `E(K)/2E(K)` is finite, for an elliptic curve in the normal
form `y² = x³ + a₂x² + a₄x + a₆` over the fraction field `K` of a Dedekind domain `R`, provided
that for each irreducible factor `p` of the cubic the ring of integers of `K[X] ⧸ (p)` has finite
class group and finitely generated unit group.

This is the input to the descent argument in the Mordell–Weil theorem proper. -/
theorem finiteIndex_range_nsmulAddMonoidHom_two :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex := by
  rw [W.finiteIndex_range_nsmulAddMonoidHom_two_iff]
  have := W.finite_selmerGroupA R
  exact ((W.selmerGroupA R : Set W.M).toFinite.subset (W.range_μ_le_selmerGroupA R)).to_subtype

end WeierstrassCurve.Affine

end
