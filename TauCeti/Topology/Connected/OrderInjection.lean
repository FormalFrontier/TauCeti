/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# A set whose punctures stay preconnected does not inject into a line

A point of a linearly ordered space separates it: an order-densely populated line, cut at an
interior point of a preconnected subset, falls apart. A preconnected set with the *opposite*
property — removing any one of its points leaves it preconnected — therefore cannot be laid out
along a line by a continuous injection unless it is a single point. That is the content of
`TauCeti.subsingleton_of_continuousOn_injOn`, the only result of this file.

The argument is the intermediate value theorem used twice. Let `ψ` be continuous and injective on
`S` and let `a`, `b ∈ S` have `ψ a < ψ b`. The image `ψ '' S` is preconnected, hence
order-connected (`IsPreconnected.Icc_subset`), so it contains every value `c` strictly between
`ψ a` and `ψ b`, say `c = ψ x` with `x ∈ S`; injectivity places `x` away from both `a` and `b`.
Now delete `x`. The set `S \ {x}` is still preconnected and still contains `a` and `b`, so its
image again contains `c` — but the only point of `S` taking the value `c` is `x`, which is gone.

## Sets without cut points

The hypothesis `∀ x ∈ S, IsPreconnected (S \ {x})` says that `S` has no cut point. A circle has
none, and so does a disc; a closed interval has one at each of its interior points, and a line has
one everywhere. So the theorem says that a preconnected set with no cut point and more than one
point carries no continuous injection into a line — which is exactly how
`TauCeti/Topology/JordanCurve/EmptyInterior.lean` uses it, with `S` a circle of `ℂ` sitting inside
a curve and the line `ℝ`.

Both hypotheses on `S` are needed. Dropping preconnectedness of `S` itself leaves the two-point
set, whose punctures are singletons and which injects continuously into `ℝ`; dropping
preconnectedness of the punctures leaves a closed interval, which is its own image under the
identity.

## Generality

The target is an arbitrary linear order with an order-closed topology in which the order is dense,
which is exactly what the two ingredients need: `IsPreconnected.Icc_subset` for the first and
`exists_between` for the choice of the intermediate value. The real line is the case the plane
consequences use. The source is an arbitrary topological space; no separation axiom, metric or
compactness enters.

## References

* K. Kuratowski, *Topology II*, §46 (cut points and the classification of the one-dimensional
  continua).
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {α : Type*} [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α] [DenselyOrdered α] {S : Set X} {ψ : X → α}

/-- **A preconnected set that stays preconnected after any one of its points is removed carries no
continuous injection into a densely ordered line, unless it is a single point.**

The values `ψ a < ψ b` at two points of `S` bracket an intermediate value `c`, which the
preconnected image `ψ '' S` must attain, at a point `x` of `S` distinct from `a` and `b`. Removing
`x` keeps `S` preconnected and keeps `a` and `b`, so `c` is attained again — at a second point of
`S`, contradicting injectivity.

The hypothesis on the punctures says that `S` has no cut point; it holds for a circle and for a
disc, and fails for an interval and for a line. -/
theorem subsingleton_of_continuousOn_injOn (hS : IsPreconnected S)
    (hpunct : ∀ x ∈ S, IsPreconnected (S \ {x})) (hψc : ContinuousOn ψ S) (hψi : S.InjOn ψ) :
    S.Subsingleton := by
  have key : ∀ a ∈ S, ∀ b ∈ S, ψ a < ψ b → False := by
    intro a ha b hb hab
    -- an intermediate value `c` is attained at some `x ∈ S`, necessarily distinct from `a`, `b`
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    obtain ⟨x, hx, hxc⟩ :=
      (hS.image ψ hψc).Icc_subset ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨hac.le, hcb.le⟩
    have hxa : a ≠ x := by rintro rfl; exact hac.ne hxc
    have hxb : b ≠ x := by rintro rfl; exact hcb.ne' hxc
    -- deleting `x` keeps `a` and `b`, so the same intermediate value is attained a second time
    obtain ⟨y, hy, hyc⟩ :=
      ((hpunct x hx).image ψ (hψc.mono sdiff_subset)).Icc_subset ⟨a, ⟨ha, hxa⟩, rfl⟩
        ⟨b, ⟨hb, hxb⟩, rfl⟩ ⟨hac.le, hcb.le⟩
    exact hy.2 (hψi hy.1 hx (hyc.trans hxc.symm))
  intro a ha b hb
  rcases lt_trichotomy (ψ a) (ψ b) with h | h | h
  · exact (key a ha b hb h).elim
  · exact hψi ha hb h
  · exact (key b hb a ha h).elim

end TauCeti
