/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.Analysis.Complex.Conformal.JordanDomain.Basic
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# The convex Jordan domains

`Conformal/JordanDomain/Basic.lean` introduces `TauCeti.IsJordanDomain` — a bounded domain of `ℂ`
whose frontier is a Jordan curve — and exhibits one example, the disc. That is a thin supply for a
predicate whose whole point is to be a hypothesis: layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` is the Carathéodory boundary correspondence, whose
"concrete L5 milestone is the **Jordan-domain case**: the RMT map of a Jordan domain extends to a
homeomorphism of closures", and the disc is the *target* of that map rather than an interesting
source. This file adds the first substantial family: **every bounded convex domain of `ℂ` is a
Jordan domain**, and more generally the interior of any bounded convex set with nonempty interior
is one. An elliptical disc, the interior of a convex polygon with nonempty interior, and any
nonempty bounded intersection of *finitely many* open half-planes all fall under it. Finiteness is
not decoration: an infinite intersection of open half-planes is convex but need not be open, so
only its interior is a domain.

## The Schoenflies question, in the convex case

`STATUS` for this roadmap records that the strong topology of Jordan curves — the Jordan curve
theorem and the Schoenflies theorem — is not available in this development, and asks whoever
attacks L5 to settle what is reachable without it. For convex sets the question has a clean
answer, and it is already answered in the pinned Mathlib: a bounded convex set `s` with nonempty
interior admits an *ambient* homeomorphism `e : ℂ ≃ₜ ℂ` carrying `interior s` onto `ball 0 1`,
`closure s` onto `closedBall 0 1` and `frontier s` onto `sphere 0 1`
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, proved there by rescaling along
the gauge of `s`). That is precisely a Schoenflies homeomorphism for the convex case, so nothing
below needs the general theorem: being a Jordan curve is invariant under a homeomorphism of the
ambient space (`TauCeti.isJordanCurve_image_homeomorph_iff`), and the circle is a Jordan curve
(`TauCeti.isJordanCurve_sphere`).

The three sets have to be handled together — the hypothesis of the Mathlib theorem is nonemptiness
of the *interior*, not of `s` — which is why the frontier statement below is proved for an
arbitrary bounded convex set and only then specialized to an open one. Reading it at that
generality is not idle: a closed convex body, such as a filled polygon, is not a domain, but its
interior is, and the two have the same frontier
(`Convex.closure_interior_eq_closure_of_nonempty_interior`).

## What this gives the boundary layer

A Jordan domain carries the geometric hypotheses that the unproved direction of the L5 milestone
consumes: `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier` and its uniform form
`TauCeti.IsJordanDomain.isUniformlyLocallyConnected_frontier`, which is what
`Conformal/CutDiameter.lean` names as the second of its two geometric inputs. A bounded convex
domain also carries a Riemann map, and needs no lemma of its own for it: a nonempty convex set is
contractible (`Convex.contractibleSpace`), hence simply connected, and
`TauCeti.IsJordanDomain.ne_univ` makes it proper, so
`TauCeti.exists_bijOn_ball_differentiableOn_invFunOn` applies as it stands. So a bounded convex
domain instantiates *both* halves of the L5 milestone's hypothesis at once — a Jordan domain
together with the conformal map of it whose boundary behaviour the milestone is about — which no
set other than the disc did before.

## Main results

* `TauCeti.isJordanCurve_frontier_of_convex` — the frontier of a bounded convex subset of `ℂ` with
  nonempty interior is a Jordan curve.
* `TauCeti.isJordanDomain_interior_of_convex` — hence the interior of such a set is a Jordan
  domain, and `TauCeti.isJordanDomain_of_convex` — a bounded convex domain is a Jordan domain.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for subsets of `ℂ`. The restriction
is not a convention here but the mathematics: `TauCeti.IsJordanCurve` asks for a homeomorphism with
the *circle*, so the frontier statement is false in every dimension other than two, the frontier of
a convex body in `ℝⁿ` being an `(n-1)`-sphere.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no Jordan-curve vocabulary. So this file is new Lean formalization rather than a
temporary shim; the convexity inputs it rests on are all consumed from Mathlib rather than rebuilt.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* R. Schneider, *Convex Bodies: the Brunn–Minkowski Theory*, §1.1 (the boundary of a convex body
  is a sphere).
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {s : Set ℂ}

/-! ## The frontier of a convex body -/

/-- **The frontier of a bounded convex subset of `ℂ` with nonempty interior is a Jordan curve.**

The set itself is not asked to be open or nonempty: what a convex set needs in order to have a
one-dimensional frontier is that it be *solid*, and that is `(interior s).Nonempty`. Without it the
statement fails — a segment is convex and bounded, and its frontier is the segment itself. -/
theorem isJordanCurve_frontier_of_convex (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : IsBounded s) : IsJordanCurve (frontier s) := by
  -- Mathlib's gauge rescaling supplies a homeomorphism of the plane carrying `frontier s` onto
  -- the unit circle: a Schoenflies homeomorphism for the convex case.
  obtain ⟨e, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hs hne hb
  refine (isJordanCurve_image_homeomorph_iff e).mp ?_
  rw [hfr]
  exact isJordanCurve_sphere 0 one_pos

/-! ## Convex domains -/

/-- **The interior of a bounded convex set with nonempty interior is a Jordan domain.**

This is the form to use on a closed convex body: a filled polygon or a closed disc is not a domain,
but its interior is one, and the two are bounded by the same curve. -/
theorem isJordanDomain_interior_of_convex (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : IsBounded s) : IsJordanDomain (interior s) where
  isOpen := isOpen_interior
  isConnected := hs.interior.isConnected hne
  isBounded := hb.subset interior_subset
  isJordanCurve_frontier := by
    -- A solid convex set is the closure of its interior, so the two have the same frontier.
    have hfr : frontier (interior s) = frontier s := by
      rw [frontier, frontier, interior_interior,
        hs.closure_interior_eq_closure_of_nonempty_interior hne]
    rw [hfr]
    exact isJordanCurve_frontier_of_convex hs hne hb

/-- **A bounded convex domain of `ℂ` is a Jordan domain.**

This is `TauCeti.isJordanDomain_interior_of_convex` at an open set. It is the first family of
Jordan domains beyond the disc, and the one the L5 milestone can be read against: an elliptical
disc, the interior of a convex polygon with nonempty interior, and any nonempty bounded
intersection of *finitely many* open half-planes are Jordan domains — finitely many, since an
infinite intersection of open half-planes need not be open, and then it is its interior that
`TauCeti.isJordanDomain_interior_of_convex` covers. Each of them carries a Riemann map, whose
boundary behaviour the milestone predicts, by `TauCeti.exists_bijOn_ball_differentiableOn_invFunOn`
at a convex set. -/
theorem isJordanDomain_of_convex (hs : Convex ℝ s) (ho : IsOpen s) (hne : s.Nonempty)
    (hb : IsBounded s) : IsJordanDomain s := by
  have h := isJordanDomain_interior_of_convex hs (by rwa [ho.interior_eq]) hb
  rwa [ho.interior_eq] at h

end TauCeti
