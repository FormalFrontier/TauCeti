/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Isometry.Equiv
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity

/-!
# Schwarz–Pick for the metric space `PoincareDisc`

Layer **L2** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) asks
for two things at once: the Schwarz–Pick theorem, and the hyperbolic (Poincaré) metric on the
disc. Both are on `main`, but they meet only at the level of the scalar function
`TauCeti.hyperbolicDist`: `TauCeti.hyperbolicDist_map_le` says a holomorphic self-map of
`Metric.ball (0 : ℂ) 1` does not increase `hyperbolicDist`, while the metric space carrying that
distance is the type synonym `TauCeti.PoincareDisc` of `Conformal/Poincare/MetricSpace.lean`. This
file states Schwarz–Pick *for that metric space*, so that the theorem becomes a statement in the
vocabulary of `Metric` — `LipschitzWith 1` and `Isometry` — that a metric-geometry consumer can use
without unfolding the distance.

The shape is the one `Conformal/Poincare/Isometry/Classification.lean` already uses for the
isometries: a self-map `F : PoincareDisc → PoincareDisc` is related to a scalar map `f : ℂ → ℂ` by
the hypothesis `(toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ)`, so that the analytic hypothesis
`DifferentiableOn` is stated where holomorphy lives, on `ℂ`, and the conclusions are stated where
the metric lives, on `PoincareDisc`. No new definition is introduced: `F` is whatever map the
consumer already has, and the representation hypothesis is what a consumer holding a holomorphic
self-map of the disc can always supply. That hypothesis already forces `f` to carry the unit disc
into itself — the value `f (toUnitDisc z : ℂ)` is a coordinate of `PoincareDisc` — so none of the
theorems below asks for a separate `MapsTo` hypothesis.

## What the metric form adds

Two statements are genuinely new here rather than transcriptions.

The first is the sharpening of the isometry classification. On `PoincareDisc` the isometries are
`Aut(𝔻)` *together with its orientation-reversing coset* (the theorem
`isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star` of
`Conformal/Poincare/Isometry/Classification.lean`), conjugation being a hyperbolic isometry that is
not holomorphic. Restricted to the maps that *are* holomorphic, that coset disappears:
`TauCeti.PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv` says a
holomorphic self-map of the Poincaré disc is an isometry exactly when it is one of the standard
disc automorphisms. So `Aut(𝔻)` is not merely a subgroup of the isometry group; it is the whole of
its holomorphic part.

The second is the dichotomy `TauCeti.PoincareDisc.forall_dist_lt_or_isometry`: a holomorphic
self-map either strictly decreases the Poincaré distance between *every* pair of distinct points,
or preserves it between every pair. There is no intermediate behaviour — a single pair at which
the Schwarz–Pick inequality is an equality already forces the map to be a disc automorphism, which
is the rigidity
`TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq`
read in the metric.

## Main results

* `TauCeti.PoincareDisc.dist_map_le` and `TauCeti.PoincareDisc.lipschitzWith_one` —
  **Schwarz–Pick, metric form**: a holomorphic self-map of the disc is nonexpanding for the
  Poincaré metric.
* `TauCeti.PoincareDisc.exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq` —
  **rigidity, metric form**: preserving the Poincaré distance between one pair of distinct points
  makes the map a standard disc automorphism.
* `TauCeti.PoincareDisc.isometry_of_dist_eq` — and hence an isometry.
* `TauCeti.PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv` — **the
  holomorphic isometries of the Poincaré disc are exactly `Aut(𝔻)`**.
* `TauCeti.PoincareDisc.forall_dist_lt_or_isometry` — strict contraction everywhere, or isometry.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes the scalar
target `ℂ` for every theorem added in layers L0–L6, the scalar map `f` is a map of `ℂ`. The domain
is the unit disc rather than a general disc because `PoincareDisc` is the unit disc; the
hyperbolic metric of a domain biholomorphic to it is a separate transport question and is not
touched here.

## Coordination with upstream Mathlib

Mathlib has no Poincaré metric on the disc — its hyperbolic material lives on `UpperHalfPlane` —
so it has no metric form of Schwarz–Pick either, and this file is new Lean formalization rather
than a temporary shim. Its scalar inputs are the L2 material of `Conformal/Hyperbolic/Distance.lean`
and `Conformal/SchwarzPick/Rigidity.lean`, which are coordinated with the in-progress
human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505); should a
human-curated Poincaré metric land upstream, this file is to be refactored onto it.

## References

* L. V. Ahlfors, *Conformal Invariants: Topics in Geometric Function Theory*, Ch. 1.
* J. B. Garnett and D. E. Marshall, *Harmonic Measure*, Ch. I §1 (the hyperbolic metric and
  Schwarz–Pick).
-/

public section

namespace TauCeti

open Metric Set

namespace PoincareDisc

variable {F : PoincareDisc → PoincareDisc} {f : ℂ → ℂ}

/-- The representation hypothesis shared by the theorems below is satisfiable, so none of them is
vacuous, and this is how a consumer holding only a scalar map discharges it: a map `f` of `ℂ`
carrying the unit disc into itself is represented by the self-map of `PoincareDisc` that reads a
point as a complex number, applies `f`, and reads the result back. Holomorphy of `f` plays no part
in producing the representative; it is only the estimates that need it. -/
example (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    ∃ F : PoincareDisc → PoincareDisc,
      ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ) :=
  ⟨fun z => Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk (f (toUnitDisc z : ℂ))
    (mem_ball_zero_iff.mp (hmaps (coe_mem_ball z)))), fun _ => rfl⟩

/-- A map of `ℂ` representing a self-map of `PoincareDisc` carries the unit disc into itself: each
value `f x` is the coordinate of a point of `PoincareDisc`. This is what lets the theorems below ask
only for the representation hypothesis, and it supplies the `MapsTo` hypothesis of their scalar
inputs. -/
private lemma mapsTo_of_rep
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ)) :
    MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := fun x hx => by
  have hx' := hrep (Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk x (mem_ball_zero_iff.mp hx)))
  rw [toUnitDisc_toPoincare, Complex.UnitDisc.coe_mk] at hx'
  exact hx' ▸ coe_mem_ball _

/-- **Schwarz–Pick for the Poincaré metric.** A self-map `F` of the Poincaré disc represented by a
holomorphic self-map `f` of the unit disc does not increase the Poincaré distance.

This is `TauCeti.hyperbolicDist_map_le` read through the metric-space instance of
`TauCeti.PoincareDisc`; the bundled `LipschitzWith` form is `TauCeti.PoincareDisc.lipschitzWith_one`
below. -/
theorem dist_map_le (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ))
    (z w : PoincareDisc) : dist (F z) (F w) ≤ dist z w := by
  simp only [dist_eq, hrep]
  exact hyperbolicDist_map_le hf (mapsTo_of_rep hrep) (coe_mem_ball z) (coe_mem_ball w)

/-- **Schwarz–Pick, Lipschitz form.** A holomorphic self-map of the unit disc is a nonexpanding
map of the metric space `TauCeti.PoincareDisc`.

Together with
`TauCeti.PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv` this says
that a holomorphic self-map of the Poincaré disc is nonexpanding, and is an isometry precisely
when it is a disc automorphism. -/
theorem lipschitzWith_one (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ)) :
    LipschitzWith 1 F :=
  LipschitzWith.of_dist_le_mul fun z w => by
    simpa using dist_map_le hf hrep z w

/-- **The equality case of Schwarz–Pick, bundled.** A holomorphic self-map of the unit disc that
preserves the Poincaré distance between one pair of distinct points *is* a standard disc
automorphism, as a map of `TauCeti.PoincareDisc`.

This is the bundled reading of
`TauCeti.exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq`,
whose conclusion is an identity of scalar functions on `Complex.UnitDisc`; here it is an identity
of self-maps of the metric space, against the isometric equivalences
`TauCeti.PoincareDisc.unitDiscStandardAutomorphismIsometryEquiv`. -/
theorem exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ))
    {z w : PoincareDisc} (hne : z ≠ w) (heq : dist (F z) (F w) = dist z w) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      ∀ ζ : PoincareDisc, F ζ = unitDiscStandardAutomorphismIsometryEquiv u a ζ := by
  have hne' : (toUnitDisc z : ℂ) ≠ (toUnitDisc w : ℂ) := fun h =>
    hne (toUnitDisc.injective (Complex.UnitDisc.coe_injective h))
  have heq' : hyperbolicDist (f (toUnitDisc z : ℂ)) (f (toUnitDisc w : ℂ))
      = hyperbolicDist (toUnitDisc z : ℂ) (toUnitDisc w : ℂ) := by
    simpa only [dist_eq, hrep] using heq
  obtain ⟨u, a, hua⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_hyperbolicDist_map_eq hf
      (mapsTo_of_rep hrep) (coe_mem_ball z) (coe_mem_ball w) hne' heq'
  refine ⟨u, a, fun ζ => toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)⟩
  rw [unitDiscStandardAutomorphismIsometryEquiv_apply, toUnitDisc_toPoincare, hrep ζ]
  exact hua (toUnitDisc ζ)

/-- **Schwarz–Pick rigidity for the Poincaré metric.** If a holomorphic self-map of the unit disc
preserves the Poincaré distance between a *single* pair of distinct points, it preserves it between
every pair: the nonexpanding map of `TauCeti.PoincareDisc.lipschitzWith_one` is an isometry.

This is the unbundled reading of
`TauCeti.PoincareDisc.exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq`, the disc
automorphism it produces being an isometric equivalence. -/
theorem isometry_of_dist_eq (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ))
    {z w : PoincareDisc} (hne : z ≠ w) (heq : dist (F z) (F w) = dist z w) : Isometry F := by
  obtain ⟨u, a, hcase⟩ :=
    exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq hf hrep hne heq
  exact funext hcase ▸ (unitDiscStandardAutomorphismIsometryEquiv u a).isometry

/-- **The holomorphic isometries of the Poincaré disc are exactly the disc automorphisms.** A
holomorphic self-map of the unit disc is a Poincaré isometry if and only if it is one of the
standard automorphisms `z ↦ u * (z - a) / (1 - conj a * z)`.

This sharpens the theorem
`isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv_or_comp_star` of
`Conformal/Poincare/Isometry/Classification.lean`,
which classifies *all* Poincaré isometries and has to admit the orientation-reversing coset of
`Aut(𝔻)`: the conjugation `TauCeti.PoincareDisc.starIsometryEquiv` is an isometry, so that
alternative cannot be dropped there. It disappears here because holomorphy excludes it. Hence the
disc automorphisms are precisely the holomorphic part of the isometry group. -/
theorem isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ)) :
    Isometry F ↔ ∃ (u : Circle) (a : Complex.UnitDisc),
      ∀ ζ : PoincareDisc, F ζ = unitDiscStandardAutomorphismIsometryEquiv u a ζ := by
  refine ⟨fun hF => ?_, ?_⟩
  · -- Spend the equality case at the pair of distinct points `0` and `1 / 2`, at which the
    -- isometry certainly preserves the distance.
    have hhalf : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have hne : Complex.UnitDisc.toPoincare 0 ≠
        Complex.UnitDisc.toPoincare (Complex.UnitDisc.mk _ hhalf) := by
      intro h
      have h₀ : (0 : Complex.UnitDisc) = Complex.UnitDisc.mk _ hhalf := by
        simpa using congrArg toUnitDisc h
      have h₁ : ((0 : Complex.UnitDisc) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        rw [h₀, Complex.UnitDisc.coe_mk]
      rw [Complex.UnitDisc.coe_zero] at h₁
      norm_num at h₁
    exact exists_eq_unitDiscStandardAutomorphismIsometryEquiv_of_dist_eq hf hrep hne
      (hF.dist_eq _ _)
  · rintro ⟨u, a, hcase⟩
    exact funext hcase ▸ (unitDiscStandardAutomorphismIsometryEquiv u a).isometry

/-- **A holomorphic self-map of the Poincaré disc is a strict contraction or an isometry.** For a
holomorphic self-map of the unit disc, either the Poincaré distance between *every* pair of
distinct points strictly decreases, or it is preserved between every pair — in which case the map
is one of the disc automorphisms, by
`TauCeti.PoincareDisc.isometry_iff_exists_eq_unitDiscStandardAutomorphismIsometryEquiv`. Nothing
in between occurs: one pair at which Schwarz–Pick is an equality decides the whole map.

The two alternatives cannot both hold, since `PoincareDisc` has distinct points and an isometry
preserves the distance between them; the statement is left a plain disjunction because that is the
form a consumer case-splits on. -/
theorem forall_dist_lt_or_isometry (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hrep : ∀ z : PoincareDisc, (toUnitDisc (F z) : ℂ) = f (toUnitDisc z : ℂ)) :
    (∀ z w : PoincareDisc, z ≠ w → dist (F z) (F w) < dist z w) ∨ Isometry F := by
  by_cases h : ∃ z w : PoincareDisc, z ≠ w ∧ dist (F z) (F w) = dist z w
  · obtain ⟨z, w, hne, heq⟩ := h
    exact Or.inr (isometry_of_dist_eq hf hrep hne heq)
  · exact Or.inl fun z w hne =>
      lt_of_le_of_ne (dist_map_le hf hrep z w) fun heq => h ⟨z, w, hne, heq⟩

end PoincareDisc

end TauCeti
