/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Betweenness

/-!
# The hyperbolic lines of the Poincaré disc

`Poincare/Geodesic.lean` introduces the unit-speed geodesic lines *through the origin* of the
Poincaré disc — the Euclidean diameters `TauCeti.PoincareDisc.radialGeodesic u`, reparametrised by
`Real.tanh` — and `Poincare/Betweenness.lean` shows they are the only ones through the origin
(`TauCeti.PoincareDisc.existsUnique_eq_radialGeodesic`). This file removes the restriction to the
origin: it names the geodesic line through an **arbitrary** point, classifies every unit-speed
geodesic line of the Poincaré disc as one of them, and deduces the incidence statement that two
distinct points lie on exactly one hyperbolic line.

## The line through a point in a direction

`TauCeti.PoincareDisc.geodesicLine a u` is the radial geodesic in direction `u : Circle` carried
back by the Moebius isometry that sends `a` to the origin. So it starts at `a` at time `0`, is a
unit-speed isometric embedding of `ℝ`, and reduces to `radialGeodesic u` when `a` *is* the origin.
No new geometry is needed for any of this: the disc automorphisms act on the Poincaré disc by
isometries (`TauCeti.PoincareDisc.unitDiscMoebiusIsometryEquiv`) and transitively, so conjugating
by one of them turns a statement about the origin into the same statement about `a`. That is also
the whole proof of the classification — for a unit-speed geodesic line `γ`, the composite
`unitDiscMoebiusIsometryEquiv (γ 0) ∘ γ` is a geodesic line *through the origin*, hence a radial
one for a unique direction.

## Hyperbolic lines as sets

A `TauCeti.PoincareDisc.IsGeodesicLine` is a subset of the disc of the form
`Set.range (geodesicLine a u)`: a hyperbolic line with its parametrisation forgotten. Forgetting
the parametrisation is what makes the incidence statement clean, because one line carries many
parametrisations. `Set.range` is unchanged by a time shift and by time reversal, and both of those
are again unit-speed geodesic lines, hence again of the form `geodesicLine a u` by the
classification. Two moves therefore normalise any line through a prescribed point `z`: shift so
that it starts at `z`, and reverse if it reaches the second point at a negative time. After that,
`TauCeti.PoincareDisc.existsUnique_geodesicLine_dist_eq` pins the direction, because
`radialGeodesic u (dist z w)` reads `u * Real.tanh (dist z w)` and `Real.tanh` vanishes only
at `0`.

## Main results

* `TauCeti.PoincareDisc.geodesicLine` — the unit-speed geodesic line through `a` in the direction
  `u`, with `TauCeti.PoincareDisc.isometry_geodesicLine` and
  `TauCeti.PoincareDisc.geodesicLine_zero`.
* `TauCeti.PoincareDisc.existsUnique_eq_geodesicLine` — **the classification of the geodesic
  lines**: every isometric embedding of `ℝ` into the Poincaré disc is `geodesicLine (γ 0) u` for a
  unique direction `u`.
* `TauCeti.PoincareDisc.existsUnique_geodesicLine_dist_eq` — through two distinct points there is
  exactly one direction at the first that reaches the second, and it reaches it at time their
  distance.
* `TauCeti.PoincareDisc.IsGeodesicLine` and
  `TauCeti.PoincareDisc.isGeodesicLine_iff_exists_isometry` — hyperbolic lines as sets, and the
  fact that they are exactly the ranges of the unit-speed geodesic lines.
* `TauCeti.PoincareDisc.existsUnique_isGeodesicLine_mem` — **the incidence theorem**: two distinct
  points of the Poincaré disc lie on exactly one hyperbolic line.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`), generalising off the origin the geodesic classification that
`Poincare/Betweenness.lean` proved there. It reuses Tau Ceti's radial-geodesic and
disc-automorphism-isometry API rather than redoing any hyperbolic computation. As with the rest of
the L0--L3 conformal-mapping material it is coordinated with the upstream Mathlib Riemann-mapping
effort leanprover-community/mathlib4#33505 and the preceding human-curated work in
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`; none of that
contains a Poincaré metric on the disc, Mathlib has no notion of geodesic space or geodesic line,
and its hyperbolic geometry on the upper half-plane (`Analysis/Complex/UpperHalfPlane`) has no
geodesics, so nothing here duplicates upstream material. Should a human-curated Poincaré disc land
upstream, this file should be refactored onto it.
-/

public section

namespace TauCeti

namespace PoincareDisc

open Set

/-! ### The geodesic line through a point in a direction -/

/-- The unit-speed geodesic line of the Poincaré disc through `a` in the direction `u : Circle`:
the radial geodesic `TauCeti.PoincareDisc.radialGeodesic u` transported by the Moebius isometry
that carries `a` to the origin. -/
noncomputable def geodesicLine (a : PoincareDisc) (u : Circle) (t : ℝ) : PoincareDisc :=
  (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm (radialGeodesic u t)

/-- The defining formula for `TauCeti.PoincareDisc.geodesicLine`; its body is not `@[expose]`d, so
this is how the definition is unfolded downstream. -/
lemma geodesicLine_def (a : PoincareDisc) (u : Circle) (t : ℝ) :
    geodesicLine a u t =
      (unitDiscMoebiusIsometryEquiv (toUnitDisc a)).symm (radialGeodesic u t) := by
  rw [geodesicLine]

/-- The Moebius isometry centred at `a` straightens the geodesic line through `a` into the radial
geodesic in the same direction. This is `TauCeti.PoincareDisc.geodesicLine_def` read forwards, and
it is how every statement below is transported to the origin. -/
lemma unitDiscMoebiusIsometryEquiv_geodesicLine (a : PoincareDisc) (u : Circle) (t : ℝ) :
    unitDiscMoebiusIsometryEquiv (toUnitDisc a) (geodesicLine a u t) = radialGeodesic u t := by
  rw [geodesicLine_def, IsometryEquiv.apply_symm_apply]

/-- Every geodesic line through `a` starts at `a`. -/
@[simp]
lemma geodesicLine_zero (a : PoincareDisc) (u : Circle) : geodesicLine a u 0 = a := by
  have ha : unitDiscMoebiusIsometryEquiv (toUnitDisc a) a = Complex.UnitDisc.toPoincare 0 := by
    rw [unitDiscMoebiusIsometryEquiv_apply, unitDiscMoebius_self]
  rw [geodesicLine_def, radialGeodesic_zero, ← ha, IsometryEquiv.symm_apply_apply]

/-- Based at the origin, the geodesic lines are exactly the radial ones: the Moebius isometry
centred at the origin is the identity. -/
lemma geodesicLine_toPoincare_zero (u : Circle) :
    geodesicLine (Complex.UnitDisc.toPoincare 0) u = radialGeodesic u := by
  funext t
  rw [geodesicLine_def, toUnitDisc_toPoincare, IsometryEquiv.symm_apply_eq]
  simp

/-- **The geodesic lines are unit-speed geodesic lines**: `geodesicLine a u` is an isometric
embedding of the real line into the Poincaré disc. -/
theorem isometry_geodesicLine (a : PoincareDisc) (u : Circle) : Isometry (geodesicLine a u) :=
  Isometry.of_dist_eq fun s t => by
    rw [geodesicLine_def, geodesicLine_def, IsometryEquiv.dist_eq,
      (isometry_radialGeodesic u).dist_eq]

/-- The geodesic line through `a` is at hyperbolic distance `|t|` from `a` at time `t`. -/
lemma dist_geodesicLine_self (a : PoincareDisc) (u : Circle) (t : ℝ) :
    dist (geodesicLine a u t) a = |t| := by
  have h := (isometry_geodesicLine a u).dist_eq t 0
  rwa [geodesicLine_zero, Real.dist_eq, sub_zero] at h

/-! ### The classification of the geodesic lines -/

/-- **Every unit-speed geodesic line of the Poincaré disc is a `geodesicLine`.** An isometric
embedding `γ` of the real line is `geodesicLine (γ 0) u` for one and only one direction
`u : Circle`.

Conjugating by the Moebius isometry that carries `γ 0` to the origin turns `γ` into a geodesic
line through the origin, where `TauCeti.PoincareDisc.existsUnique_eq_radialGeodesic` applies. -/
theorem existsUnique_eq_geodesicLine {γ : ℝ → PoincareDisc} (hγ : Isometry γ) :
    ∃! u : Circle, γ = geodesicLine (γ 0) u := by
  have hcomp : Isometry fun t => unitDiscMoebiusIsometryEquiv (toUnitDisc (γ 0)) (γ t) :=
    (unitDiscMoebiusIsometryEquiv (toUnitDisc (γ 0))).isometry.comp hγ
  have h0 : unitDiscMoebiusIsometryEquiv (toUnitDisc (γ 0)) (γ 0) =
      Complex.UnitDisc.toPoincare 0 := by
    rw [unitDiscMoebiusIsometryEquiv_apply, unitDiscMoebius_self]
  obtain ⟨u, hu, huniq⟩ := existsUnique_eq_radialGeodesic hcomp h0
  refine ⟨u, funext fun t => ?_, fun v hv => huniq v (funext fun t => ?_)⟩
  · have ht : unitDiscMoebiusIsometryEquiv (toUnitDisc (γ 0)) (γ t) = radialGeodesic u t :=
      congrFun hu t
    rw [geodesicLine_def, ← ht, IsometryEquiv.symm_apply_apply]
  · rw [show γ t = geodesicLine (γ 0) v t from congrFun hv t,
      unitDiscMoebiusIsometryEquiv_geodesicLine]

/-- Distinct directions give distinct geodesic lines through a common point. -/
theorem geodesicLine_injective (a : PoincareDisc) : Function.Injective (geodesicLine a) := by
  intro u v huv
  refine radialGeodesic_injective (funext fun t => ?_)
  have h := congrArg (unitDiscMoebiusIsometryEquiv (toUnitDisc a)) (congrFun huv t)
  rwa [unitDiscMoebiusIsometryEquiv_geodesicLine,
    unitDiscMoebiusIsometryEquiv_geodesicLine] at h

/-- **Two distinct points determine a direction.** For `z ≠ w` there is exactly one direction
`u : Circle` for which the geodesic line through `z` in direction `u` reaches `w`, and it reaches
it at time `dist z w`.

Existence is the geodesic-space property
`TauCeti.PoincareDisc.exists_isometry_apply_zero_apply_dist` read through the classification.
Uniqueness is immediate once both lines are straightened to the origin: `radialGeodesic u t` is
the disc point `u * Real.tanh t`, and `Real.tanh (dist z w) ≠ 0` because `z ≠ w`. -/
theorem existsUnique_geodesicLine_dist_eq {z w : PoincareDisc} (h : z ≠ w) :
    ∃! u : Circle, geodesicLine z u (dist z w) = w := by
  have hpos : 0 < dist z w := dist_pos.mpr h
  have htanh : ((Real.tanh (dist z w) : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr fun hzero => hpos.ne' ?_
    exact Real.tanh_injective (hzero.trans Real.tanh_zero.symm)
  obtain ⟨γ, hγ, h0, hd⟩ := exists_isometry_apply_zero_apply_dist z w
  obtain ⟨u, hu, -⟩ := existsUnique_eq_geodesicLine hγ
  rw [h0] at hu
  have hueq : geodesicLine z u (dist z w) = w := by rw [← congrFun hu (dist z w)]; exact hd
  refine ⟨u, hueq, fun v hv => ?_⟩
  -- Straightening to the origin turns the two hypotheses into one equation between radial
  -- geodesics, which reads `v * tanh (dist z w) = u * tanh (dist z w)` on disc points.
  have key : ∀ p : Circle, geodesicLine z p (dist z w) = w →
      radialGeodesic p (dist z w) = unitDiscMoebiusIsometryEquiv (toUnitDisc z) w := by
    intro p hp
    rw [← unitDiscMoebiusIsometryEquiv_geodesicLine z p (dist z w), hp]
  have hvu := (key v hv).trans (key u hueq).symm
  refine Circle.ext (mul_right_cancel₀ htanh ?_)
  have hcoe := congrArg
    (fun q : PoincareDisc => ((toUnitDisc q : Complex.UnitDisc) : ℂ)) hvu
  simpa only [coe_radialGeodesic] using hcoe

/-! ### Hyperbolic lines as sets -/

/-- A subset of the Poincaré disc is a **hyperbolic line** when it is the trace of a unit-speed
geodesic line, that is, of the form `Set.range (TauCeti.PoincareDisc.geodesicLine a u)`. -/
def IsGeodesicLine (L : Set PoincareDisc) : Prop :=
  ∃ (a : PoincareDisc) (u : Circle), L = range (geodesicLine a u)

/-- The trace of a geodesic line is a hyperbolic line. -/
theorem isGeodesicLine_range_geodesicLine (a : PoincareDisc) (u : Circle) :
    IsGeodesicLine (range (geodesicLine a u)) :=
  ⟨a, u, rfl⟩

/-- A geodesic line through `a` passes through `a`. -/
lemma mem_range_geodesicLine_self (a : PoincareDisc) (u : Circle) :
    a ∈ range (geodesicLine a u) :=
  ⟨0, geodesicLine_zero a u⟩

/-- Hyperbolic lines are nonempty. -/
theorem IsGeodesicLine.nonempty {L : Set PoincareDisc} (hL : IsGeodesicLine L) : L.Nonempty := by
  obtain ⟨a, u, rfl⟩ := hL
  exact ⟨a, mem_range_geodesicLine_self a u⟩

/-- **Hyperbolic lines are exactly the ranges of the unit-speed geodesic lines.** The forward
direction is `TauCeti.PoincareDisc.isometry_geodesicLine`, the reverse the classification
`TauCeti.PoincareDisc.existsUnique_eq_geodesicLine`. -/
theorem isGeodesicLine_iff_exists_isometry {L : Set PoincareDisc} :
    IsGeodesicLine L ↔ ∃ γ : ℝ → PoincareDisc, Isometry γ ∧ L = range γ := by
  constructor
  · rintro ⟨a, u, rfl⟩
    exact ⟨geodesicLine a u, isometry_geodesicLine a u, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨u, hu, -⟩ := existsUnique_eq_geodesicLine hγ
    exact ⟨γ 0, u, congrArg range hu⟩

/-- **A hyperbolic line may be based at any of its points.** Shifting time turns a geodesic line
into one that starts at a prescribed point of its trace, and by the classification the shifted line
is again a `geodesicLine`. -/
theorem IsGeodesicLine.exists_eq_range_geodesicLine_of_mem {L : Set PoincareDisc}
    (hL : IsGeodesicLine L) {z : PoincareDisc} (hz : z ∈ L) :
    ∃ u : Circle, L = range (geodesicLine z u) := by
  obtain ⟨a, u, rfl⟩ := hL
  obtain ⟨t₀, ht₀⟩ := hz
  have hshift : Isometry fun t : ℝ => geodesicLine a u (t + t₀) :=
    Isometry.of_dist_eq fun s t => by
      rw [(isometry_geodesicLine a u).dist_eq, Real.dist_eq, Real.dist_eq]
      congr 1
      ring
  obtain ⟨v, hv, -⟩ := existsUnique_eq_geodesicLine hshift
  rw [zero_add, ht₀] at hv
  refine ⟨v, ?_⟩
  rw [← hv]
  ext p
  simp only [mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t - t₀, by simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t + t₀, rfl⟩

/-- **A hyperbolic line may be run backwards.** For every direction `u` there is a direction `v`
at the same base point whose geodesic line is the time reversal of the one in direction `u`; in
particular the two have the same trace. -/
theorem exists_geodesicLine_neg (a : PoincareDisc) (u : Circle) :
    ∃ v : Circle, (∀ t : ℝ, geodesicLine a v t = geodesicLine a u (-t)) ∧
      range (geodesicLine a v) = range (geodesicLine a u) := by
  have hneg : Isometry fun t : ℝ => geodesicLine a u (-t) :=
    Isometry.of_dist_eq fun s t => by
      rw [(isometry_geodesicLine a u).dist_eq, Real.dist_eq, Real.dist_eq, ← abs_neg]
      congr 1
      ring
  obtain ⟨v, hv, -⟩ := existsUnique_eq_geodesicLine hneg
  simp only [neg_zero, geodesicLine_zero] at hv
  have hpt : ∀ t : ℝ, geodesicLine a v t = geodesicLine a u (-t) := fun t => (congrFun hv t).symm
  refine ⟨v, hpt, ?_⟩
  ext p
  simp only [mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-t, (hpt t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by rw [hpt (-t), neg_neg]⟩

/-- **The incidence theorem for the Poincaré disc.** Two distinct points lie on exactly one
hyperbolic line.

Any line through `z` may be based at `z` (`IsGeodesicLine.exists_eq_range_geodesicLine_of_mem`)
and, if it meets `w` at a negative time, run backwards (`exists_geodesicLine_neg`); after those
two normalisations it reaches `w` at time `dist z w`, where
`TauCeti.PoincareDisc.existsUnique_geodesicLine_dist_eq` fixes its direction. -/
theorem existsUnique_isGeodesicLine_mem {z w : PoincareDisc} (h : z ≠ w) :
    ∃! L : Set PoincareDisc, IsGeodesicLine L ∧ z ∈ L ∧ w ∈ L := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_geodesicLine_dist_eq h
  refine ⟨range (geodesicLine z u), ⟨isGeodesicLine_range_geodesicLine z u,
    mem_range_geodesicLine_self z u, ⟨dist z w, hu⟩⟩, ?_⟩
  rintro L ⟨hL, hzL, hwL⟩
  obtain ⟨v, hLv⟩ := hL.exists_eq_range_geodesicLine_of_mem hzL
  subst hLv
  obtain ⟨s, hs⟩ := hwL
  -- The time at which the line meets `w` is `± dist z w`, because the line is unit-speed.
  have habs : |s| = dist z w := by
    have hd := dist_geodesicLine_self z v s
    rw [hs] at hd
    rw [← hd, dist_comm]
  rcases (abs_eq dist_nonneg).mp habs with hsd | hsd
  · rw [huniq v (by rw [← hsd]; exact hs)]
  · obtain ⟨v', hpt, hrange⟩ := exists_geodesicLine_neg z v
    have hv' : geodesicLine z v' (dist z w) = w := by rw [hpt, ← hsd]; exact hs
    rw [← hrange, huniq v' hv']

end PoincareDisc

end TauCeti
