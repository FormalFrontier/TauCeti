/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Transporting an `Lp` element along an equality of measures

Equal measures give *equal* (not merely isomorphic) `Lp` types, so an element of `Lp E p μ` can be
moved to `Lp E p ν` by `cast` whenever `μ = ν`. The cast is the identity on representatives, which
is what `TauCeti.coeFn_cast_lp` records.

This is the bookkeeping a statement needs when a space is *defined* with one description of its
measure and *used* with another, for example a basis of `L²(γ)` fed to
`TauCeti.weightL2Isometry`, whose domain is spelled `L²(volume.withDensity …)`.

Bundling that cast as a linear isometric equivalence, `TauCeti.castLpₗᵢ`, is what lets an equality
of measures be *composed* with other isometries — for instance to feed
`HilbertBasis.mapₗᵢ`, which needs a genuine `≃ₗᵢ` and not a `cast`.

## Main statements

* `TauCeti.coeFn_cast_lp`: the cast does not move representatives.
* `TauCeti.castLpₗᵢ`: the cast as a linear isometric equivalence.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

/-- **Transporting an `Lp` element along an equality of measures does not move its
representative.** The `cast` is along the equality of types `↥(Lp E p μ) = ↥(Lp E p ν)` induced by
`μ = ν`, so it acts as the identity on functions. -/
@[simp]
theorem coeFn_cast_lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ ν : Measure α} (h : μ = ν) (f : Lp E p μ) (x : α) :
    ((cast (congrArg (fun m : Measure α => (Lp E p m : Type _)) h) f : Lp E p ν) : α → E) x
      = (f : α → E) x := by
  subst h
  rfl

/-- **Equal measures give isometrically identical `Lp` spaces.** This is `cast` along the equality
of types `↥(Lp E p μ) = ↥(Lp E p ν)`, packaged as a linear isometric equivalence so that it can be
composed with other isometries; `TauCeti.coeFn_castLpₗᵢ` records that it still does not move
representatives. -/
noncomputable def castLpₗᵢ {α E 𝕜 : Type*} [MeasurableSpace α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    (h : μ = ν) : Lp E p μ ≃ₗᵢ[𝕜] Lp E p ν :=
  h.rec (motive := fun m _ => Lp E p μ ≃ₗᵢ[𝕜] Lp E p m) (LinearIsometryEquiv.refl 𝕜 _)

/-- **The isometric cast is the transport `cast`.** This is what lets a consumer rewrite the
transported vector itself, rather than only its representative, so no extensionality step is needed
to get at it. -/
@[simp]
theorem castLpₗᵢ_apply {α E 𝕜 : Type*} [MeasurableSpace α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    (h : μ = ν) (f : Lp E p μ) :
    castLpₗᵢ (𝕜 := 𝕜) h f = cast (congrArg (fun m : Measure α => (Lp E p m : Type _)) h) f := by
  subst h
  rfl

/-- **The isometric cast does not move representatives.** This is not itself a `simp` lemma:
`TauCeti.castLpₗᵢ_apply` followed by `TauCeti.coeFn_cast_lp` already reduces its left-hand side,
so `simp` reaches the same normal form and marking it too would only duplicate them. -/
theorem coeFn_castLpₗᵢ {α E 𝕜 : Type*} [MeasurableSpace α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    (h : μ = ν) (f : Lp E p μ) (x : α) :
    ((castLpₗᵢ (𝕜 := 𝕜) h f : Lp E p ν) : α → E) x = (f : α → E) x := by
  subst h
  rfl

/-- The inverse of the isometric cast is the cast along the reversed equality. -/
@[simp]
theorem castLpₗᵢ_symm {α E 𝕜 : Type*} [MeasurableSpace α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    (h : μ = ν) : (castLpₗᵢ (𝕜 := 𝕜) (E := E) (p := p) h).symm = castLpₗᵢ h.symm := by
  subst h
  rfl

end TauCeti
