/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.Homotopy.Path

/-!
# The punctured unit sphere

Removing a point `p` from the unit sphere of a real normed space leaves a set that can be swept
onto the antipode `-p`: for `x ≠ p` on the sphere the straight segment from `x` to `-p` never
meets the origin, so normalising it gives a contraction of the punctured sphere inside the
sphere. Consequently the inclusion of the punctured sphere into the sphere is null-homotopic, and
a loop on the sphere that misses even a single point is null-homotopic.

This is the easy half of the computation of `π₁(Sⁿ)`: the work left over is to homotope an
arbitrary loop off a point, which is done in
`TauCeti.AlgebraicTopology.Sphere.SimplyConnected`.

## Main declarations

* `TauCeti.sub_smul_ne_zero_of_norm_eq_one`: the segment from `x` to the antipode of `p` avoids
  the origin, for distinct points `x`, `p` of the unit sphere.
* `TauCeti.nullhomotopic_inclusion_sphere_compl`: the inclusion of the sphere minus a point into
  the sphere is null-homotopic.
* `TauCeti.homotopic_refl_of_notMem_range`: a loop on the unit sphere omitting a point of the
  sphere is null-homotopic.

## References

This serves the `π₁(RPⁿ)` line of `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13,
whose only missing input is the simple connectivity of the covering sphere. The contraction of a
punctured sphere onto the antipode of the puncture is the standard one, as in Hatcher,
*Algebraic Topology*, Section 1.1. No Mathlib code is vendored.
-/

public section

noncomputable section

open Metric NormedSpace
open scoped unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For distinct points `x` and `p` of the unit sphere, the segment running from `x` to the
antipode `-p` misses the origin: a vanishing convex combination would force the two coefficients
to agree, hence `x = p`. -/
theorem sub_smul_ne_zero_of_norm_eq_one {x p : E} (hx : ‖x‖ = 1) (hp : ‖p‖ = 1) (hxp : x ≠ p)
    {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) : (1 - u) • x - u • p ≠ 0 := by
  intro h
  have h' : (1 - u) • x = u • p := by rwa [sub_eq_zero] at h
  have hcoeff : 1 - u = u := by
    have hnorm := congrArg norm h'
    rw [norm_smul, norm_smul, hx, hp, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg hu₀] at hnorm
    exact hnorm
  have hu : u = 1 / 2 := by linarith
  refine hxp ?_
  have h2 : (2 : ℝ) • ((1 - u) • x) = (2 : ℝ) • (u • p) := by rw [h']
  rw [smul_smul, smul_smul, hu] at h2
  norm_num at h2
  exact h2

/-- **The inclusion of the punctured unit sphere into the unit sphere is null-homotopic.**
Radial projection of the segment towards `-p` sweeps every point other than `p` to the
antipode `-p`. -/
theorem nullhomotopic_inclusion_sphere_compl (p : sphere (0 : E) 1) :
    (ContinuousMap.mk (Subtype.val : ({p}ᶜ : Set (sphere (0 : E) 1)) → sphere (0 : E) 1)
      continuous_subtype_val).Nullhomotopic := by
  have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  set g : I × ({p}ᶜ : Set (sphere (0 : E) 1)) → E := fun z =>
    (1 - (z.1 : ℝ)) • ((z.2 : sphere (0 : E) 1) : E) - (z.1 : ℝ) • (p : E) with hg
  have hgcont : Continuous g := by
    have h1 : Continuous fun z : I × ({p}ᶜ : Set (sphere (0 : E) 1)) =>
        ((z.2 : sphere (0 : E) 1) : E) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have h2 : Continuous fun z : I × ({p}ᶜ : Set (sphere (0 : E) 1)) => ((z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub h2).smul h1).sub (h2.smul continuous_const)
  have hgne : ∀ z, g z ≠ 0 := by
    rintro ⟨u, q⟩
    refine sub_smul_ne_zero_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2) hp ?_ u.2.1 u.2.2
    intro hq
    exact q.2 (Set.mem_singleton_iff.mpr (Subtype.ext hq))
  refine ⟨⟨-(p : E), by simp⟩, ⟨?_⟩⟩
  exact
    { toFun := fun z => ⟨normalize (g z), mem_sphere_zero_iff_norm.mpr (norm_normalize (hgne z))⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        change Continuous fun z => ‖g z‖⁻¹ • g z
        exact ((continuous_norm.comp hgcont).inv₀
          (fun z => norm_ne_zero_iff.mpr (hgne z))).smul hgcont
      map_zero_left := fun q => by
        refine Subtype.ext ?_
        change NormedSpace.normalize (g (0, q)) = ((q : sphere (0 : E) 1) : E)
        have hgq : g (0, q) = ((q : sphere (0 : E) 1) : E) := by simp [hg]
        rw [hgq]
        exact normalize_eq_self_of_norm_eq_one
          (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2)
      map_one_left := fun q => by
        refine Subtype.ext ?_
        change NormedSpace.normalize (g (1, q)) = -(p : E)
        have hgq : g (1, q) = -(p : E) := by simp [hg]
        rw [hgq, normalize_neg, normalize_eq_self_of_norm_eq_one hp] }

/-- **A loop on the unit sphere that omits a point of the sphere is null-homotopic.** The loop
runs in the punctured sphere, whose inclusion into the sphere is null-homotopic. -/
theorem homotopic_refl_of_notMem_range {x : sphere (0 : E) 1} (γ : Path x x)
    {p : sphere (0 : E) 1} (hp : p ∉ Set.range γ) : γ.Homotopic (Path.refl x) := by
  have hmem : ∀ t, γ t ∈ ({p}ᶜ : Set (sphere (0 : E) 1)) := fun t hmem =>
    hp ⟨t, (Set.mem_singleton_iff.mp hmem).symm ▸ rfl⟩
  have hx : x ∈ ({p}ᶜ : Set (sphere (0 : E) 1)) := γ.source ▸ hmem 0
  have key := Path.Homotopic.map_nullhomotopic_of_nullhomotopic
    (nullhomotopic_inclusion_sphere_compl p)
    (Path.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) γ hmem)
  rwa [Path.map_codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) γ hmem] at key

end TauCeti

end
