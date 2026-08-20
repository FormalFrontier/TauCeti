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

* `TauCeti.normalizeToSphere`: radial projection of a continuous nowhere-zero map to the unit
  sphere.
* `Path.homotopic_of_normalize_segment_ne_zero`: radial projection of a straight-line
  homotopy between sphere loops.
* `TauCeti.contractibleSpace_sphere_compl_singleton`: the sphere minus one point is contractible.
* `TauCeti.nullhomotopic_inclusion_sphere_compl_singleton`: the inclusion of the sphere minus a
  point into the sphere is null-homotopic.
* `TauCeti.homotopic_refl_of_notMem_range_sphere`: a loop on the unit sphere omitting a point of
  the sphere is null-homotopic.

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

/-- Radial projection sends a continuous nowhere-zero map into a real normed space continuously
to its unit sphere. -/
@[expose] noncomputable def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨normalize (f y), mem_sphere_zero_iff_norm.mpr (norm_normalize (h0 y))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    -- `normalize` is definitionally inverse-norm scalar multiplication; exposing that formula
    -- lets the standard continuity combinators apply.
    change Continuous fun y => ‖f y‖⁻¹ • f y
    exact ((continuous_norm.comp hf).inv₀
      (fun y => norm_ne_zero_iff.mpr (h0 y))).smul hf

/-- The underlying vector of `normalizeToSphere f hf h0 y` is the normalization of `f y`. -/
@[simp]
theorem normalizeToSphere_apply {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) (y : Y) :
    ((normalizeToSphere f hf h0 y : sphere (0 : E) 1) : E) = normalize (f y) := rfl

private theorem smul_sub_smul_ne_zero_of_ne {x p : E} (hx : ‖x‖ = 1) (hp : ‖p‖ = 1)
    (hxp : x ≠ p) (u : ℝ) : (1 - u) • x - u • p ≠ 0 := by
  intro h
  have h' : (1 - u) • x = u • p := by rwa [sub_eq_zero] at h
  have habs : |1 - u| = |u| := by
    have hnorm := congrArg norm h'
    rw [norm_smul, norm_smul, hx, hp, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    exact hnorm
  have hu : u = 1 / 2 := by
    have hsquare := congrArg (fun r : ℝ => r ^ 2) habs
    simp only [sq_abs] at hsquare
    nlinarith
  refine hxp ?_
  have h2 : (2 : ℝ) • ((1 - u) • x) = (2 : ℝ) • (u • p) := by rw [h']
  rw [smul_smul, smul_smul, hu] at h2
  norm_num at h2
  exact h2

private noncomputable def normalizeSegmentToSphere {Y : Type*} [TopologicalSpace Y]
    (f g : Y → E) (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ z : I × Y, (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2 ≠ 0) :
    C(I × Y, sphere (0 : E) 1) := by
  have hu : Continuous fun z : I × Y => ((z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact normalizeToSphere
    (fun z => (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2)
    (((continuous_const.sub hu).smul (hf.comp continuous_snd)).add
      (hu.smul (hg.comp continuous_snd))) h0

/-- A loop in the unit sphere is homotopic to the radial projection of a continuous comparison
loop when every point of their pointwise straight-line homotopy avoids the origin. -/
theorem _root_.Path.homotopic_of_normalize_segment_ne_zero {x : sphere (0 : E) 1} (γ γ' : Path x x)
    (f : I → E) (hf : Continuous f)
    (hγ' : ∀ t, ((γ' t : sphere (0 : E) 1) : E) = normalize (f t))
    (hf_zero : f 0 = (x : E)) (hf_one : f 1 = (x : E))
    (h : ∀ z : I × I,
      (1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E) +
        (z.1 : ℝ) • f z.2 ≠ 0) : γ.Homotopic γ' := by
  let K := normalizeSegmentToSphere
    (fun t => ((γ t : sphere (0 : E) 1) : E)) f
    (continuous_subtype_val.comp γ.continuous) hf h
  have hxnorm : ‖((x : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  refine Path.homotopic_of_continuous_square K K.continuous ?_ ?_ ?_ ?_
  · intro s
    apply Subtype.ext
    simpa [K, normalizeSegmentToSphere, normalizeToSphere] using
      normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (γ s).2)
  · intro s
    apply Subtype.ext
    simpa [K, normalizeSegmentToSphere, normalizeToSphere] using (hγ' s).symm
  · intro u
    apply Subtype.ext
    simpa [K, normalizeSegmentToSphere, normalizeToSphere, γ.source, hf_zero, ← add_smul] using
      normalize_eq_self_of_norm_eq_one hxnorm
  · intro u
    apply Subtype.ext
    simpa [K, normalizeSegmentToSphere, normalizeToSphere, γ.target, hf_one, ← add_smul] using
      normalize_eq_self_of_norm_eq_one hxnorm

private theorem normalize_smul_sub_smul_ne_of_ne {x p : E} (hx : ‖x‖ = 1) (hp : ‖p‖ = 1)
    (hxp : x ≠ p) (u : I) : normalize ((1 - (u : ℝ)) • x - (u : ℝ) • p) ≠ p := by
  let v := (1 - (u : ℝ)) • x - (u : ℝ) • p
  have hv0 : v ≠ 0 := smul_sub_smul_ne_zero_of_ne hx hp hxp u
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  intro hvp
  have hscale : ‖v‖ • p = v := by
    rw [← hvp]
    exact norm_smul_normalize v
  have heq : (‖v‖ + (u : ℝ)) • p = (1 - (u : ℝ)) • x := by
    rw [add_smul, hscale]
    simp only [v]
    abel
  have hleft : 0 < ‖v‖ + (u : ℝ) := add_pos_of_pos_of_nonneg hvnorm u.2.1
  have hright : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.2.2
  have hcoeff := congrArg norm heq
  rw [norm_smul, norm_smul, hp, hx, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hleft, abs_of_nonneg hright] at hcoeff
  have hright' : 0 < 1 - (u : ℝ) := hcoeff ▸ hleft
  rw [hcoeff] at heq
  have hinv := congrArg (fun y : E => (1 - (u : ℝ))⁻¹ • y) heq
  simp only [smul_smul, inv_mul_cancel₀ hright'.ne', one_smul] at hinv
  exact hxp hinv.symm

/-- **The unit sphere minus one point is contractible.** Radial projection of the segment towards
the antipode of the deleted point gives a contraction that stays inside the punctured sphere. -/
theorem contractibleSpace_sphere_compl_singleton (p : sphere (0 : E) 1) :
    ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) := by
  refine (contractible_iff_id_nullhomotopic _).mpr ?_
  have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  let inclusion : ({p}ᶜ : Set (sphere (0 : E) 1)) → E := fun q =>
    ((q : sphere (0 : E) 1) : E)
  have hinclusion : Continuous inclusion := continuous_subtype_val.comp continuous_subtype_val
  have hsegment : ∀ z : I × ({p}ᶜ : Set (sphere (0 : E) 1)),
      (1 - (z.1 : ℝ)) • inclusion z.2 + (z.1 : ℝ) • (-(p : E)) ≠ 0 := by
    rintro ⟨u, q⟩
    simpa only [inclusion, smul_neg, sub_eq_add_neg] using smul_sub_smul_ne_zero_of_ne
      (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2) hp
      (fun hq => q.2 (Set.mem_singleton_iff.mpr (Subtype.ext hq))) u
  let G := normalizeSegmentToSphere inclusion (fun _ => -(p : E))
    hinclusion continuous_const hsegment
  have hGne : ∀ z, G z ≠ p := by
    rintro ⟨u, q⟩ hG
    exact normalize_smul_sub_smul_ne_of_ne
      (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2) hp
      (fun hq => q.2 (Set.mem_singleton_iff.mpr (Subtype.ext hq))) u
      (by simpa [G, normalizeSegmentToSphere, normalizeToSphere, inclusion, smul_neg,
        sub_eq_add_neg] using congrArg Subtype.val hG)
  let antipode : sphere (0 : E) 1 := ⟨-(p : E), by simp⟩
  have hneg : antipode ≠ p := by
    intro h
    have hval : -(p : E) = (p : E) := by
      simpa only [antipode] using congrArg Subtype.val h
    have htwo : (2 : ℝ) • (p : E) = 0 := by
      calc
        (2 : ℝ) • (p : E) = (p : E) + (p : E) := two_smul ℝ (p : E)
        _ = -(p : E) + (p : E) := congrArg (fun y : E => y + (p : E)) hval.symm
        _ = 0 := neg_add_cancel (p : E)
    have hpzero : (p : E) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [hpzero, norm_zero] at hp
    norm_num at hp
  refine ⟨⟨antipode, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]⟩, ⟨?_⟩⟩
  exact
    { toFun := fun z => ⟨G z,
        by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hGne z⟩
      continuous_toFun := G.continuous.subtype_mk fun z => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hGne z
      map_zero_left := fun q => by
        have hraw : ((G (0, q) : sphere (0 : E) 1) : E) =
            ((q : sphere (0 : E) 1) : E) := by
          simpa [G, normalizeSegmentToSphere, normalizeToSphere, inclusion] using
            normalize_eq_self_of_norm_eq_one
              (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2)
        exact Subtype.ext (Subtype.ext hraw)
      map_one_left := fun q => by
        have hraw : ((G (1, q) : sphere (0 : E) 1) : E) = -(p : E) := by
          simpa [G, normalizeSegmentToSphere, normalizeToSphere, inclusion, normalize_neg] using
            congrArg Neg.neg (normalize_eq_self_of_norm_eq_one hp)
        exact Subtype.ext (Subtype.ext hraw) }

/-- **The inclusion of the unit sphere minus one point into the sphere is null-homotopic.** -/
theorem nullhomotopic_inclusion_sphere_compl_singleton (p : sphere (0 : E) 1) :
    (ContinuousMap.mk (Subtype.val : ({p}ᶜ : Set (sphere (0 : E) 1)) → sphere (0 : E) 1)
      continuous_subtype_val).Nullhomotopic := by
  let _ : ContractibleSpace ({p}ᶜ : Set (sphere (0 : E) 1)) :=
    contractibleSpace_sphere_compl_singleton p
  simpa using (id_nullhomotopic ({p}ᶜ : Set (sphere (0 : E) 1))).comp_right
    (ContinuousMap.mk (Subtype.val : ({p}ᶜ : Set (sphere (0 : E) 1)) → sphere (0 : E) 1)
      continuous_subtype_val)

/-- **A loop on the unit sphere that omits a point of the sphere is null-homotopic.** The loop
runs in the punctured sphere, whose inclusion into the sphere is null-homotopic. -/
theorem homotopic_refl_of_notMem_range_sphere {x : sphere (0 : E) 1} (γ : Path x x)
    {p : sphere (0 : E) 1} (hp : p ∉ Set.range γ) : γ.Homotopic (Path.refl x) := by
  have hmem : ∀ t, γ t ∈ ({p}ᶜ : Set (sphere (0 : E) 1)) := fun t hmem =>
    hp ⟨t, (Set.mem_singleton_iff.mp hmem).symm ▸ rfl⟩
  exact Path.Homotopic.refl_of_forall_mem_of_nullhomotopic
    (nullhomotopic_inclusion_sphere_compl_singleton p) γ hmem

end TauCeti

end
