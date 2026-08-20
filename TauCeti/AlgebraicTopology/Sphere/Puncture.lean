/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Analysis.Normed.Module.Normalize
public import TauCeti.Topology.Homotopy.Path
-- Private: these supply the affine homotopy and the antipode inequality used in proofs below.
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Topology.Homotopy.Affine

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

* `TauCeti.homotopic_of_normalize_segment_ne_zero`: radial projection of a straight-line
  homotopy between sphere paths.
* `TauCeti.contractibleSpace_sphere_compl_singleton`: the sphere minus one point is contractible.
* `TauCeti.nullhomotopic_inclusion_sphere_compl_singleton`: the inclusion of the sphere minus a
  point into the sphere is null-homotopic.
* `TauCeti.homotopic_refl_of_notMem_range`: a loop on the unit sphere omitting a point of
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

private theorem smul_sub_smul_ne_zero_of_ne {x p : E} (hx : ‖x‖ = 1) (hp : ‖p‖ = 1)
    (hxp : x ≠ p) (u : ℝ) : (1 - u) • x - u • p ≠ 0 := by
  intro h
  have h' : (1 - u) • x = u • p := by rwa [sub_eq_zero] at h
  have habs : |1 - u| = |u| := by
    simpa [norm_smul, hx, hp, Real.norm_eq_abs] using congrArg norm h'
  have hu : u = 1 / 2 := by
    have hsquare := congrArg (fun r : ℝ => r ^ 2) habs
    simp only [sq_abs] at hsquare
    nlinarith
  refine hxp ?_
  have h2 : (2 : ℝ) • ((1 - u) • x) = (2 : ℝ) • (u • p) := by rw [h']
  rw [smul_smul, smul_smul, hu] at h2
  norm_num at h2
  exact h2

/-- Radial projection of the straight-line homotopy from `f` to `g`, available whenever that
segment never meets the origin. -/
private noncomputable def normalizeSegmentToSphere {Y : Type*} [TopologicalSpace Y]
    (f g : Y → E) (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ z : I × Y, (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2 ≠ 0) :
    C(I × Y, sphere (0 : E) 1) :=
  let F : C(Y, E) := ⟨f, hf⟩
  let G : C(Y, E) := ⟨g, hg⟩
  normalizeToSphere (ContinuousMap.Homotopy.affine F G)
    (ContinuousMap.Homotopy.affine F G).continuous fun z => by
      have hline : (ContinuousMap.Homotopy.affine F G) z =
          (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2 := by
        rw [ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module]
        rfl
      rw [hline]
      exact h0 z

section Segment

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → E} {hf : Continuous f} {hg : Continuous g}
  {h0 : ∀ z : I × Y, (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • g z.2 ≠ 0}

/-- The underlying vector of the segment homotopy at `(u, y)` is the normalization of the point
of the segment from `f y` to `g y` at time `u`. -/
private theorem coe_normalizeSegmentToSphere_apply (u : I) (y : Y) :
    ((normalizeSegmentToSphere f g hf hg h0 (u, y) : sphere (0 : E) 1) : E) =
      normalize ((1 - (u : ℝ)) • f y + (u : ℝ) • g y) := by
  rw [normalizeSegmentToSphere, coe_normalizeToSphere_apply,
    ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module]
  rfl

/-- The segment homotopy starts at the radial projection of `f`. -/
private theorem coe_normalizeSegmentToSphere_zero_left (y : Y) :
    ((normalizeSegmentToSphere f g hf hg h0 (0, y) : sphere (0 : E) 1) : E) = normalize (f y) := by
  rw [coe_normalizeSegmentToSphere_apply]
  simp

/-- The segment homotopy ends at the radial projection of `g`. -/
private theorem coe_normalizeSegmentToSphere_one_left (y : Y) :
    ((normalizeSegmentToSphere f g hf hg h0 (1, y) : sphere (0 : E) 1) : E) = normalize (g y) := by
  rw [coe_normalizeSegmentToSphere_apply]
  simp

/-- Where `f` and `g` agree at a unit vector the segment homotopy stays at that vector. -/
private theorem coe_normalizeSegmentToSphere_apply_of_eq {y : Y} {v : E} (hfy : f y = v)
    (hgy : g y = v) (hv : ‖v‖ = 1) (u : I) :
    ((normalizeSegmentToSphere f g hf hg h0 (u, y) : sphere (0 : E) 1) : E) = v := by
  rw [coe_normalizeSegmentToSphere_apply, hfy, hgy, ← add_smul]
  simpa using normalize_eq_self_of_norm_eq_one hv

end Segment

/-- A path in the unit sphere is homotopic to the radial projection of a continuous comparison
map when every point of their pointwise straight-line homotopy avoids the origin and the comparison
map itself takes the source and target values at the two endpoints. -/
theorem homotopic_of_normalize_segment_ne_zero {a b : sphere (0 : E) 1} (γ γ' : Path a b)
    (f : I → E) (hf : Continuous f)
    (hγ' : ∀ t, ((γ' t : sphere (0 : E) 1) : E) = normalize (f t))
    (hf_zero : f 0 = (a : E)) (hf_one : f 1 = (b : E))
    (h : ∀ z : I × I,
      (1 - (z.1 : ℝ)) • ((γ z.2 : sphere (0 : E) 1) : E) +
        (z.1 : ℝ) • f z.2 ≠ 0) : γ.Homotopic γ' := by
  have hanorm : ‖((a : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp a.2
  have hbnorm : ‖((b : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp b.2
  refine Path.homotopic_of_continuous_square
    (normalizeSegmentToSphere (fun t => ((γ t : sphere (0 : E) 1) : E)) f
      (continuous_subtype_val.comp γ.continuous) hf h)
    (ContinuousMap.continuous _) ?_ ?_ ?_ ?_
  · intro s
    refine Subtype.ext ?_
    rw [coe_normalizeSegmentToSphere_zero_left]
    exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (γ s).2)
  · intro s
    refine Subtype.ext ?_
    rw [coe_normalizeSegmentToSphere_one_left]
    exact (hγ' s).symm
  · intro u
    refine Subtype.ext (coe_normalizeSegmentToSphere_apply_of_eq (y := (0 : I)) ?_ hf_zero hanorm u)
    exact congrArg Subtype.val γ.source
  · intro u
    refine Subtype.ext (coe_normalizeSegmentToSphere_apply_of_eq (y := (1 : I)) ?_ hf_one hbnorm u)
    exact congrArg Subtype.val γ.target

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
  have hcoeff : ‖v‖ + (u : ℝ) = 1 - (u : ℝ) := by
    simpa [norm_smul, hp, hx, Real.norm_eq_abs, abs_of_pos hleft, abs_of_nonneg hright] using
      congrArg norm heq
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
  -- The contraction, presented by the value of its underlying vector so that no later step has
  -- to unfold `normalizeSegmentToSphere`.
  obtain ⟨G, hGcont, hGval⟩ :
      ∃ G : I × ({p}ᶜ : Set (sphere (0 : E) 1)) → sphere (0 : E) 1, Continuous G ∧
        ∀ (u : I) (q : ({p}ᶜ : Set (sphere (0 : E) 1))),
          ((G (u, q) : sphere (0 : E) 1) : E) =
            normalize ((1 - (u : ℝ)) • ((q : sphere (0 : E) 1) : E) - (u : ℝ) • (p : E)) :=
    ⟨normalizeSegmentToSphere inclusion (fun _ => -(p : E)) hinclusion continuous_const hsegment,
      ContinuousMap.continuous _,
      fun u q => by rw [coe_normalizeSegmentToSphere_apply, smul_neg, ← sub_eq_add_neg]⟩
  have hGne : ∀ z, G z ≠ p := by
    rintro ⟨u, q⟩ hG
    refine normalize_smul_sub_smul_ne_of_ne
      (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2) hp
      (fun hq => q.2 (Set.mem_singleton_iff.mpr (Subtype.ext hq))) u ?_
    rw [← hGval u q, hG]
  have hneg : -p ≠ p := (ne_neg_of_mem_unit_sphere ℝ p).symm
  refine ⟨⟨-p, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]⟩, ⟨?_⟩⟩
  exact
    { toFun := fun z => ⟨G z,
        by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hGne z⟩
      continuous_toFun := hGcont.subtype_mk fun z => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hGne z
      map_zero_left := fun q => by
        have hraw : ((G (0, q) : sphere (0 : E) 1) : E) =
            ((q : sphere (0 : E) 1) : E) := by
          rw [hGval]
          simpa using normalize_eq_self_of_norm_eq_one
            (mem_sphere_zero_iff_norm.mp (q : sphere (0 : E) 1).2)
        exact Subtype.ext (Subtype.ext hraw)
      map_one_left := fun q => by
        have hraw : ((G (1, q) : sphere (0 : E) 1) : E) = -(p : E) := by
          rw [hGval]
          simpa [normalize_neg] using congrArg Neg.neg (normalize_eq_self_of_norm_eq_one hp)
        exact Subtype.ext (Subtype.ext (hraw.trans (coe_neg_sphere p).symm)) }

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
theorem homotopic_refl_of_notMem_range {x : sphere (0 : E) 1} (γ : Path x x)
    {p : sphere (0 : E) 1} (hp : p ∉ Set.range γ) : γ.Homotopic (Path.refl x) := by
  have hmem : ∀ t, γ t ∈ ({p}ᶜ : Set (sphere (0 : E) 1)) := fun t hmem =>
    hp ⟨t, (Set.mem_singleton_iff.mp hmem).symm ▸ rfl⟩
  exact Path.Homotopic.refl_of_forall_mem_of_nullhomotopic
    (nullhomotopic_inclusion_sphere_compl_singleton p) γ hmem

end TauCeti

end
