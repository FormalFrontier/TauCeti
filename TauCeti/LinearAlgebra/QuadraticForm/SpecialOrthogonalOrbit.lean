/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Orbits of nondegenerate special orthogonal groups

A nondegenerate special orthogonal group acts transitively on every nonzero quadratic level set in
dimension at least two. This is the linear-algebra input for the compact real Spin orbit interface.

Roadmap: RepresentationTheory — SpinRepresentations Layer 7, “Connectivity of the compact spin
group”. The construction follows Lawson–Michelsohn, *Spin Geometry* (1989), Chapter I, §2, and
uses TauCeti's quadratic-form reflection and special-orthogonal APIs.
-/

public section

open Module Submodule

namespace TauCeti.QuadraticMap

noncomputable section

universe u v

variable {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem exists_orthogonal_anisotropic (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hrank : 2 ≤ finrank K V) {y : V} (hy : Q y ≠ 0) :
    ∃ z : V, Q.IsOrtho z y ∧ Q z ≠ 0 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let B : LinearMap.BilinForm K V := Q.polarBilin
  let W : Submodule K V := B.orthogonal (K ∙ y)
  have hB : B.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff (Q := Q)).mpr hQ
  have hBsymm : B.IsSymm := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hByy : B y y ≠ 0 := by
    simpa only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      Nat.cast_ofNat] using mul_ne_zero (NeZero.ne (2 : K)) hy
  have hWnondeg : (B.restrict W).Nondegenerate :=
    B.restrict_nondegenerate_orthogonal_spanSingleton hB hBsymm.isRefl hByy
  have hWrank : 0 < finrank K W := by
    dsimp only [W]
    rw [B.finrank_orthogonal hB]
    rw [finrank_span_singleton (fun h => hy (by simp [h]))]
    omega
  let _ : Nontrivial W := Module.nontrivial_of_finrank_pos hWrank
  obtain ⟨z, hz⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    hWnondeg.ne_zero (LinearMap.BilinForm.isSymm_iff.mp (hBsymm.restrict W))
  refine ⟨z, ?_, ?_⟩
  · apply QuadraticMap.isOrtho_polarBilin.mp
    simpa only [B, W, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using
      z.2 y (Submodule.mem_span_singleton_self y)
  · have hz' : B (z : V) (z : V) ≠ 0 := by
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using hz
    simpa only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      Nat.cast_ofNat, mul_ne_zero_iff_left (NeZero.ne (2 : K))] using hz'

private noncomputable def reflectionPairSpecialOrthogonal
    (Q : QuadraticForm K V) (u v : V) [Invertible (Q u)] [Invertible (Q v)] :
    specialOrthogonalGroup Q :=
  ⟨(reflectionOrthogonal Q u : V ≃ₗ[K] V) * reflectionOrthogonal Q v, by
    rw [mem_specialOrthogonalGroup_iff]
    constructor
    · exact (orthogonalGroup Q).mul_mem (reflectionOrthogonal Q u).2
        (reflectionOrthogonal Q v).2
    · simp⟩

omit [NeZero (2 : K)] in
private theorem reflectionPairSpecialOrthogonal_apply
    (Q : QuadraticForm K V) (u v x : V) [Invertible (Q u)] [Invertible (Q v)] :
    (reflectionPairSpecialOrthogonal Q u v : V ≃ₗ[K] V) x =
      reflection Q u (reflection Q v x) := by
  simp only [reflectionPairSpecialOrthogonal, Subgroup.coe_mk, LinearEquiv.mul_apply,
    coe_reflectionOrthogonal]

/-- A nondegenerate special orthogonal group acts transitively on every nonzero quadratic level set
when the quadratic space has dimension at least two. -/
theorem exists_specialOrthogonal_map_eq_of_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate)
    (hrank : 2 ≤ finrank K V) {x y : V} (hxy : Q x = Q y) (hy : Q y ≠ 0) :
    ∃ g : specialOrthogonalGroup Q, (g : V ≃ₗ[K] V) x = y := by
  rcases isUnit_sub_or_add_of_map_eq Q x y hxy hy with hsub | hadd
  · let _ : Invertible (Q (x - y)) := hsub.invertible
    obtain ⟨z, hzy, hzQ⟩ := exists_orthogonal_anisotropic Q hQ hrank (y := y) hy
    let _ : Invertible (Q z) := (isUnit_iff_ne_zero.mpr hzQ).invertible
    refine ⟨reflectionPairSpecialOrthogonal Q z (x - y), ?_⟩
    rw [reflectionPairSpecialOrthogonal_apply]
    rw [reflection_sub_apply_eq_of_map_eq Q x y hxy]
    exact reflection_apply_of_isOrtho Q z hzy
  · let _ : Invertible (Q (x - -y)) := by
      simpa only [sub_neg_eq_add] using hadd.invertible
    have hyUnit : IsUnit (Q y) := isUnit_iff_ne_zero.mpr hy
    let _ : Invertible (Q y) := hyUnit.invertible
    refine ⟨reflectionPairSpecialOrthogonal Q y (x - -y), ?_⟩
    rw [reflectionPairSpecialOrthogonal_apply]
    rw [reflection_sub_apply_eq_of_map_eq Q x (-y)]
    · simp
    · simpa [QuadraticMap.map_neg] using hxy

end

end TauCeti.QuadraticMap
