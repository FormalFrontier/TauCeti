/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Geometric invariance of harmonic functions

`TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean` proves that the Laplacian `Δ` is invariant
under the rigid motions of a Euclidean space — affine isometry equivalences, with linear
isometry equivalences and translations as special cases. This file transports that invariance to
harmonic functions.

Smoothness enters here, where the `ContDiffAt` half of `InnerProductSpace.HarmonicAt` is
transported across the equivalence: harmonicity is invariant under the full isometry group, the
symmetry that underlies the mean-value property and the construction of radial harmonic functions
(PDE roadmap, Lane C, item 12).

## Main declarations

* `TauCeti.harmonicAt_comp_affineIsometryEquiv_right_iff`,
  `TauCeti.harmonicOnNhd_comp_affineIsometryEquiv_right_iff`: harmonicity is invariant
  under affine isometry equivalences.
* `TauCeti.harmonicAt_comp_linearIsometryEquiv_right_iff`,
  `TauCeti.harmonicOnNhd_comp_linearIsometryEquiv_right_iff`: harmonicity is invariant
  under linear isometric changes of variable.
* `TauCeti.harmonicAt_comp_add_right_iff`, `TauCeti.harmonicOnNhd_comp_add_right_iff`:
  harmonicity is invariant under translation.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Harmonicity is invariant under isometric changes of variable.** For a linear isometry
equivalence `l`, the function `f ∘ l` is harmonic at `x` iff `f` is harmonic at `l x`. -/
theorem harmonicAt_comp_linearIsometryEquiv_right_iff (l : E ≃ₗᵢ[ℝ] E') {f : E' → F}
    {x : E} : HarmonicAt (f ∘ l) x ↔ HarmonicAt f (l x) := by
  have hcd : ContDiffAt ℝ 2 (f ∘ l) x ↔ ContDiffAt ℝ 2 f (l x) := by
    have := l.toContinuousLinearEquiv.contDiffAt_comp_iff (f := f) (n := 2) (x := l x)
    simpa using this
  have hlap : (Δ (f ∘ l) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (l x)] 0) := by
    rw [laplacian_comp_linearIsometryEquiv_right l f]
    -- View precomposition by `l` as precomposition by the homeomorphism `l.toHomeomorph`
    -- (definitionally the same map) so `map_nhds_eq` can transport the neighbourhood filter.
    change (Δ f ∘ l.toHomeomorph =ᶠ[𝓝 x] 0) ↔
      (Δ f =ᶠ[𝓝 (l.toHomeomorph x)] 0)
    rw [← l.toHomeomorph.map_nhds_eq x]
    -- `Filter.eventuallyEq_map` reads `g =ᶠ[map h l] g' ↔ g ∘ h =ᶠ[l] g' ∘ h`; write the zero
    -- side as `0 ∘ l.toHomeomorph` (definitionally `0`) to land in that shape.
    change (Δ f ∘ l.toHomeomorph =ᶠ[𝓝 x] (0 : E' → F) ∘ l.toHomeomorph) ↔
      (Δ f =ᶠ[Filter.map l.toHomeomorph (𝓝 x)] (0 : E' → F))
    exact (Filter.eventuallyEq_map (f := 𝓝 x) (m := l.toHomeomorph) (f₁ := Δ f)
      (f₂ := (0 : E' → F))).symm
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩, fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- **Harmonicity is invariant under translation.** The function `y ↦ f (y + a)` is harmonic
at `x` iff `f` is harmonic at `x + a`. -/
theorem harmonicAt_comp_add_right_iff {f : E → F} {x a : E} :
    HarmonicAt (fun y ↦ f (y + a)) x ↔ HarmonicAt f (x + a) := by
  have hcd : ContDiffAt ℝ 2 (fun y ↦ f (y + a)) x ↔ ContDiffAt ℝ 2 f (x + a) := by
    constructor
    · intro h
      have hφ : ContDiffAt ℝ 2 (fun z : E ↦ z - a) (x + a) := by fun_prop
      have h' : ContDiffAt ℝ 2 (fun y ↦ f (y + a)) ((fun z : E ↦ z - a) (x + a)) := by
        simpa using h
      have hc := h'.comp (x + a) hφ
      have hgf : (fun y ↦ f (y + a)) ∘ (fun z : E ↦ z - a) = f := by funext w; simp
      rwa [hgf] at hc
    · intro h
      have hψ : ContDiffAt ℝ 2 (fun y : E ↦ y + a) x := by fun_prop
      exact h.comp x hψ
  have hlap : (Δ (fun y ↦ f (y + a)) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (x + a)] 0) := by
    rw [laplacian_comp_add_right f a]
    -- Rephrase translation as precomposition with the homeomorphism `Homeomorph.addRight a`
    -- (definitionally the same map) so `map_nhds_eq` can transport the neighbourhood filter.
    change ((fun y : E ↦ Δ f (y + a)) =ᶠ[𝓝 x] 0) ↔
      (Δ f =ᶠ[𝓝 ((Homeomorph.addRight a) x)] 0)
    rw [← (Homeomorph.addRight a).map_nhds_eq x]
    -- Match `Filter.eventuallyEq_map` (`g =ᶠ[map h l] g' ↔ g ∘ h =ᶠ[l] g' ∘ h`) by writing the
    -- zero side as `0 ∘ addRight a` (definitionally `0`).
    change (Δ f ∘ Homeomorph.addRight a =ᶠ[𝓝 x]
        (0 : E → F) ∘ Homeomorph.addRight a) ↔
      (Δ f =ᶠ[Filter.map (Homeomorph.addRight a) (𝓝 x)] (0 : E → F))
    exact (Filter.eventuallyEq_map (f := 𝓝 x) (m := Homeomorph.addRight a) (f₁ := Δ f)
      (f₂ := (0 : E → F))).symm
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩, fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- **Harmonicity is invariant under affine isometries.** For an affine isometry equivalence
`e`, the function `f ∘ e` is harmonic at `x` iff `f` is harmonic at `e x`. -/
theorem harmonicAt_comp_affineIsometryEquiv_right_iff (e : E ≃ᵃⁱ[ℝ] E') {f : E' → F}
    {x : E} : HarmonicAt (f ∘ e) x ↔ HarmonicAt f (e x) := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext y
    have hy : e y = e.linearIsometryEquiv y + e 0 := by
      simpa using e.map_vadd (0 : E) y
    simp [Function.comp_apply, hy]
  rw [hcomp, harmonicAt_comp_linearIsometryEquiv_right_iff e.linearIsometryEquiv,
    harmonicAt_comp_add_right_iff]
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  rw [← hx]

/-- Harmonicity on a neighbourhood of a set is invariant under an affine isometry equivalence. -/
theorem harmonicOnNhd_comp_affineIsometryEquiv_right_iff (e : E ≃ᵃⁱ[ℝ] E') {f : E' → F}
    {s : Set E'} : HarmonicOnNhd (f ∘ e) (e ⁻¹' s) ↔ HarmonicOnNhd f s := by
  constructor
  · intro hf y hy
    have hpre : e (e.symm y) ∈ s := by simpa using hy
    have h := hf (e.symm y) hpre
    simpa using (harmonicAt_comp_affineIsometryEquiv_right_iff e).1 h
  · intro hf x hx
    exact (harmonicAt_comp_affineIsometryEquiv_right_iff e).2 (hf (e x) hx)

/-- Harmonicity on a neighbourhood of a set is invariant under a linear isometric change of
variable. -/
theorem harmonicOnNhd_comp_linearIsometryEquiv_right_iff (l : E ≃ₗᵢ[ℝ] E') {f : E' → F}
    {s : Set E'} : HarmonicOnNhd (f ∘ l) (l ⁻¹' s) ↔ HarmonicOnNhd f s := by
  rw [← LinearIsometryEquiv.coe_toAffineIsometryEquiv l]
  exact harmonicOnNhd_comp_affineIsometryEquiv_right_iff l.toAffineIsometryEquiv

/-- Harmonicity on a neighbourhood of a set is invariant under translation. -/
theorem harmonicOnNhd_comp_add_right_iff {f : E → F} {s : Set E} (a : E) :
    HarmonicOnNhd (fun y ↦ f (y + a)) ((fun y ↦ y + a) ⁻¹' s) ↔ HarmonicOnNhd f s := by
  let e : E ≃ᵃⁱ[ℝ] E := AffineIsometryEquiv.constVAdd ℝ E a
  have hfun : (fun y ↦ f (y + a)) = f ∘ e := by
    funext y
    simp [e, Function.comp_apply, add_comm]
  have hset : ((fun y ↦ y + a) ⁻¹' s) = e ⁻¹' s := by
    ext y
    simp [e, add_comm]
  rw [hfun, hset]
  exact harmonicOnNhd_comp_affineIsometryEquiv_right_iff e

end TauCeti
