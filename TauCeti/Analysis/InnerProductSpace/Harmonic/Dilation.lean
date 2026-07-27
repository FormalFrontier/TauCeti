/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Dilation invariance of the Laplacian and harmonic functions

`TauCeti.Analysis.InnerProductSpace.Laplacian.Basic` records invariance under rigid motions and the
Laplacian scaling law under affine homotheties. This file transports the homothety bookkeeping to
harmonicity: under the right-composition `AffineMap.homothety a c`, harmonicity is preserved and
reflected when `c ≠ 0`.

These lemmas are a small Lane C prerequisite from the PDE roadmap. They let later mean-value,
maximum-principle, and Poisson-kernel arguments normalize balls by translating and rescaling
without reproving the Laplacian calculation each time.

## Main declarations

* `TauCeti.harmonicAt_comp_homothety_right_iff`: harmonicity is invariant under nonzero
  homothety about an arbitrary center.
* `TauCeti.harmonicOnNhd_comp_homothety_right_iff`: set-level nonzero homothety invariance.
* `TauCeti.harmonicAt_comp_smul_right_iff`: harmonicity is invariant under nonzero dilation.
* `TauCeti.harmonicOnNhd_comp_smul_right_iff`: set-level nonzero dilation invariance.
* `TauCeti.harmonicAt_comp_const_add_smul_iff`: harmonicity is invariant under the affine
  normalization `z ↦ x + c • z` with nonzero scale.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_iff`: set-level affine normalization invariance.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Homotheties of a finite-dimensional normed affine space are homeomorphisms when the scale is
nonzero. -/
private abbrev homothetyHomeomorph (a : E) (c : ℝ) (hc : c ≠ 0) : E ≃ₜ E :=
  (AffineEquiv.toContinuousAffineEquiv
    (AffineEquiv.homothetyUnitsMulHom a (Units.mk0 c hc))).toHomeomorph

private lemma homothetyHomeomorph_apply (a : E) (c : ℝ) (hc : c ≠ 0) (x : E) :
    homothetyHomeomorph a c hc x = AffineMap.homothety a c x := by
  -- Expose the `toHomeomorph` coercion back to the continuous affine equivalence it wraps.
  change (AffineEquiv.toContinuousAffineEquiv
    (AffineEquiv.homothetyUnitsMulHom a (Units.mk0 c hc)) : E ≃ᴬ[ℝ] E) x =
      AffineMap.homothety a c x
  rw [AffineEquiv.coe_toContinuousAffineEquiv]
  exact congrFun (AffineEquiv.coe_homothetyUnitsMulHom_apply a (Units.mk0 c hc)) x

omit [FiniteDimensional ℝ E] in
private lemma contDiffAt_homothety (a : E) (c : ℝ) (x : E) :
    ContDiffAt ℝ 2 (fun y : E ↦ AffineMap.homothety a c y) x := by
  have h : ContDiffAt ℝ 2 (fun y : E ↦ c • (y - a) + a) x := by
    fun_prop
  simpa [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using h

omit [FiniteDimensional ℝ E] in
/-- Twice continuous differentiability at a point is invariant under nonzero homothety.

For `c ≠ 0`, the function `y ↦ f (AffineMap.homothety a c y)` is `C²` at `x` iff `f` is `C²`
at `AffineMap.homothety a c x`. -/
private lemma contDiffAt_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {x : E} :
    ContDiffAt ℝ 2 (fun y : E ↦ f (AffineMap.homothety a c y)) x ↔
      ContDiffAt ℝ 2 f (AffineMap.homothety a c x) := by
  constructor
  · intro h
    -- Right-compose with the inverse homothety `AffineMap.homothety a c⁻¹` to recover `f`.
    have hφ : ContDiffAt ℝ 2 (fun y : E ↦ AffineMap.homothety a c⁻¹ y)
        (AffineMap.homothety a c x) :=
      contDiffAt_homothety a c⁻¹ (AffineMap.homothety a c x)
    have hx : AffineMap.homothety a c⁻¹ (AffineMap.homothety a c x) = x := by
      rw [← AffineMap.homothety_mul_apply]
      simp [hc]
    have h' : ContDiffAt ℝ 2 (fun y : E ↦ f (AffineMap.homothety a c y))
        ((fun y : E ↦ AffineMap.homothety a c⁻¹ y)
          (AffineMap.homothety a c x)) := by
      simpa [hx] using h
    have hc' := h'.comp (AffineMap.homothety a c x) hφ
    have hgf :
        (fun y : E ↦ f (AffineMap.homothety a c y)) ∘
            (fun y : E ↦ AffineMap.homothety a c⁻¹ y) = f := by
      funext y
      simp only [Function.comp_apply]
      rw [← AffineMap.homothety_mul_apply]
      simp [hc]
    rwa [hgf] at hc'
  · intro h
    exact h.comp x (contDiffAt_homothety a c x)

/-- Local vanishing of the Laplacian is invariant under nonzero homothety.

For `c ≠ 0`, the Laplacian of `y ↦ f (AffineMap.homothety a c y)` vanishes near `x` iff the
Laplacian of `f` vanishes near `AffineMap.homothety a c x`. -/
private lemma laplacian_eventuallyEq_zero_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0)
    {f : E → F} {x : E} :
    (Δ (fun y : E ↦ f (AffineMap.homothety a c y)) =ᶠ[𝓝 x] 0) ↔
      (Δ f =ᶠ[𝓝 (AffineMap.homothety a c x)] 0) := by
  -- `e` realises the homothety as a homeomorphism so we can transport the neighbourhood filter.
  let e : E ≃ₜ E := homothetyHomeomorph a c hc
  have he : ∀ y : E, e y = AffineMap.homothety a c y := fun y ↦
    homothetyHomeomorph_apply a c hc y
  rw [laplacian_comp_homothety_right a c f]
  have hscale :
      (fun y : E ↦ c ^ 2 • (Δ f) (AffineMap.homothety a c y)) =
        (fun z ↦ c ^ 2 • z) ∘ (Δ f ∘ e) := by
    funext y
    simp [he y, Function.comp_apply]
  rw [hscale]
  have hzero : Function.Injective (fun z : F ↦ c ^ 2 • z) := by
    exact smul_right_injective F (pow_ne_zero 2 hc)
  constructor
  · intro h
    have h' : Δ f ∘ e =ᶠ[𝓝 x] 0 := by
      filter_upwards [h] with y hy
      exact hzero (by simpa [Function.comp_apply] using hy)
    have hmain : Δ f =ᶠ[𝓝 (e x)] (0 : E → F) := by
      rw [← e.map_nhds_eq x]
      exact ((Filter.eventuallyEq_map (f := 𝓝 x) (m := e) (f₁ := Δ f)
        (f₂ := (0 : E → F))).symm).1 (by simpa using h')
    simpa [he x] using hmain
  · intro h
    have h' : Δ f ∘ e =ᶠ[𝓝 x] 0 := by
      have hmain : Δ f =ᶠ[𝓝 (e x)] (0 : E → F) := by
        simpa [he x] using h
      rw [← e.map_nhds_eq x] at hmain
      -- `Filter.eventuallyEq_map` compares `g ∘ e` with `g' ∘ e`; reshape the zero side as
      -- `0 ∘ e` (definitionally `0`) so it applies to `hmain`.
      change Δ f ∘ e =ᶠ[𝓝 x] (0 : E → F) ∘ e
      exact ((Filter.eventuallyEq_map (f := 𝓝 x) (m := e) (f₁ := Δ f)
        (f₂ := (0 : E → F))).symm).2 hmain
    filter_upwards [h'] with y hy
    -- Unfold the scaled composition produced by `hscale` at this point.
    change c ^ 2 • ((Δ f ∘ e) y) = 0
    rw [hy]
    simp

/-- **Harmonicity is invariant under nonzero homothety.**

For `c ≠ 0`, the function `y ↦ f (AffineMap.homothety a c y)` is harmonic at `x` iff `f`
is harmonic at `AffineMap.homothety a c x`. -/
theorem harmonicAt_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {x : E} :
    HarmonicAt (fun y ↦ f (AffineMap.homothety a c y)) x ↔
      HarmonicAt f (AffineMap.homothety a c x) :=
  ⟨fun hf ↦ ⟨(contDiffAt_comp_homothety_right_iff a c hc).1 hf.1,
      (laplacian_eventuallyEq_zero_comp_homothety_right_iff a c hc).1 hf.2⟩,
    fun hf ↦ ⟨(contDiffAt_comp_homothety_right_iff a c hc).2 hf.1,
      (laplacian_eventuallyEq_zero_comp_homothety_right_iff a c hc).2 hf.2⟩⟩

/-- Harmonicity on a neighbourhood of a set is invariant under nonzero homothety. -/
theorem harmonicOnNhd_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {s : Set E} :
    HarmonicOnNhd (fun y ↦ f (AffineMap.homothety a c y))
        ((fun y ↦ AffineMap.homothety a c y) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  let e : E ≃ₜ E := homothetyHomeomorph a c hc
  have he : ∀ y : E, e y = AffineMap.homothety a c y := fun y ↦
    homothetyHomeomorph_apply a c hc y
  constructor
  · intro hf y hy
    have hye : AffineMap.homothety a c (e.symm y) = y := by
      rw [← he (e.symm y)]
      exact e.apply_symm_apply y
    have hpre : AffineMap.homothety a c (e.symm y) ∈ s := by rwa [hye]
    have h := hf (e.symm y) hpre
    simpa [hye] using (harmonicAt_comp_homothety_right_iff a c hc).1 h
  · intro hf x hx
    exact (harmonicAt_comp_homothety_right_iff a c hc).2
      (hf (AffineMap.homothety a c x) hx)

/-- **Harmonicity is invariant under nonzero dilation.**

For `c ≠ 0`, the function `x ↦ f (c • x)` is harmonic at `x` iff `f` is harmonic at
`c • x`. -/
theorem harmonicAt_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F} {x : E} :
    HarmonicAt (fun y ↦ f (c • y)) x ↔ HarmonicAt f (c • x) := by
  have hfun : (fun y : E ↦ f (c • y)) =
      fun y ↦ f (AffineMap.homothety (0 : E) c y) := by
    funext y
    simp [AffineMap.homothety_apply]
  have hx : AffineMap.homothety (0 : E) c x = c • x := by
    simp [AffineMap.homothety_apply]
  rw [hfun, harmonicAt_comp_homothety_right_iff (0 : E) c hc, hx]

/-- Harmonicity on a neighbourhood of a set is invariant under nonzero dilation. -/
theorem harmonicOnNhd_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {s : Set E} :
    HarmonicOnNhd (fun y ↦ f (c • y)) ((fun y ↦ c • y) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  have hfun : (fun y : E ↦ f (c • y)) =
      fun y ↦ f (AffineMap.homothety (0 : E) c y) := by
    funext y
    simp [AffineMap.homothety_apply]
  have hset : ((fun y : E ↦ c • y) ⁻¹' s) =
      ((fun y : E ↦ AffineMap.homothety (0 : E) c y) ⁻¹' s) := by
    ext y
    simp [AffineMap.homothety_apply]
  rw [hfun, hset]
  exact harmonicOnNhd_comp_homothety_right_iff (0 : E) c hc

/-- **Harmonicity is invariant under the affine normalization `z ↦ x + c • z`** when the scale
is nonzero.

For `c ≠ 0`, the function `z ↦ f (x + c • z)` is harmonic at `y` iff `f` is harmonic at
`x + c • y`. -/
theorem harmonicAt_comp_const_add_smul_iff (x : E) {c : ℝ} (hc : c ≠ 0) {f : E → F} {y : E} :
    HarmonicAt (fun z ↦ f (x + c • z)) y ↔ HarmonicAt f (x + c • y) := by
  have hfun : (fun z : E ↦ f (x + c • z)) = fun z ↦ (fun w : E ↦ f (x + w)) (c • z) := rfl
  have hpoint : x + c • y = c • y + x := by rw [add_comm]
  have hscale :=
    harmonicAt_comp_smul_right_iff (c := c) hc (f := fun w : E ↦ f (x + w)) (x := y)
  have htranslate :=
    harmonicAt_comp_add_right_iff (f := f) (x := c • y) (a := x)
  have hcomm : (fun w : E ↦ f (x + w)) = fun w ↦ f (w + x) := by
    funext w
    rw [add_comm]
  rw [hcomm] at hscale
  rw [hfun]
  exact hscale.trans (by simpa [hpoint] using htranslate)

/-- **Harmonicity on a neighbourhood of a set is invariant under the affine normalization
`z ↦ x + c • z`** when the scale is nonzero.

For `c ≠ 0`, the function `z ↦ f (x + c • z)` is harmonic near `(fun z ↦ x + c • z) ⁻¹' s`
iff `f` is harmonic near `s`. -/
theorem harmonicOnNhd_comp_const_add_smul_iff (x : E) {c : ℝ} (hc : c ≠ 0) {f : E → F}
    {s : Set E} :
    HarmonicOnNhd (fun z ↦ f (x + c • z)) ((fun z ↦ x + c • z) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  have hfun : (fun z : E ↦ f (x + c • z)) = fun z ↦ (fun w : E ↦ f (w + x)) (c • z) := by
    funext z
    rw [add_comm]
  have hset : ((fun z : E ↦ x + c • z) ⁻¹' s) =
      ((fun z : E ↦ c • z) ⁻¹' ((fun y : E ↦ y + x) ⁻¹' s)) := by
    ext z
    simp [add_comm]
  rw [hfun, hset, harmonicOnNhd_comp_smul_right_iff (c := c) hc (f := fun w : E ↦ f (w + x)),
    harmonicOnNhd_comp_add_right_iff (f := f) (s := s) x]

end TauCeti

end
