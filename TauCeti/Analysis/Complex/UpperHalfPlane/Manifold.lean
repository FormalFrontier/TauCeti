/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

import TauCeti.Topology.DiscreteSeparation

/-!
# Analyticity through `ofComplex`

A function holomorphic on the upper half-plane, extended to `ℂ` by `ofComplex`, is
analytic at every point of the open upper half-plane. Holomorphy on `ℍ` is also invariant
under the Möbius action of a positive-determinant real matrix, the biholomorphism
`UpperHalfPlane.mdifferentiable_smul` exhibits.

## Main declarations

* `TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex`.
* `TauCeti.UpperHalfPlane.mdifferentiable_comp_smul_iff` — `τ ↦ f (g • τ)` is holomorphic
  exactly when `f` is, for `g : GL (Fin 2) ℝ` of positive determinant.
* `TauCeti.UpperHalfPlane.not_accPt_zeros_comp_ofComplex` and
  `TauCeti.UpperHalfPlane.exists_isOpen_zeros_inter` — a subset's zeros isolate in an
  open neighbourhood.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public section

open UpperHalfPlane

open scoped Manifold MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- A function holomorphic on `ℍ` composes with `ofComplex` to a function analytic at
every point of the open upper half-plane. -/
lemma analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

/-- The zeros of a nonzero holomorphic function's complex extension do not accumulate at
any point of the upper half-plane. -/
lemma not_accPt_zeros_comp_ofComplex {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {x : ℂ} (hx : 0 < x.im) :
    ¬AccPt x (Filter.principal {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) := by
  have hall : AnalyticOnNhd ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} := fun w hw =>
    analyticAt_comp_ofComplex hg hw
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hg0
  have hcod := hall.preimage_zero_mem_codiscreteWithin (x := (τ : ℂ))
    (by simpa [Function.comp, ofComplex_apply] using hτ) τ.2
    ⟨⟨Complex.I, by simp⟩, (convex_halfSpace_im_gt 0).isPreconnected⟩
  have hne := mem_codiscreteWithin_accPt.mp hcod x hx
  have hset : {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} =
      {z : ℂ | 0 < z.im} \ (g ∘ ofComplex) ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_not]
  rwa [hset]

/-- Any subset of the upper half-plane has an open neighbourhood in the upper half-plane
containing no zeros of the function's complex extension beyond its own. -/
lemma exists_isOpen_zeros_inter {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      {z ∈ U | (g ∘ ofComplex) z = 0} = {z ∈ K | (g ∘ ofComplex) z = 0} := by
  obtain ⟨U, hUo, hKU, hUV, hUZ⟩ := TauCeti.exists_isOpen_inter_eq_of_not_accPt
    (Z := {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) isOpen_upperHalfPlaneSet hK
    fun x hx => not_accPt_zeros_comp_ofComplex hg hg0 (hK hx)
  refine ⟨U, hUo, hKU, hUV, ?_⟩
  have hmassage : ∀ {W : Set ℂ}, W ⊆ {z : ℂ | 0 < z.im} →
      {z ∈ W | (g ∘ ofComplex) z = 0} =
        W ∩ {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} := by
    intro W hW
    ext z
    exact ⟨fun hz => ⟨hz.1, hW hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  rw [hmassage hUV, hmassage hK, hUZ]

/-! ### Holomorphy and the Möbius action -/

/-- **Holomorphy is invariant under a positive-determinant Möbius action.** For any
`g : GL (Fin 2) ℝ` with `0 < det g`, the function `τ ↦ f (g • τ)` is holomorphic exactly when
`f` is: `g` acts on `ℍ` by a biholomorphism, whose inverse is the action of `g⁻¹`, again of
positive determinant. -/
lemma mdifferentiable_comp_smul_iff {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) {f : ℍ → ℂ} :
    MDiff (fun τ ↦ f (g • τ)) ↔ MDiff f := by
  have hg' : 0 < ((g⁻¹).det : ℝ) := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hg
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp (mdifferentiable_smul hg)⟩
  have hcomp : f = (fun τ ↦ f (g • τ)) ∘ fun τ : ℍ ↦ g⁻¹ • τ := by
    funext τ
    simp [smul_smul]
  rw [hcomp]
  exact hf.comp (mdifferentiable_smul hg')

end TauCeti.UpperHalfPlane

end
