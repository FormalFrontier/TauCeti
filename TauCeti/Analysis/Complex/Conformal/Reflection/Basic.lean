/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Piecewise

/-!
# Conjugation and holomorphic domains

This file records the elementary conjugation API used by the conformal-mapping roadmap's
Schwarz-reflection layer.  Mathlib already proves the pointwise fact
`DifferentiableAt.conj_conj`: if `f` is complex differentiable at `conj z`, then
`z ↦ conj (f (conj z))` is complex differentiable at `z`.  The lemmas here package the
corresponding within-set statement for reflected images, which is the form needed before the
real-axis Schwarz reflection principle.

It also names the standard real-axis Schwarz-reflection extension
`z ↦ if 0 ≤ z.im then f z else conj (f (conj z))`, together with the pointwise API for the
upper and lower half-planes and the conjugation symmetry forced by real boundary values.
The closed upper branch is intentionally exposed through the pointwise simplifier
`schwarzReflection_of_im_nonneg`, with subset-level wrappers for branch agreement and
differentiability transfer.  The continuity lemmas record the topological gluing input for
the later Morera-based reflection theorem: the reflected branch is continuous on reflected
sets, and the explicit Schwarz-reflection extension is continuous across the real axis when
the boundary values are real.
The private semilinear within-set helper adapts the proof pattern of Mathlib's
`HasFDerivAt.comp_semilinear`.
-/

public section

namespace TauCeti

open Complex Filter Set
open scoped ComplexConjugate

variable {f : ℂ → ℂ} {S : Set ℂ}

/--
The explicit real-axis Schwarz-reflection extension of a function from the closed upper
half-plane to the plane.

On `0 ≤ z.im` this is `f z`; on the lower half-plane it is `conj (f (conj z))`.
-/
noncomputable def schwarzReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

/-- The Schwarz-reflection extension is the explicit upper/lower half-plane witness. -/
theorem schwarzReflection_def (f : ℂ → ℂ) (z : ℂ) :
    schwarzReflection f z =
      if 0 ≤ z.im then f z else (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) := by
  rw [schwarzReflection]

/-- On the closed upper half-plane, Schwarz reflection agrees with the original function. -/
@[simp]
lemma schwarzReflection_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflection f z = f z := by
  simp [schwarzReflection, hz]

/-- On the lower half-plane, Schwarz reflection is `z ↦ conj (f (conj z))`. -/
@[simp]
lemma schwarzReflection_of_im_neg {z : ℂ} (hz : z.im < 0) :
    schwarzReflection f z = (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) := by
  simp [schwarzReflection, not_le.mpr hz]

/-- On the real axis, Schwarz reflection agrees with the original function. -/
lemma schwarzReflection_of_im_zero {z : ℂ} (hz : z.im = 0) :
    schwarzReflection f z = f z := by
  exact schwarzReflection_of_im_nonneg (f := f) (z := z) hz.ge

/-- On any subset of the closed upper half-plane, Schwarz reflection agrees with the original
function. -/
lemma eqOn_schwarzReflection_of_subset_im_nonneg
    (hS : S ⊆ {z : ℂ | 0 ≤ z.im}) :
    Set.EqOn (schwarzReflection f) f S :=
  fun _ hz => schwarzReflection_of_im_nonneg (f := f) (hS hz)

/-- On any subset of the lower half-plane, Schwarz reflection agrees with the reflected
branch. -/
lemma eqOn_schwarzReflection_of_subset_im_neg
    (hS : S ⊆ {z : ℂ | z.im < 0}) :
    Set.EqOn (schwarzReflection f) (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) S :=
  fun _ hz => schwarzReflection_of_im_neg (f := f) (hS hz)

/-- Conjugating a point in the upper half-plane evaluates the reflected lower branch. -/
lemma schwarzReflection_conj_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    schwarzReflection f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z) := by
  have hneg : ((starRingEnd ℂ) z).im < 0 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
    exact neg_neg_of_pos hz
  simpa [starRingEnd_self_apply] using
    schwarzReflection_of_im_neg (f := f) (z := (starRingEnd ℂ) z) hneg

/-- Conjugating the lower-half-plane value recovers the original function at `conj z`. -/
lemma conj_schwarzReflection_of_im_neg {z : ℂ} (hz : z.im < 0) :
    (starRingEnd ℂ) (schwarzReflection f z) = f ((starRingEnd ℂ) z) := by
  rw [schwarzReflection_of_im_neg (f := f) hz, starRingEnd_self_apply]

/--
At a real-axis point where `f` has a real value, `f` commutes with conjugation:
`f z = conj (f (conj z))`.
-/
private lemma apply_eq_conj_apply_conj_of_im_zero_of_apply_im_zero
    {z : ℂ} (hz : z.im = 0) (hreal : (f z).im = 0) :
    f z = (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) := by
  have hzconj : (starRingEnd ℂ) z = z := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
    exact hz
  rw [hzconj]
  exact (Complex.conj_eq_iff_im.mpr hreal).symm

/--
The Schwarz-reflection extension is conjugation-symmetric when the original function has real
value at the real-axis point under consideration.
-/
lemma schwarzReflection_conj
    (z : ℂ) (hreal : z.im = 0 → ((f z).im = 0)) :
    schwarzReflection f ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (schwarzReflection f z) := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · rw [schwarzReflection_of_im_neg (f := f) hneg]
    have hnonneg : 0 ≤ ((starRingEnd ℂ) z).im := by
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_nonneg.mpr hneg.le
    rw [schwarzReflection_of_im_nonneg (f := f) hnonneg]
    simp
  · rw [schwarzReflection_of_im_zero (f := f) hzero]
    have hconj_im : ((starRingEnd ℂ) z).im = 0 := by
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_im, hzero, neg_zero]
    rw [schwarzReflection_of_im_zero (f := f) hconj_im,
      apply_eq_conj_apply_conj_of_im_zero_of_apply_im_zero (f := f) hzero (hreal hzero),
      starRingEnd_self_apply]
  · rw [schwarzReflection_conj_of_im_pos (f := f) hpos]
    rw [schwarzReflection_of_im_nonneg (f := f) hpos.le]

/--
On a domain where the original function is real-valued on the real axis, the Schwarz-reflection
extension is conjugation-symmetric at each point of the domain.
-/
lemma schwarzReflection_conj_of_real_on_axis {Ω : Set ℂ}
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) {z : ℂ} (hz : z ∈ Ω) :
    schwarzReflection f ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (schwarzReflection f z) :=
  schwarzReflection_conj (f := f) z fun hz0 => hreal z hz hz0

/--
On a domain where the original function is real-valued on the real axis, the Schwarz-reflection
extension is conjugation-symmetric on that domain.
-/
lemma eqOn_schwarzReflection_conj_of_real_on_axis {Ω : Set ℂ}
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    Set.EqOn (fun z => schwarzReflection f ((starRingEnd ℂ) z))
      (fun z => (starRingEnd ℂ) (schwarzReflection f z)) Ω := fun _ hz =>
  schwarzReflection_conj_of_real_on_axis (f := f) hreal hz

/--
For a domain closed under conjugation, conjugation carries the upper half-plane part of the
domain to its lower half-plane part.
-/
lemma image_conj_inter_im_pos_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω) :
    (starRingEnd ℂ) '' (Ω ∩ {z | 0 < z.im}) = Ω ∩ {z | z.im < 0} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwΩ, hwim⟩, rfl⟩
    constructor
    · exact hΩ hwΩ
    · rw [Set.mem_setOf_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_neg_of_pos hwim
  · rintro ⟨hzΩ, hzim⟩
    refine ⟨(starRingEnd ℂ) z, ⟨?_, ?_⟩, ?_⟩
    · exact hΩ hzΩ
    · rw [Set.mem_setOf_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_pos.mpr hzim
    · rw [starRingEnd_self_apply]

/--
For a domain closed under conjugation, conjugation carries the lower half-plane part of the
domain to its upper half-plane part.
-/
lemma image_conj_inter_im_neg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω) :
    (starRingEnd ℂ) '' (Ω ∩ {z | z.im < 0}) = Ω ∩ {z | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwΩ, hwim⟩, rfl⟩
    constructor
    · exact hΩ hwΩ
    · rw [Set.mem_setOf_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_pos.mpr hwim
  · rintro ⟨hzΩ, hzim⟩
    refine ⟨(starRingEnd ℂ) z, ⟨?_, ?_⟩, ?_⟩
    · exact hΩ hzΩ
    · rw [Set.mem_setOf_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_neg_of_pos hzim
    · rw [starRingEnd_self_apply]

/--
Conjugating both source and target preserves continuity on reflected sets.
-/
lemma continuousOn_conj_conj (hf : ContinuousOn f S) :
    ContinuousOn (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) '' S) := by
  have hmaps : MapsTo (starRingEnd ℂ) ((starRingEnd ℂ) '' S) S := by
    rintro w ⟨x, hx, rfl⟩
    rwa [starRingEnd_self_apply]
  simpa only [Function.comp_def, starRingEnd_apply] using
    (hf.comp Complex.continuous_conj.continuousOn hmaps).star

/--
Conjugating both source and target preserves continuity on reflected sets, in both directions.
-/
@[simp]
lemma continuousOn_conj_conj_iff :
    ContinuousOn (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
        ((starRingEnd ℂ) '' S) ↔
      ContinuousOn f S := by
  constructor
  · intro h
    have htwice :=
      continuousOn_conj_conj
        (S := (starRingEnd ℂ) '' S)
        (f := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) h
    simpa [Function.Involutive.image_eq_preimage_symm
      (starRingEnd_self_apply : Function.Involutive (starRingEnd ℂ)), Set.preimage_preimage,
      Function.comp_def] using htwice
  · exact continuousOn_conj_conj

/--
On any subset of the closed upper half-plane, the explicit Schwarz-reflection extension is
continuous whenever the original function is.
-/
lemma continuousOn_schwarzReflection_of_subset_im_nonneg
    (hS : S ⊆ {z : ℂ | 0 ≤ z.im}) (hf : ContinuousOn f S) :
    ContinuousOn (schwarzReflection f) S :=
  hf.congr fun _ hz => eqOn_schwarzReflection_of_subset_im_nonneg (f := f) hS hz

/--
If a domain is closed under conjugation and `f` is continuous on its upper half-plane
part, then the reflected branch `z ↦ conj (f (conj z))` is continuous on the lower
half-plane part.
-/
lemma continuousOn_conj_conj_inter_im_neg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : ContinuousOn f (Ω ∩ {z | 0 < z.im})) :
    ContinuousOn (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      (Ω ∩ {z | z.im < 0}) := by
  simpa [image_conj_inter_im_pos_of_symmetric hΩ] using
    continuousOn_conj_conj (S := Ω ∩ {z | 0 < z.im}) (f := f) hf

/--
On the lower half-plane part of a domain closed under conjugation, the explicit Schwarz
reflection extension is continuous whenever the original function is continuous on the
upper half-plane part.
-/
lemma continuousOn_schwarzReflection_inter_im_neg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : ContinuousOn f (Ω ∩ {z | 0 < z.im})) :
    ContinuousOn (schwarzReflection f) (Ω ∩ {z | z.im < 0}) := by
  intro z hz
  exact ((continuousOn_conj_conj_inter_im_neg_of_symmetric
    (f := f) hΩ hf) z hz).congr
      (fun w hw => schwarzReflection_of_im_neg (f := f) hw.2)
      (schwarzReflection_of_im_neg (f := f) hz.2)

/--
For a domain closed under conjugation, conjugation carries the closed upper half-plane part of
the domain to its closed lower half-plane part.
-/
lemma image_conj_inter_im_nonneg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω) :
    (starRingEnd ℂ) '' (Ω ∩ {z | 0 ≤ z.im}) = Ω ∩ {z | z.im ≤ 0} := by
  ext w
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxΩ, hxim⟩, rfl⟩
    refine ⟨hΩ hxΩ, ?_⟩
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
    exact neg_nonpos.mpr hxim
  · rintro ⟨hwΩ, hwim⟩
    refine ⟨(starRingEnd ℂ) w, ⟨hΩ hwΩ, ?_⟩, ?_⟩
    · rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact neg_nonneg.mpr hwim
    · rw [starRingEnd_self_apply]

/--
If a domain `Ω` is closed under conjugation, `f` is continuous on its closed upper half-plane
part, and `f` takes real values at the real-axis points of `Ω`, then the explicit
Schwarz-reflection extension is continuous on `Ω`.
-/
lemma continuousOn_schwarzReflection_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ContinuousOn (schwarzReflection f) Ω := by
  have hUclosed : IsClosed {z : ℂ | 0 ≤ z.im} :=
    isClosed_Ici.preimage Complex.continuous_im
  have hlower : ContinuousOn (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      (Ω ∩ {z : ℂ | z.im ≤ 0}) := by
    rw [← image_conj_inter_im_nonneg_of_symmetric hΩ]
    exact continuousOn_conj_conj (S := Ω ∩ {z : ℂ | 0 ≤ z.im}) (f := f) hf
  have hpiece :
      ContinuousOn (fun z : ℂ =>
        if 0 ≤ z.im then f z else (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) Ω := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro z hz
      rw [Set.mem_inter_iff, Complex.frontier_setOf_le_im, Set.mem_setOf_eq] at hz
      exact apply_eq_conj_apply_conj_of_im_zero_of_apply_im_zero (f := f) hz.2
        (hreal z hz.1 hz.2)
    · rwa [hUclosed.closure_eq]
    · simp only [not_le]
      rw [Complex.closure_setOf_im_lt]
      exact hlower
  exact hpiece.congr fun z _ => schwarzReflection_def f z

/--
If `f` is continuous on the closed upper half-plane and takes real values on the real axis,
then its explicit Schwarz-reflection extension is continuous on the plane.
-/
lemma continuous_schwarzReflection
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ z : ℂ, z.im = 0 → (f z).im = 0) :
    Continuous (schwarzReflection f) := by
  rw [← continuousOn_univ]
  refine continuousOn_schwarzReflection_of_symmetric (Ω := Set.univ)
    (Set.mapsTo_univ _ _) ?_ (fun z _ => hreal z)
  rwa [Set.univ_inter]

private lemma starRingEnd_eq_starL (z : ℂ) :
    (starRingEnd ℂ) z = (starL ℂ : ℂ ≃L⋆[ℂ] ℂ) z := by
  rw [starL_apply, starRingEnd_apply]

private lemma HasFDerivWithinAt.comp_semilinear_preimage
    {𝕜 V V' W W' : Type*} [NontriviallyNormedField 𝕜] {σ σ' : RingHom 𝕜 𝕜}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup W'] [NormedSpace 𝕜 W']
    [RingHomIsometric σ] [RingHomInvPair σ σ']
    (L : W →SL[σ] W') (R : V' →SL[σ'] V)
    {g : V → W} {g' : V →L[𝕜] W} {T : Set V} {x : V'}
    (hg : HasFDerivWithinAt g g' T (R x)) :
    HasFDerivWithinAt (L ∘ g ∘ R) (L.comp (g'.comp R)) (R ⁻¹' T) x := by
  rw [hasFDerivWithinAt_iff_isLittleO] at ⊢ hg
  have : RingHomIsometric σ' := .inv σ
  have hR : Tendsto R (nhdsWithin x (R ⁻¹' T)) (nhdsWithin (R x) T) :=
    R.continuous.continuousAt.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage R T)
  have hsmall := hg.comp_tendsto hR
  have hRsub : ((fun x' => x' - R x) ∘ R) =O[nhdsWithin x (R ⁻¹' T)] fun x' => x' - x := by
    simpa [Function.comp_def, map_sub] using R.isBigO_sub (nhdsWithin x (R ⁻¹' T)) x
  simpa [Function.comp_def, map_sub] using
    ((L.isBigO_comp _ _).trans_isLittleO hsmall).trans_isBigO hRsub

/--
Antiholomorphic-composition prerequisite for Schwarz reflection.

If `f` is holomorphic on `S`, then `z ↦ conj (f (conj z))` is holomorphic on the reflected
set `conj '' S`.
-/
lemma differentiableOn_conj_conj (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) '' S) := by
  intro z hz
  have hzS : (starRingEnd ℂ) z ∈ S :=
    (Set.mem_image_iff_of_inverse
      (Function.Involutive.leftInverse (starRingEnd_self_apply : Function.Involutive
        (starRingEnd ℂ)))
      (Function.Involutive.rightInverse (starRingEnd_self_apply : Function.Involutive
        (starRingEnd ℂ)))).mp hz
  rcases (hf ((starRingEnd ℂ) z) hzS) with ⟨f', hf'⟩
  have hstar :=
    HasFDerivWithinAt.comp_semilinear_preimage
      (starL ℂ).toContinuousLinearMap (starL ℂ).toContinuousLinearMap (x := z) hf'
  rw [Function.Involutive.image_eq_preimage_symm
    (starRingEnd_self_apply : Function.Involutive (starRingEnd ℂ))]
  have hfun :
      (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) =
        (⇑(starL ℂ).toContinuousLinearMap ∘ f ∘ ⇑(starL ℂ).toContinuousLinearMap) := by
    funext w
    dsimp [Function.comp_def]
    rw [starRingEnd_eq_starL, starRingEnd_eq_starL]
  have hset : (starRingEnd ℂ) ⁻¹' S = ⇑(starL ℂ).toContinuousLinearMap ⁻¹' S := by
    ext w
    -- Expose membership in the preimages before rewriting across the two conjugation coercions.
    change (starRingEnd ℂ) w ∈ S ↔ ((starL ℂ).toContinuousLinearMap : ℂ → ℂ) w ∈ S
    have hw : (starRingEnd ℂ) w = ((starL ℂ).toContinuousLinearMap : ℂ → ℂ) w := by
      rw [starRingEnd_eq_starL]
      rfl
    rw [hw]
  rw [hfun, hset]
  exact hstar.differentiableWithinAt

/--
On any subset of the closed upper half-plane, the explicit Schwarz-reflection extension is
holomorphic whenever the original function is.
-/
lemma differentiableOn_schwarzReflection_of_subset_im_nonneg
    (hS : S ⊆ {z : ℂ | 0 ≤ z.im}) (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (schwarzReflection f) S :=
  hf.congr fun _ hz => eqOn_schwarzReflection_of_subset_im_nonneg (f := f) hS hz

/--
Conjugating both source and target preserves holomorphicity on domains, in both directions.
-/
@[simp]
lemma differentiableOn_conj_conj_iff :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
        ((starRingEnd ℂ) '' S) ↔
      DifferentiableOn ℂ f S := by
  constructor
  · intro h
    have htwice :=
      differentiableOn_conj_conj
        (S := (starRingEnd ℂ) '' S)
        (f := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) h
    simpa [Function.Involutive.image_eq_preimage_symm
      (starRingEnd_self_apply : Function.Involutive (starRingEnd ℂ)), Set.preimage_preimage,
      Function.comp_def] using htwice
  · exact differentiableOn_conj_conj

/--
If a domain is closed under conjugation and `f` is holomorphic on its upper half-plane
part, then the reflected branch `z ↦ conj (f (conj z))` is holomorphic on the lower
half-plane part.
-/
lemma differentiableOn_conj_conj_inter_im_neg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im})) :
    DifferentiableOn ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      (Ω ∩ {z | z.im < 0}) := by
  simpa [image_conj_inter_im_pos_of_symmetric hΩ] using
    differentiableOn_conj_conj (S := Ω ∩ {z | 0 < z.im}) (f := f) hf

/--
On the lower half-plane part of a domain closed under conjugation, the explicit Schwarz
reflection extension is holomorphic whenever the original function is holomorphic on the
upper half-plane part.
-/
lemma differentiableOn_schwarzReflection_inter_im_neg_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im})) :
    DifferentiableOn ℂ (schwarzReflection f) (Ω ∩ {z | z.im < 0}) := by
  intro z hz
  exact ((differentiableOn_conj_conj_inter_im_neg_of_symmetric
    (f := f) hΩ hf) z hz).congr
      (fun w hw => schwarzReflection_of_im_neg (f := f) hw.2)
      (schwarzReflection_of_im_neg (f := f) hz.2)

/-- Away from the real axis, the Schwarz-reflection extension is holomorphic on a
conjugation-symmetric domain whenever the original function is holomorphic on its upper
half-plane part. -/
lemma differentiableOn_schwarzReflection_inter_im_ne_zero_of_symmetric {Ω : Set ℂ}
    (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hf : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im})) :
    DifferentiableOn ℂ (schwarzReflection f) (Ω ∩ {z | z.im ≠ 0}) := by
  have hupper : DifferentiableOn ℂ (schwarzReflection f) (Ω ∩ {z | 0 < z.im}) :=
    differentiableOn_schwarzReflection_of_subset_im_nonneg (f := f)
      (fun _ hz => by simpa using hz.2.le) hf
  have hlower := differentiableOn_schwarzReflection_inter_im_neg_of_symmetric
    (f := f) hΩ hf
  intro z hz
  rcases lt_or_gt_of_ne hz.2 with hzneg | hzpos
  · apply (differentiableWithinAt_congr_set ?_).mp (hlower z ⟨hz.1, hzneg⟩)
    filter_upwards [
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzneg] with w hw
    apply propext
    constructor
    · rintro ⟨hwΩ, _⟩
      exact ⟨hwΩ, ne_of_lt hw⟩
    · rintro ⟨hwΩ, _⟩
      exact ⟨hwΩ, hw⟩
  · apply (differentiableWithinAt_congr_set ?_).mp (hupper z ⟨hz.1, hzpos⟩)
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzpos] with w hw
    apply propext
    constructor
    · rintro ⟨hwΩ, _⟩
      exact ⟨hwΩ, ne_of_gt hw⟩
    · rintro ⟨hwΩ, _⟩
      exact ⟨hwΩ, hw⟩

/-- At a point in the open upper half-plane, the Schwarz-reflection extension has the same
derivative as the original function. -/
lemma hasDerivAt_schwarzReflection_of_im_pos {z f' : ℂ} (hz : 0 < z.im)
    (hf : HasDerivAt f f' z) :
    HasDerivAt (schwarzReflection f) f' z :=
  hf.congr_of_eventuallyEq
    (mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      fun _ hw => schwarzReflection_of_im_nonneg (f := f) hw.le)

/-- At a point in the open lower half-plane, the derivative of the Schwarz-reflection
extension is the conjugate of the derivative of `f` at the conjugate point. -/
lemma hasDerivAt_schwarzReflection_of_im_neg {z f' : ℂ} (hz : z.im < 0)
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z)) :
    HasDerivAt (schwarzReflection f) ((starRingEnd ℂ) f') z := by
  have hreflected : HasDerivAt
      (fun w : ℂ => (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) f') z := by
    simpa [Function.comp_def] using hf.conj_conj
  exact hreflected.congr_of_eventuallyEq
    (mem_of_superset ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz)
      fun w hw => schwarzReflection_of_im_neg (f := f) hw)

/-- On the open upper half-plane, the derivative of the Schwarz-reflection extension agrees
with the derivative of the original function. -/
@[simp] lemma deriv_schwarzReflection_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    deriv (schwarzReflection f) z = deriv f z := by
  exact Filter.EventuallyEq.deriv_eq <|
    mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      fun w hw => schwarzReflection_of_im_nonneg (f := f) hw.le

/-- On the open lower half-plane, the derivative of the Schwarz-reflection extension is the
conjugate of the derivative of the original function at the conjugate point. -/
@[simp] lemma deriv_schwarzReflection_of_im_neg {z : ℂ} (hz : z.im < 0) :
    deriv (schwarzReflection f) z =
      (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) z)) := by
  calc
    deriv (schwarzReflection f) z =
        deriv (fun w : ℂ => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z :=
      Filter.EventuallyEq.deriv_eq <|
        mem_of_superset ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz)
          fun w hw => schwarzReflection_of_im_neg (f := f) hw
    _ = (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) z)) := by
      simpa only [Function.comp_def] using congrFun deriv_conj_conj z

end TauCeti
