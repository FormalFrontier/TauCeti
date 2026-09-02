/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
public import TauCeti.Analysis.Complex.Conformal.Biholomorph
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Schwarz reflection of a conformal map is conformal

`Conformal/Reflection/Principle.lean` extends a function holomorphic on the upper part of a
conjugation-symmetric open set `Ω` and real on `Ω ∩ ℝ` to a function holomorphic on all of `Ω`.
This file upgrades that extension from *holomorphic* to *conformal*: if the original map is
injective on the closed upper part and sends the open upper part into the open upper half-plane,
then the reflected extension `schwarzReflection f` is injective on all of `Ω` — hence conformal at
every point of `Ω`, with a holomorphic inverse on its image.

This is the form layer **L5** of `ConformalMapping/README.md` consumes: the boundary
correspondence extends a Riemann map across an *analytic boundary arc* by reflecting it, and what
that step needs is not merely a holomorphic continuation but a conformal one — a continuation that
is again injective, and whose derivative therefore does not vanish *on the boundary arc itself*.
That last point is the payoff: `f` is not assumed differentiable at the real points of `Ω` at all,
only continuous there from above, yet `conformalAt_schwarzReflection_of_symmetric` produces a
nonvanishing derivative there for the extension.

## The proof

Purely a matter of which half-plane each branch lands in, once the sign bookkeeping is recorded:

* on `Ω ∩ {0 < im}` the extension is `f`, which lands in `{0 < im}` by hypothesis;
* on `Ω ∩ ℝ` the extension is `f`, which is real by hypothesis — for injectivity alone only the
  weaker `0 ≤ (f z).im` is used there;
* on `Ω ∩ {im < 0}` the extension is `conj ∘ f ∘ conj`, and conjugation twice reverses the sign of
  the imaginary part, so it lands in `{im < 0}`.

So the two branches have images in the two *open* half-planes and cannot collide with each other;
a coincidence of values must therefore happen inside one branch, where injectivity of `f` on the
closed upper part settles it — directly on the upper branch, and after cancelling the two
conjugations on the lower one. The strictness of `0 < (f z).im` for `0 < z.im` is what
separates the branches, and it is genuinely needed: without it `f` could map an interior point to
the real axis, where the two branches meet.

The reflection hypotheses here are exactly those of the reflection principle, plus the two extra
ones (`hupper` and `hinj`); the holomorphy of the extension is quoted from
`differentiableOn_schwarzReflection_of_symmetric`, its pointwise conformality from
`TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn`, and the holomorphy of the inverse from
`TauCeti.DifferentiableOn.invFunOn`.

## Main results

* `TauCeti.injOn_schwarzReflection_of_symmetric` — the reflected extension of an injective map is
  injective.
* `TauCeti.image_schwarzReflection_of_symmetric` — its image is the image of the closed upper part
  together with the mirror image of that set.
* `TauCeti.deriv_schwarzReflection_ne_zero` — its derivative vanishes nowhere on `Ω`, in
  particular on the boundary segment `Ω ∩ ℝ`.
* `TauCeti.conformalAt_schwarzReflection_of_symmetric` — the extension is conformal at every point
  of `Ω`, including the points of the real axis.
* `TauCeti.differentiableOn_invFunOn_schwarzReflection_of_symmetric` — its inverse is holomorphic,
  so the extension is a biholomorphism onto its image.
* `TauCeti.exists_differentiableOn_injOn_eqOn_conj_of_symmetric` — the packaged form: a conformal
  map of the upper part extends to a conformal map of `Ω` obeying the reflection symmetry.

## Coordination with upstream Mathlib

Layer L4 (reflection) and layer L5 (boundary correspondence) are absent from the in-progress
Mathlib Riemann-mapping draft
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
so this is new Lean formalization rather than a shim; the shared L0--L3 infrastructure it consumes
(`Conformal/Biholomorph.lean`, `Conformal/Inverse/Function.lean`) carries its own shim notice.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 1--3.
-/

public section

namespace TauCeti

open Complex Set
open scoped ComplexConjugate

variable {Ω : Set ℂ} {f : ℂ → ℂ}

/-- On the open upper part of the domain the reflection extension is the original map, so it
inherits the hypothesis that `f` takes the open upper part into the open upper half-plane. -/
theorem mapsTo_schwarzReflection_im_pos
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im}) :
    Set.MapsTo (schwarzReflection f) (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} := by
  rintro z ⟨hzΩ, (hzim : 0 < z.im)⟩
  rw [Set.mem_ofPred_eq, schwarzReflection_of_im_nonneg hzim.le]
  exact hupper ⟨hzΩ, hzim⟩

/-- The reflected branch takes the lower part of a conjugation-symmetric domain into the open
lower half-plane: it conjugates a value of `f` at a point of the open upper part, and conjugation
reverses the sign of the imaginary part. -/
theorem mapsTo_schwarzReflection_im_neg (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im}) :
    Set.MapsTo (schwarzReflection f) (Ω ∩ {z : ℂ | z.im < 0}) {z : ℂ | z.im < 0} := by
  rintro z ⟨hzΩ, (hzim : z.im < 0)⟩
  have hconj : (starRingEnd ℂ) z ∈ Ω ∩ {z : ℂ | 0 < z.im} := by
    refine ⟨hΩ hzΩ, ?_⟩
    rw [Set.mem_ofPred_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
    exact neg_pos.mpr hzim
  rw [Set.mem_ofPred_eq, schwarzReflection_of_im_neg hzim, starRingEnd_apply, Complex.star_def,
    Complex.conj_im]
  exact neg_neg_of_pos (hupper hconj)

/-- On the closed upper part the extension has nonnegative imaginary part: positive above the
axis, and nonnegative on it. Only nonnegativity of `(f z).im` on the axis is needed, not the
reflection principle's stronger `(f z).im = 0`. -/
theorem im_schwarzReflection_nonneg
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (haxis : ∀ z ∈ Ω, z.im = 0 → 0 ≤ (f z).im)
    {z : ℂ} (hz : z ∈ Ω) (hzim : 0 ≤ z.im) : 0 ≤ (schwarzReflection f z).im := by
  rw [schwarzReflection_of_im_nonneg hzim]
  rcases hzim.lt_or_eq with h | h
  · exact (hupper ⟨hz, h⟩).le
  · exact haxis z hz h.symm

/-- **Schwarz reflection preserves injectivity.** On a conjugation-symmetric open set `Ω`, if `f`
is injective on the closed upper part, has nonnegative imaginary part on `Ω ∩ ℝ`, and maps the open
upper part into the open upper half-plane, then the reflection extension `schwarzReflection f` is
injective on all of `Ω`.

The two branches take values in the two open half-planes, so they cannot meet; within a single
branch the injectivity of `f` applies, on the lower branch after cancelling the conjugations.

Injectivity alone does not need `f` to be *real* on the axis, only to stay in the closed upper
half-plane there; the corollaries below feed `haxis` from the reflection principle's `hreal`. -/
theorem injOn_schwarzReflection_of_symmetric (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (haxis : ∀ z ∈ Ω, z.im = 0 → 0 ≤ (f z).im) (hinj : Set.InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    Set.InjOn (schwarzReflection f) Ω := by
  intro z hz w hw hzw
  rcases le_or_gt 0 z.im with hz0 | hz0 <;> rcases le_or_gt 0 w.im with hw0 | hw0
  · -- both points lie in the closed upper part, where the extension is `f`
    rw [schwarzReflection_of_im_nonneg hz0, schwarzReflection_of_im_nonneg hw0] at hzw
    exact hinj ⟨hz, hz0⟩ ⟨hw, hw0⟩ hzw
  · -- the value at `z` lies in the closed upper half-plane, the one at `w` strictly below it
    exact absurd (hzw ▸ im_schwarzReflection_nonneg hupper haxis hz hz0)
      (not_le.mpr (mapsTo_schwarzReflection_im_neg hΩ hupper ⟨hw, hw0⟩))
  · -- the mirror image of the previous case
    exact absurd (hzw ▸ mapsTo_schwarzReflection_im_neg hΩ hupper ⟨hz, hz0⟩)
      (not_lt.mpr (im_schwarzReflection_nonneg hupper haxis hw hw0))
  · -- both points lie strictly below the axis: cancel the two conjugations
    rw [schwarzReflection_of_im_neg hz0, schwarzReflection_of_im_neg hw0] at hzw
    have hmem : ∀ {v : ℂ}, v ∈ Ω → v.im < 0 → (starRingEnd ℂ) v ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} := by
      intro v hvΩ hvim
      refine ⟨hΩ hvΩ, ?_⟩
      rw [Set.mem_ofPred_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
      exact (neg_pos.mpr hvim).le
    have hf : f ((starRingEnd ℂ) z) = f ((starRingEnd ℂ) w) := by
      simpa using congrArg (starRingEnd ℂ) hzw
    have hconj := hinj (hmem hz hz0) (hmem hw hw0) hf
    simpa using congrArg (starRingEnd ℂ) hconj

/-- The image of the reflection extension is the image of the closed upper part together with its
mirror image in the real axis. The real axis contributes to both pieces, since `f` is real
there. -/
theorem image_schwarzReflection_of_symmetric (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    schwarzReflection f '' Ω =
      f '' (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∪ (starRingEnd ℂ) '' (f '' (Ω ∩ {z : ℂ | 0 ≤ z.im})) := by
  ext w
  constructor
  · rintro ⟨z, hzΩ, rfl⟩
    rcases le_or_gt 0 z.im with hz0 | hz0
    · exact Or.inl ⟨z, ⟨hzΩ, hz0⟩, (schwarzReflection_of_im_nonneg hz0).symm⟩
    · have hconj : (starRingEnd ℂ) z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im} := by
        refine ⟨hΩ hzΩ, ?_⟩
        rw [Set.mem_ofPred_eq, starRingEnd_apply, Complex.star_def, Complex.conj_im]
        exact (neg_pos.mpr hz0).le
      exact Or.inr ⟨f ((starRingEnd ℂ) z), ⟨(starRingEnd ℂ) z, hconj, rfl⟩,
        (schwarzReflection_of_im_neg hz0).symm⟩
  · rintro (⟨z, ⟨hzΩ, (hz0 : 0 ≤ z.im)⟩, rfl⟩ | ⟨v, ⟨z, ⟨hzΩ, (hz0 : 0 ≤ z.im)⟩, rfl⟩, rfl⟩)
    · exact ⟨z, hzΩ, schwarzReflection_of_im_nonneg hz0⟩
    · rcases hz0.lt_or_eq with h | h
      · exact ⟨(starRingEnd ℂ) z, hΩ hzΩ, schwarzReflection_conj_of_im_pos h⟩
      · refine ⟨z, hzΩ, ?_⟩
        rw [schwarzReflection_of_im_zero h.symm]
        exact (Complex.conj_eq_iff_im.mpr (hreal z hzΩ h.symm)).symm

/-- **The reflected map has nonvanishing derivative on the boundary segment.** Under the
hypotheses of the reflection principle, together with injectivity of `f` on the closed upper part
and the requirement that the open upper part goes to the open upper half-plane, the derivative of
the extension vanishes nowhere on `Ω`. At a point of `Ω ∩ ℝ` this is a statement about the
boundary behaviour of `f`, which is not assumed differentiable there. -/
theorem deriv_schwarzReflection_ne_zero (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (hinj : Set.InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    {z : ℂ} (hz : z ∈ Ω) : deriv (schwarzReflection f) z ≠ 0 := by
  have hd := differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont hholo hreal
  have hi := injOn_schwarzReflection_of_symmetric hΩ hupper
    (fun w hw h => (hreal w hw h).ge) hinj
  exact deriv_ne_zero_of_injOn hd hΩopen hi hz

/-- **Schwarz reflection of a conformal map is conformal.** Under the hypotheses of the reflection
principle, together with injectivity of `f` on the closed upper part and the requirement that the
open upper part goes to the open upper half-plane, the extension is conformal at every point of
`Ω` — in particular at the points of the real axis, where `f` itself is not assumed
differentiable. -/
theorem conformalAt_schwarzReflection_of_symmetric
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (hinj : Set.InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    {z : ℂ} (hz : z ∈ Ω) : ConformalAt (schwarzReflection f) z :=
  TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont hholo hreal) hΩopen
    (injOn_schwarzReflection_of_symmetric hΩ hupper (fun w hw h => (hreal w hw h).ge) hinj) hz

/-- The inverse of the reflection extension is holomorphic on its image: the extension is a
biholomorphism of `Ω` onto the doubled image described by
`image_schwarzReflection_of_symmetric`. -/
theorem differentiableOn_invFunOn_schwarzReflection_of_symmetric
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (hinj : Set.InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    DifferentiableOn ℂ (Function.invFunOn (schwarzReflection f) Ω) (schwarzReflection f '' Ω) :=
  TauCeti.DifferentiableOn.invFunOn
    (differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont hholo hreal) hΩopen
    (injOn_schwarzReflection_of_symmetric hΩ hupper (fun w hw h => (hreal w hw h).ge) hinj)

/-- **The conformal reflection principle**, packaged existential form: a conformal map of the
upper part of a conjugation-symmetric open set that is real on the axis and takes the open upper
part into the open upper half-plane extends to a *conformal* map of the whole set, agreeing with
the original on the closed upper part and obeying the reflection symmetry
`F (conj z) = conj (F z)`. The explicit witness is `schwarzReflection f`.

This strengthens `exists_differentiableOn_eqOn_conj_of_symmetric` by the injectivity clause. -/
theorem exists_differentiableOn_injOn_eqOn_conj_of_symmetric
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0)
    (hupper : Set.MapsTo f (Ω ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im})
    (hinj : Set.InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ Set.InjOn F Ω ∧
      Set.EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∧
      ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z) :=
  ⟨schwarzReflection f,
    differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont hholo hreal,
    injOn_schwarzReflection_of_symmetric hΩ hupper (fun w hw h => (hreal w hw h).ge) hinj,
    eqOn_schwarzReflection_of_subset_im_nonneg fun _ hz => hz.2,
    fun _ hz => schwarzReflection_conj_of_real_on_axis hreal hz⟩

end TauCeti
