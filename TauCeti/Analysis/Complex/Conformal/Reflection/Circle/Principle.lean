/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Circle.Conjugate
public import TauCeti.Analysis.Complex.Conformal.Removability

/-!
# The Schwarz reflection principle across a circle

This file proves the circle case of the Schwarz reflection principle. A continuous function
holomorphic on one side of a circle and taking that circle into another circle extends across the
source circle by conjugating it with the two circle inversions. The extension is holomorphic
wherever the reflected branch avoids the target centre.

The analytic gluing step is Painlevé removability for a circle. We prove it here from the
straight-line theorem in `Conformal/Removability.lean`: two fractional-linear charts cover the
circle, and each chart carries the real axis to the circle. This is the Möbius-reduction route
specified by layer L4 of the conformal-mapping roadmap.

The construction follows Ahlfors, *Complex Analysis*, Chapters 4--6. It reuses Mathlib's
topological piecewise API and Euclidean inversion, together with Tau Ceti's line-removability and
circle-reflection conjugation theorems. Layer L4 is absent from the upstream Mathlib
Riemann-mapping draft mathlib4#33505.
-/

public section

namespace TauCeti

open Complex EuclideanGeometry Metric Set
open scoped ComplexConjugate

/-- A fractional-linear parametrisation of the circle centred at `c` through `c + a`.
It maps the real axis to that circle and omits `c + a`. -/
private noncomputable def circleLineMap (c a w : ℂ) : ℂ :=
  c + a * ((w - I) / (w + I))

/-- The inverse coordinate to `circleLineMap`, away from its omitted point `c + a`. -/
private noncomputable def circleLineMapInv (c a z : ℂ) : ℂ :=
  I * ((a + (z - c)) / (a - (z - c)))

private lemma differentiableOn_circleLineMap {c a : ℂ} {S : Set ℂ}
    (hI : -I ∉ S) :
    DifferentiableOn ℂ (circleLineMap c a) S := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · fun_prop
  apply DifferentiableAt.mul
  · fun_prop
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · intro h
    apply hI
    have : w = -I := by linear_combination h
    exact this ▸ hw

private lemma differentiableOn_circleLineMapInv {c a : ℂ} {S : Set ℂ}
    (ha : c + a ∉ S) :
    DifferentiableOn ℂ (circleLineMapInv c a) S := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · fun_prop
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · intro h
    apply ha
    have h' : a = z - c := sub_eq_zero.mp h
    have : z = c + a := by
      rw [h']
      ring
    exact this ▸ hz

private lemma circleLineMap_circleLineMapInv {c a z : ℂ}
    (ha : a ≠ 0) (hz : z ≠ c + a) :
    circleLineMap c a (circleLineMapInv c a z) = z := by
  have hden : a - (z - c) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hz
    rw [h]
    ring
  have hsum : I * ((a + (z - c)) / (a - (z - c))) + I ≠ 0 := by
    intro h
    have hzero : (2 * I) * a = 0 := by
      field_simp [hden] at h
      linear_combination h
    exact ha ((mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) I_ne_zero))
  rw [circleLineMap, circleLineMapInv]
  field_simp [hden, hsum]
  field_simp [ha]
  ring

private lemma circleLineMap_ne_neg_I {c a z : ℂ} (ha : a ≠ 0)
    (hz : z ≠ c + a) :
    circleLineMapInv c a z ≠ -I := by
  have hden : a - (z - c) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hz
    rw [h]
    ring
  intro h
  have hzero : 2 * a = 0 := by
    rw [circleLineMapInv] at h
    field_simp [hden] at h
    linear_combination h
  exact ha ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

private lemma circleLineMap_mem_sphere_iff {c a w : ℂ}
    (ha : a ≠ 0) (hw : w ≠ -I) :
    circleLineMap c a w ∈ sphere c ‖a‖ ↔ w.im = 0 := by
  rw [mem_sphere, circleLineMap, dist_eq, add_sub_cancel_left, norm_mul,
    norm_div]
  have hden : ‖w + I‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro h
    apply hw
    linear_combination h)
  have hnorm : ‖w - I‖ = ‖w + I‖ ↔ w.im = 0 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, I_re, sub_zero, sub_im, I_im, add_re,
      add_zero, add_im]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
      ring
  constructor
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 :=
      mul_left_cancel₀ (norm_ne_zero_iff.mpr ha) (by simpa using h)
    exact hnorm.mp (div_eq_one_iff_eq hden |>.mp hquot)
  · intro h
    have hquot : ‖w - I‖ / ‖w + I‖ = 1 :=
      div_eq_one_iff_eq hden |>.mpr (hnorm.mpr h)
    rw [hquot, mul_one]

private theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
    {Ω : Set ℂ} {F : ℂ → ℂ} {c a : ℂ} (ha : a ≠ 0)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c ‖a‖)) :
    DifferentiableOn ℂ F (Ω \ {c + a}) := by
  let φ := circleLineMap c a
  let ψ := circleLineMapInv c a
  let U := {-I}ᶜ ∩ φ ⁻¹' Ω
  have hV : IsOpen ({-I}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hφV : DifferentiableOn ℂ φ ({-I}ᶜ : Set ℂ) :=
    differentiableOn_circleLineMap fun h => h (by simp)
  have hφ : DifferentiableOn ℂ φ U := hφV.mono inter_subset_left
  have hU : IsOpen U :=
    hφV.continuousOn.isOpen_inter_preimage hV hΩ
  have hG : DifferentiableOn ℂ (F ∘ φ) U := by
    refine differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hU
      (hcont.comp hφ.continuousOn fun w hw => hw.2) ?_
    refine hdiff.comp (hφ.mono inter_subset_left) fun w hw => ⟨hw.1.2, ?_⟩
    rw [circleLineMap_mem_sphere_iff ha (fun h => by
      rw [h] at hw
      exact hw.1.1 (by simp))]
    exact hw.2
  have hψ : DifferentiableOn ℂ ψ (Ω \ {c + a}) :=
    differentiableOn_circleLineMapInv fun h => h.2 (by simp)
  refine (hG.comp hψ fun z hz => ?_).congr fun z hz => ?_
  · refine ⟨?_, ?_⟩
    · simpa using circleLineMap_ne_neg_I ha (by simpa using hz.2)
    · -- Expose the two local chart abbreviations so the inverse law rewrites the goal.
      change φ (ψ z) ∈ Ω
      dsimp only [φ, ψ]
      rw [circleLineMap_circleLineMapInv ha (by simpa using hz.2)]
      exact hz.1
  · -- The same chart abbreviations hide the pointwise equality used by `DifferentiableOn.congr`.
    change F z = F (φ (ψ z))
    dsimp only [φ, ψ]
    rw [circleLineMap_circleLineMapInv ha (by simpa using hz.2)]

/-- **Painlevé removability across a circle.** A function continuous on an open set `Ω ⊆ ℂ`
and holomorphic off a positive-radius circle is holomorphic throughout `Ω`.

Two fractional-linear charts, omitting opposite points of the circle, reduce the result to
Painlevé removability of the real axis. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere
    {Ω : Set ℂ} {F : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ sphere c r)) :
    DifferentiableOn ℂ F Ω := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hpos :=
    differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
      (c := c) (a := (r : ℂ)) hr0 hΩ hcont
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hdiff)
  have hneg :=
    differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere_omit
      (c := c) (a := -(r : ℂ)) (neg_ne_zero.mpr hr0) hΩ hcont
        (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hdiff)
  have hopenPos : IsOpen (Ω \ {c + (r : ℂ)}) := hΩ.sdiff isClosed_singleton
  have hopenNeg : IsOpen (Ω \ {c + -(r : ℂ)}) := hΩ.sdiff isClosed_singleton
  intro z hz
  by_cases hzr : z = c + (r : ℂ)
  · have hzneg : z ∈ Ω \ {c + -(r : ℂ)} := by
      refine ⟨hz, ?_⟩
      simp only [mem_singleton_iff]
      rw [hzr]
      intro h
      apply hr0
      have hzero : (2 : ℂ) * (r : ℂ) = 0 := by linear_combination h
      exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (hneg z hzneg).differentiableAt (hopenNeg.mem_nhds hzneg) |>.differentiableWithinAt
  · have hzpos : z ∈ Ω \ {c + (r : ℂ)} := ⟨hz, by simpa using hzr⟩
    exact (hpos z hzpos).differentiableAt (hopenPos.mem_nhds hzpos) |>.differentiableWithinAt

/-- The explicit extension used for Schwarz reflection across a circle. Inside the closed source
disc it is `f`; outside it is `f` conjugated by reflection in the source and target circles. -/
noncomputable def circleSchwarzReflection (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact (closedBall c r).piecewise f (circleReflectionConjugate c r d s f) z

/-- On the closed source disc, the circle-reflection extension agrees with the original map. -/
@[simp]
lemma circleSchwarzReflection_of_mem_closedBall {c : ℂ} {r : ℝ} (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ closedBall c r) :
    circleSchwarzReflection c r d s f z = f z := by
  classical
  simp [circleSchwarzReflection, hz]

/-- Outside the closed source disc, the extension is the circle-reflection conjugate. -/
@[simp]
lemma circleSchwarzReflection_of_notMem_closedBall (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∉ closedBall c r) :
    circleSchwarzReflection c r d s f z =
      circleReflectionConjugate c r d s f z := by
  classical
  simp [circleSchwarzReflection, hz]

/-- The circle-reflection extension is continuous when the original map is continuous on the
closed inside part, maps the source-circle boundary to the target circle, and avoids the target
centre in the punctured open inside part. -/
theorem continuousOn_circleSchwarzReflection {Ω : Set ℂ} {c d : ℂ} {r s : ℝ}
    {f : ℂ → ℂ} (hr : 0 < r) (hs : 0 < s)
    (hsymm : MapsTo (inversion c r) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ closedBall c r))
    (hboundary : MapsTo f (Ω ∩ sphere c r) (sphere d s))
    (havoid : ∀ z ∈ Ω ∩ ball c r, z ≠ c → f z ≠ d) :
    ContinuousOn (circleSchwarzReflection c r d s f) Ω := by
  classical
  let E := {z : ℂ | r ≤ dist z c}
  have hE : IsClosed E :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hclosure : closure (closedBall c r)ᶜ ⊆ E := by
    apply closure_minimal
    · intro z hz
      exact not_lt.mp fun h => hz (by simpa [mem_closedBall] using h.le)
    · exact hE
  have hinvCont : ContinuousOn (inversion c r) (Ω ∩ E) :=
    continuousOn_const.inversion continuousOn_const continuousOn_id fun z hz hzc => by
      have hdist : r ≤ dist z c := hz.2
      exact (not_le_of_gt hr) (by simpa [hzc] using hdist)
  have hinvMaps : MapsTo (inversion c r) (Ω ∩ E) (Ω ∩ closedBall c r) := by
    intro z hz
    have hdist : r ≤ dist z c := hz.2
    have hzc : z ≠ c := fun h => (not_le_of_gt hr) (by simpa [h] using hdist)
    refine ⟨hsymm hz.1, ?_⟩
    rw [mem_closedBall]
    exact not_lt.mp fun h =>
      (not_lt_of_ge hz.2) ((lt_dist_inversion_center_iff hr hzc).mp h)
  have havoidClosed : ∀ z ∈ Ω ∩ closedBall c r, z ≠ c → f z ≠ d := by
    intro z hz hzc
    by_cases hzr : dist z c < r
    · exact havoid z ⟨hz.1, by simpa [mem_ball] using hzr⟩ hzc
    · have heq : dist z c = r := le_antisymm (by simpa [mem_closedBall] using hz.2) (not_lt.mp hzr)
      have htarget : dist (f z) d = s :=
        hboundary ⟨hz.1, Metric.mem_sphere.mpr heq⟩
      intro hfd
      rw [hfd, dist_self] at htarget
      linarith
  have hreflected : ContinuousOn (circleReflectionConjugate c r d s f) (Ω ∩ E) := by
    have hraw : ContinuousOn (fun z => inversion d s (f (inversion c r z))) (Ω ∩ E) :=
      continuousOn_const.inversion continuousOn_const
        (hcont.comp hinvCont hinvMaps) fun z hz => havoidClosed _ (hinvMaps hz)
          ((inversion_eq_center hr.ne').not.mpr fun h => by
            have hdist : r ≤ dist z c := hz.2
            exact (not_le_of_gt hr) (by simpa [h] using hdist))
    exact hraw.congr fun z _ => circleReflectionConjugate_apply c r d s f z
  -- Unfold the opaque piecewise definition to apply Mathlib's gluing theorem.
  change ContinuousOn
    ((closedBall c r).piecewise f (circleReflectionConjugate c r d s f)) Ω
  apply ContinuousOn.piecewise
  · intro z hz
    have hzSphere : z ∈ sphere c r := frontier_closedBall_subset_sphere hz.2
    rw [circleReflectionConjugate_apply, inversion_of_mem_sphere hzSphere,
      inversion_of_mem_sphere (hboundary ⟨hz.1, hzSphere⟩)]
  · simpa only [isClosed_closedBall.closure_eq] using hcont
  · exact hreflected.mono fun z hz => ⟨hz.1, hclosure hz.2⟩

/-- **Schwarz reflection principle across a circle.** Let `Ω` be an open set invariant under
reflection in the source circle. If `f` is continuous on the closed inside part, holomorphic on
the open inside part, sends the source-circle boundary into the
target circle, and avoids the target centre in the punctured interior, then its explicit
circle-reflection extension is holomorphic throughout `Ω`.

The target-centre avoidance is exactly the non-pole condition for reflection in the target
circle. -/
theorem differentiableOn_circleSchwarzReflection_of_symmetric
    {Ω : Set ℂ} {c d : ℂ} {r s : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hΩ : IsOpen Ω)
    (hsymm : MapsTo (inversion c r) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ closedBall c r))
    (hholo : DifferentiableOn ℂ f (Ω ∩ ball c r))
    (hboundary : MapsTo f (Ω ∩ sphere c r) (sphere d s))
    (havoid : ∀ z ∈ Ω ∩ ball c r, z ≠ c → f z ≠ d) :
    DifferentiableOn ℂ (circleSchwarzReflection c r d s f) Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere (c := c) hr hΩ
    (continuousOn_circleSchwarzReflection hr hs hsymm hcont hboundary havoid) ?_
  have hrs : r ≠ 0 ∧ s ≠ 0 := ⟨hr.ne', hs.ne'⟩
  let E := Ω ∩ {z : ℂ | r < dist z c}
  have hEinv : MapsTo (inversion c r) E (Ω ∩ ball c r) := by
    intro z hz
    have hzc : z ≠ c := fun h => (not_lt_of_ge hr.le) (by simpa [h] using hz.2)
    exact ⟨hsymm hz.1, by
      rw [mem_ball, dist_inversion_center_lt_iff hr hzc]
      exact hz.2⟩
  have hreflected : DifferentiableOn ℂ (circleReflectionConjugate c r d s f) E :=
    differentiableOn_circleReflectionConjugate
      (fun _ => hholo) (fun _ => hEinv)
      (fun _ h => by
        have hdist : r < dist c c := h.2
        exact (not_lt_of_ge hr.le) (by simpa using hdist))
      (fun _ z hz => havoid _ (hEinv hz)
        ((inversion_eq_center hr.ne').not.mpr fun h => by
          have hdist : r < dist z c := hz.2
          exact (not_lt_of_ge hr.le) (by simpa [h] using hdist)))
  have hins : DifferentiableOn ℂ (circleSchwarzReflection c r d s f)
      (Ω ∩ ball c r) :=
    hholo.congr fun z hz => (circleSchwarzReflection_of_mem_closedBall d s f
      (ball_subset_closedBall hz.2))
  have hout : DifferentiableOn ℂ (circleSchwarzReflection c r d s f) E :=
    hreflected.congr fun z hz => (circleSchwarzReflection_of_notMem_closedBall c r d s f
      (by
        have hdist : r < dist z c := hz.2
        simpa [mem_closedBall] using not_le_of_gt hdist))
  have hopenIn : IsOpen (Ω ∩ ball c r) := hΩ.inter isOpen_ball
  have hopenOut : IsOpen E :=
    hΩ.inter (isOpen_lt continuous_const (continuous_id.dist continuous_const))
  intro z hz
  rcases lt_trichotomy (dist z c) r with hlt | heq | hgt
  · have hzin : z ∈ Ω ∩ ball c r := ⟨hz.1, by simpa [mem_ball] using hlt⟩
    exact (hins z hzin).differentiableAt (hopenIn.mem_nhds hzin) |>.differentiableWithinAt
  · exact (hz.2 (Metric.mem_sphere.mpr heq)).elim
  · have hzout : z ∈ E := ⟨hz.1, hgt⟩
    exact (hout z hzout).differentiableAt (hopenOut.mem_nhds hzout) |>.differentiableWithinAt

end TauCeti
