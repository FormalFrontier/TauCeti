/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Circle.Conjugate
public import TauCeti.Analysis.Complex.Conformal.Removability.Circle

/-!
# The Schwarz reflection principle across a circle

This file proves the circle case of the Schwarz reflection principle. A continuous function
holomorphic on one side of a circle and taking that circle into another circle extends across the
source circle by conjugating it with the two circle inversions. The extension is holomorphic
wherever the reflected branch avoids the target centre.

The analytic gluing step is Painlevé removability for a circle, supplied by
`Conformal/Removability/Circle.lean`. This is the Möbius-reduction route specified by layer L4 of
the conformal-mapping roadmap.

The construction follows Ahlfors, *Complex Analysis*, Chapters 4--6. It reuses Mathlib's
topological piecewise API and Euclidean inversion, together with Tau Ceti's line-removability and
circle-reflection conjugation theorems. Layer L4 is absent from the upstream Mathlib
Riemann-mapping draft mathlib4#33505.
-/

public section

namespace TauCeti

open Complex EuclideanGeometry Metric Set
open scoped ComplexConjugate

/-- The explicit extension used for Schwarz reflection across a circle. Inside the closed source
disc it is `f`; outside it is `f` conjugated by reflection in the source and target circles. -/
noncomputable def circleSchwarzReflection (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact (closedBall c r).piecewise f (circleReflectionConjugate c r d s f) z

/-- The circle Schwarz-reflection extension is the explicit inside/outside piecewise function. -/
theorem circleSchwarzReflection_def (c : ℂ) (r : ℝ) (d : ℂ) (s : ℝ) (f : ℂ → ℂ) :
    circleSchwarzReflection c r d s f =
      (by
        classical
        exact (closedBall c r).piecewise f (circleReflectionConjugate c r d s f)) := by
  classical
  funext z
  rw [circleSchwarzReflection]

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

/-- If `Ω` is mapped into itself by inversion in the source circle, the circle-reflection
extension is continuous when the original map is continuous on the closed inside part, maps the
source-circle boundary to the target circle, and avoids the target centre in the punctured open
inside part. -/
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
  rw [circleSchwarzReflection_def]
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
