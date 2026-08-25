/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Basic
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Poles
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# A possible singularity on the contour: the half-residue on a half-disc boundary

The pure on-contour case of `WorkedExamples/HalfDisc/Poles.lean`: an integrand whose only possible
singularity is at the origin, where it is at worst a simple pole and where the half-disc contour
passes straight through. Nothing is enclosed, so the result is the **half-residue** identity: the
origin's generalized winding number is `½` (`windingNumber_halfDiscBoundary`), and its contribution
is `π i · Res`. When the singularity is a genuine simple pole, rather than removable or regular,
this is half the `2π i · Res` contribution of an enclosed pole and is Hungerbühler–Wasem's
motivating example.

Each statement here is the `S = ∅` case of its counterpart in `HalfDisc/Poles.lean`, restated
without the (then empty) sum over enclosed poles because that is the shape the Dirichlet-integral
evaluation downstream consumes.

## Main results

* `TauCeti.Contour.hasCauchyPV_halfDiscBoundary_of_simple_pole` — for any `f` holomorphic off
  the origin with at worst a simple pole there, the principal value of `∫_γ f` along the
  half-disc boundary is `π i · residue f 0`.
* `TauCeti.Contour.hasCauchyPV_halfDiscBoundary_inv` — the concrete instance `f z = z⁻¹`, whose
  principal value is exactly `π i`.
* `TauCeti.Contour.hasCauchyPV_halfDiscBoundary_diameter` — the same identity with the arc
  contribution subtracted off, leaving the principal value along the diameter and an explicit
  `circleMap` integral for the arc, the form Jordan's lemma bounds.
* `TauCeti.Contour.hasCauchyPV_realSegment_diameter` — the same, restated along the straight line
  `t ↦ t`, which is the form a real-axis improper integral consumes.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Thm 3.3.
* P. Henrici, *Applied and Computational Complex Analysis*, Thm 4.8f.
-/

public section

noncomputable section

open Complex Set

namespace TauCeti.Contour

variable {R : ℝ}

/-- The `S = ∅` hypotheses of `hasCauchyPV_halfDiscBoundary_of_simple_poles`, repackaged from the
single-singularity form: `insert 0 ∅` is the singleton `{0}`. -/
private theorem simplePole_hypotheses {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    DifferentiableOn ℂ f (univ \ ((insert (0 : ℂ) (∅ : Finset ℂ) : Finset ℂ) : Set ℂ)) ∧
      (∀ s ∈ insert (0 : ℂ) (∅ : Finset ℂ), MeromorphicAt f s) ∧
      (∀ s ∈ insert (0 : ℂ) (∅ : Finset ℂ),
        ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) := by
  refine ⟨by simpa using hf, ?_, ?_⟩ <;>
    · intro s hs
      have hs0 : s = 0 := by simpa using hs
      rw [hs0]
      assumption

/-- **The half-residue theorem on the half-disc boundary.** If `f` is holomorphic off the origin
and has at worst a simple pole there (the hypotheses also permit a removable singularity, or
`f` holomorphic at `0`, in which case the residue is `0`), then along the half-disc boundary —
which passes *through* the origin — the Cauchy principal value of `∫ f` is `π i · residue f 0`:
half of what the classical residue theorem would give for a pole enclosed by the contour, because
the generalized winding number at a smooth crossing is `½`.

This is `hasCauchyPV_halfDiscBoundary_of_simple_poles` with no enclosed poles. -/
theorem hasCauchyPV_halfDiscBoundary_of_simple_pole {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (halfDiscBoundary R) (-R) (R + Real.pi) f
      ((Real.pi : ℂ) * Complex.I * residue f 0) := by
  obtain ⟨hf', hmero', hsimple'⟩ := simplePole_hypotheses hf hmero h_simple
  simpa using
    hasCauchyPV_halfDiscBoundary_of_simple_poles (S := ∅) hR (by simp) hf' hmero' hsimple'

/-- **The motivating example**: the principal value of `∫ dz / z` along the half-disc
boundary is `π i`. The pole sits *on* the contour, so the classical residue theorem does not
apply and the integral exists only as a principal value; the generalized theorem evaluates it as
half the enclosed-pole answer `2π i`. -/
theorem hasCauchyPV_halfDiscBoundary_inv (hR : 0 < R) :
    HasCauchyPV (halfDiscBoundary R) (-R) (R + Real.pi) (fun z => z⁻¹)
      ((Real.pi : ℂ) * Complex.I) := by
  -- `z⁻¹` is the elementary simple pole `(z - 0)⁻¹`: `Residue/SimplePole.lean` supplies its
  -- meromorphy and its residue, and Mathlib's `meromorphicOrderAt_zpow_id_sub_const` its order.
  have hfun : (fun z : ℂ => (z - 0)⁻¹) = fun z : ℂ => z⁻¹ := by simp
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (univ \ {0}) := fun z hz =>
    (differentiableAt_inv (by simpa using hz.2)).differentiableWithinAt
  have hmero : MeromorphicAt (fun z : ℂ => z⁻¹) 0 := hfun ▸ meromorphicAt_sub_inv 0
  have hzpow : (fun z : ℂ => z⁻¹) = fun z : ℂ => (z - 0) ^ (-1 : ℤ) := by
    funext z; simp
  have horder : meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 = -1 := by
    rw [hzpow]; exact meromorphicOrderAt_zpow_id_sub_const
  have hres : residue (fun z : ℂ => z⁻¹) 0 = 1 := by rw [← hfun]; exact residue_sub_inv 0
  have key := hasCauchyPV_halfDiscBoundary_of_simple_pole hR hdiff hmero (by simp [horder])
  rwa [hres, mul_one] at key

/-- **Splitting the half-disc: the diameter piece.** Subtracting the arc contribution from the
half-residue identity leaves the principal value along the diameter alone.

The arc term is expressed as a `circleMap` integral, which is the form Jordan's lemma bounds. It
vanishes as `R → ∞` for an integrand `e^{iaz} · g z` (`a > 0`) whose sup bound on the semicircle
tends to `0` — oscillation alone is not enough, the amplitude must decay. The concrete case
`f z = e^{iz}/z`, where that bound is `1/R`, is the Hungerbühler–Wasem motivating example.

This is `hasCauchyPV_halfDiscBoundary_diameter_of_simple_poles` with no enclosed poles. -/
theorem hasCauchyPV_halfDiscBoundary_diameter {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (halfDiscBoundary R) (-R) R f
      ((Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  obtain ⟨hf', hmero', hsimple'⟩ := simplePole_hypotheses hf hmero h_simple
  simpa using hasCauchyPV_halfDiscBoundary_diameter_of_simple_poles (S := ∅) hR (by simp)
    hf' hmero' hsimple'

/-- **The identity along the real segment.** The diameter of the half-disc traces the straight
line `t ↦ t`, so the principal value can be stated along that curve directly — the form the
real-axis improper integral consumes, with no reference to the auxiliary contour.

This is `hasCauchyPV_realSegment_of_simple_poles` with no enclosed poles. -/
theorem hasCauchyPV_realSegment_diameter {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (fun t : ℝ => (t : ℂ)) (-R) R f
      ((Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  obtain ⟨hf', hmero', hsimple'⟩ := simplePole_hypotheses hf hmero h_simple
  simpa using hasCauchyPV_realSegment_of_simple_poles (S := ∅) hR (by simp) hf' hmero' hsimple'

end TauCeti.Contour

end

end
