/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Concat
import TauCeti.Analysis.Contour.Crossing.Finiteness
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Basic
import TauCeti.Analysis.Contour.HungerbuhlerWasem
import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# A simple pole on the contour: the half-residue on a half-disc boundary

The Hungerbühler–Wasem generalized residue theorem applied to a concrete contour and a concrete
integrand. The contour is `halfDiscBoundary R` — the real diameter `[-R, R]` followed by the
upper semicircle of radius `R` — which passes *through* the origin rather than around it, so the
classical residue theorem does not apply: the integral only exists as a Cauchy principal value,
and the origin is a boundary point of the region rather than an interior one.

What replaces the classical statement is the **half-residue**: because the contour crosses the
singularity smoothly, its generalized winding number there is `½` rather than `0` or `1`
(`windingNumber_halfDiscBoundary`), and the principal value picks up `π i · Res` instead of
`2π i · Res`. This is HW's motivating example, and the acceptance test for the whole
development: every hypothesis of `hasCauchyPV_half_residue_of_simple_pole` is discharged here
from the geometry of an explicit curve.

The null-homology hypothesis is vacuous because the ambient region is all of `ℂ`, which has no
exterior points; conditions (A′) and (B) are supplied by the simple-pole form of the theorem,
which derives them from the pole order. For a pole of *higher* order the general form is the one
to use, and `conditionAprime_halfDiscBoundary` already discharges its condition (A′) — the
half-disc is flat to every order at the origin, so it meets (A′) whatever the pole. Condition (B)
is independent and would still have to be established separately for that integrand.

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

/-- **The half-residue theorem on the half-disc boundary.** If `f` is holomorphic off the origin
and has at worst a simple pole there (the hypotheses also permit a removable singularity, or
`f` holomorphic at `0`, in which case the residue is `0`), then along the half-disc boundary —
which passes *through*
the origin — the Cauchy principal value of `∫ f` is `π i · residue f 0`: half of what the classical
residue theorem would give for a pole enclosed by the contour, because the generalized winding
number at a smooth crossing is `½`. -/
theorem hasCauchyPV_halfDiscBoundary_of_simple_pole {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (halfDiscBoundary R) (-R) (R + Real.pi) f
      ((Real.pi : ℂ) * Complex.I * residue f 0) := by
  have hbase : halfDiscBoundary R (-R) ≠ 0 := by
    rw [halfDiscBoundary_left hR.le]
    simp [hR.ne']
  refine hasCauchyPV_half_residue_of_simple_pole isOpen_univ (halfDiscBoundary R) (-R)
    (R + Real.pi) 0 (isPwC1ImmersionOn_halfDiscBoundary hR) (mem_univ 0) ?_ hbase
    (fun t _ => mem_univ _) hf hmero (isNullHomologous_univ _ _ _) h_simple
    (windingNumber_halfDiscBoundary hR)
  rw [halfDiscBoundary_left hR.le, halfDiscBoundary_right]

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
`f z = e^{iz}/z`, where that bound is `1/R`, is the Hungerbühler–Wasem motivating example. -/
theorem hasCauchyPV_halfDiscBoundary_diameter {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (halfDiscBoundary R) (-R) R f
      ((Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  have hpi := Real.pi_pos
  have hsub : Set.uIcc R (R + Real.pi) ⊆ Set.uIcc (-R) (R + Real.pi) :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)) Set.right_mem_uIcc
  -- On the arc the contour stays off the origin, so `f` is continuous along it and the
  -- integrand is integrable there: a continuous factor times the piecewise-`C¹` derivative.
  have hne : ∀ t ∈ Set.uIcc R (R + Real.pi), halfDiscBoundary R t ≠ 0 := by
    intro t ht h0
    rw [Set.uIcc_of_le (by linarith)] at ht
    have := (halfDiscBoundary_eq_zero_iff hR).mp h0
    linarith [ht.1]
  have hcont : ContinuousOn (fun t => f (halfDiscBoundary R t)) (Set.uIcc R (R + Real.pi)) :=
    hf.continuousOn.comp (continuous_halfDiscBoundary R).continuousOn
      fun t ht => ⟨Set.mem_univ _, hne t ht⟩
  have h_arc : IntervalIntegrable
      (fun t => f (halfDiscBoundary R t) * deriv (halfDiscBoundary R) t)
      MeasureTheory.volume R (R + Real.pi) :=
    (((isPwC1ImmersionOn_halfDiscBoundary hR).isPiecewiseC1On.intervalIntegrable_deriv).mono_set
      hsub).continuousOn_mul hcont
  -- The half-residue theorem's excision set is existentially bound, so name it and supply the
  -- arc piece for that same witness before subtracting.
  obtain ⟨S, hS⟩ := hasCauchyPV_iff_exists_hasCauchyPVWith.mp
    (hasCauchyPV_halfDiscBoundary_of_simple_pole hR hf hmero h_simple)
  have harc : HasCauchyPVWith (halfDiscBoundary R) R (R + Real.pi) f S
      (∫ t in R..(R + Real.pi),
        f (halfDiscBoundary R t) * deriv (halfDiscBoundary R) t) :=
    .of_integrable_of_finite_crossings S
      (continuous_halfDiscBoundary R).measurable.aemeasurable h_arc
      fun s _ => ((isPwC1ImmersionOn_halfDiscBoundary hR).finite_crossings (z₀ := s)).subset
        (Set.inter_subset_inter_left _ (Set.uIoc_subset_uIcc.trans hsub))
  simpa [integral_halfDiscBoundary_arc] using (hS.sub_right harc).hasCauchyPV

/-- **The identity along the real segment.** The diameter of the half-disc traces the straight
line `t ↦ t`, so the principal value can be stated along that curve directly — the form the
real-axis improper integral consumes, with no reference to the auxiliary contour. -/
theorem hasCauchyPV_realSegment_diameter {f : ℂ → ℂ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (univ \ {0})) (hmero : MeromorphicAt f 0)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f 0) :
    HasCauchyPV (fun t : ℝ => (t : ℂ)) (-R) R f
      ((Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  refine (hasCauchyPV_halfDiscBoundary_diameter hR hf hmero h_simple).congr_curve fun t ht => ?_
  rw [Set.uIoo_of_le (by linarith)] at ht
  exact halfDiscBoundary_of_le ht.2.le

end TauCeti.Contour

end

end
