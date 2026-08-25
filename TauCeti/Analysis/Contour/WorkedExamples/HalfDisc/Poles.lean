/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Basic
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Concat
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.HungerbuhlerWasem
import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Winding

/-!
# The half-disc residue theorem

The Hungerbühler–Wasem generalized residue theorem, run on the boundary of the upper half-disc of
radius `R` about the origin -- the contour of `WorkedExamples/HalfDisc/Basic.lean`, which passes
*through* the origin instead of detouring around it. With the winding numbers of
`WorkedExamples/HalfDisc/Winding.lean` -- `1` in the open upper half-disc, `½` at the origin, `0`
outside -- the principal value of `∮ f` along that contour is

`2π i · Σ_{s ∈ S} Res_s f + π i · Res₀ f`

for `f` holomorphic off `insert 0 S` with at worst simple poles there and `S` inside the half-disc:
each enclosed possible singularity contributes its full residue, while the possible singularity
*on* the contour contributes only half of its own. In the nonremovable simple-pole case at the
origin, the classical residue theorem cannot reach the second term at all, because the pole lies on
the path of integration and only a principal-value integral exists.

The `S = ∅` case, where the origin is the only prescribed point, is
`WorkedExamples/HalfDisc/HalfResidue.lean`; when `f` is regular at the origin, the result reduces to
the classical residue theorem for this contour.

The possible singularity on the real axis is pinned at the origin, as throughout the half-disc
development: the contour `halfDiscBoundary` is centred there, and a possible real singularity
elsewhere is reached by centring the contour on it instead. Every prescribed singularity is
required to be at worst simple, which is what makes the Hungerbühler–Wasem conditions (A′) and (B)
automatic.

## Main results

* `TauCeti.Contour.hasCauchyPV_halfDiscBoundary_of_simple_poles` — the principal value along the
  half-disc boundary, with possible enclosed singularities and a possible singularity at the
  origin on the contour.
* `TauCeti.Contour.hasCauchyPV_halfDiscBoundary_diameter_of_simple_poles` — the same with the arc
  contribution subtracted off, leaving the principal value along the diameter and an explicit
  `circleMap` integral for the arc, the form Jordan's lemma bounds.
* `TauCeti.Contour.hasCauchyPV_realSegment_of_simple_poles` — the same restated along the straight
  line `t ↦ t`, the form a real-axis improper integral consumes.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Thm 3.3.
* P. Henrici, *Applied and Computational Complex Analysis, Volume 1: Power Series—Integration—
  Conformal Mapping—Location of Zeros*, Wiley, 1974, Thm 4.8f.
-/

public section

noncomputable section

open Complex Set

namespace TauCeti.Contour

variable {R : ℝ} {S : Finset ℂ}

/-- The origin is not one of the prescribed enclosed points: those lie strictly above the real
axis. -/
private theorem zero_notMem_of_im_pos (hS : ∀ s ∈ S, 0 < s.im ∧ ‖s‖ < R) : (0 : ℂ) ∉ S :=
  fun h => absurd (hS 0 h).1 (by simp)

/-- **The half-disc residue theorem with enclosed possible singularities.** Let `f` be holomorphic
off the finite set `insert 0 S`, with at worst a simple singularity at each of its points, and let
every point of `S` lie in the open upper half-disc of radius `R`. Then the Cauchy principal value of
`∮ f` along the half-disc boundary is

`2π i · Σ_{s ∈ S} Res_s f + π i · Res₀ f`:

each enclosed possible singularity contributes its full residue, because the generalized winding
number there is `1`, while the possible singularity *on* the contour contributes only half of its
own. In the genuine simple-pole case, this is the half-residue contribution from the winding number
`½` at a smooth crossing. -/
theorem hasCauchyPV_halfDiscBoundary_of_simple_poles {f : ℂ → ℂ} (hR : 0 < R)
    (hS : ∀ s ∈ S, 0 < s.im ∧ ‖s‖ < R)
    (hf : DifferentiableOn ℂ f (univ \ (insert (0 : ℂ) S : Finset ℂ)))
    (hmero : ∀ s ∈ insert (0 : ℂ) S, MeromorphicAt f s)
    (h_simple : ∀ s ∈ insert (0 : ℂ) S,
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV (halfDiscBoundary R) (-R) (R + Real.pi) f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) +
        (Real.pi : ℂ) * Complex.I * residue f 0) := by
  have hbase : halfDiscBoundary R (-R) ∉ ((insert (0 : ℂ) S : Finset ℂ) : Set ℂ) := by
    rw [halfDiscBoundary_left hR.le]
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
    refine ⟨by simpa using hR.ne', fun hmem => ?_⟩
    have := (hS _ hmem).1
    simp at this
  have hclosed : halfDiscBoundary R (-R) = halfDiscBoundary R (R + Real.pi) :=
    (halfDiscBoundary_left hR.le).trans (halfDiscBoundary_right R).symm
  have key := hungerbuhlerWasem_residueTheorem_of_simple_poles isOpen_univ
    (insert (0 : ℂ) S) (halfDiscBoundary R) (-R) (R + Real.pi)
    (isPwC1ImmersionOn_halfDiscBoundary hR) (subset_univ _) hclosed hbase
    (fun t _ => mem_univ _) hf hmero (isNullHomologous_univ _ _ _) h_simple
  rw [Finset.sum_insert (zero_notMem_of_im_pos hS), windingNumber_halfDiscBoundary hR,
    Finset.sum_congr rfl (fun s hs => by
      rw [windingNumber_halfDiscBoundary_eq_one (hS s hs).1 (hS s hs).2, one_mul])] at key
  have hvalue : 2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) +
      (Real.pi : ℂ) * Complex.I * residue f 0
      = 2 * (Real.pi : ℂ) * Complex.I * (1 / 2 * residue f 0 + ∑ s ∈ S, residue f s) := by
    ring
  rw [hvalue]
  exact key

/-- **Splitting off the arc.** Subtracting the arc contribution from the principal value along the
whole half-disc boundary leaves the principal value along the diameter alone, with the arc
expressed as a `circleMap` integral — the form Jordan's lemma bounds when the radius grows. -/
theorem hasCauchyPV_halfDiscBoundary_diameter_of_simple_poles {f : ℂ → ℂ} (hR : 0 < R)
    (hS : ∀ s ∈ S, 0 < s.im ∧ ‖s‖ < R)
    (hf : DifferentiableOn ℂ f (univ \ (insert (0 : ℂ) S : Finset ℂ)))
    (hmero : ∀ s ∈ insert (0 : ℂ) S, MeromorphicAt f s)
    (h_simple : ∀ s ∈ insert (0 : ℂ) S,
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV (halfDiscBoundary R) (-R) R f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) +
        (Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  have hpi := Real.pi_pos
  have hsub : uIcc R (R + Real.pi) ⊆ uIcc (-R) (R + Real.pi) :=
    uIcc_subset_uIcc (mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)) right_mem_uIcc
  -- On the arc the contour has norm `R`, so it misses every prescribed singularity.
  have hne : ∀ t ∈ uIcc R (R + Real.pi),
      halfDiscBoundary R t ∈ univ \ ((insert (0 : ℂ) S : Finset ℂ) : Set ℂ) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hnorm : ‖halfDiscBoundary R t‖ = R := norm_halfDiscBoundary_eq hR.le ht.1
    refine ⟨mem_univ _, ?_⟩
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
    refine ⟨fun h0 => ?_, fun hmem => ?_⟩
    · rw [h0] at hnorm
      simp only [norm_zero] at hnorm
      exact hR.ne hnorm
    · have hlt := (hS _ hmem).2
      rw [hnorm] at hlt
      exact absurd hlt (lt_irrefl R)
  have hcont : ContinuousOn (fun t => f (halfDiscBoundary R t)) (uIcc R (R + Real.pi)) :=
    hf.continuousOn.comp (continuous_halfDiscBoundary R).continuousOn hne
  have h_arc : IntervalIntegrable
      (fun t => f (halfDiscBoundary R t) * deriv (halfDiscBoundary R) t)
      MeasureTheory.volume R (R + Real.pi) :=
    (((isPwC1ImmersionOn_halfDiscBoundary hR).isPiecewiseC1On.intervalIntegrable_deriv).mono_set
      hsub).continuousOn_mul hcont
  obtain ⟨T, hT⟩ := hasCauchyPV_iff_exists_hasCauchyPVWith.mp
    (hasCauchyPV_halfDiscBoundary_of_simple_poles hR hS hf hmero h_simple)
  have harc : HasCauchyPVWith (halfDiscBoundary R) R (R + Real.pi) f T
      (∫ t in R..(R + Real.pi),
        f (halfDiscBoundary R t) * deriv (halfDiscBoundary R) t) :=
    .of_integrable_of_finite_crossings T
      (continuous_halfDiscBoundary R).measurable.aemeasurable h_arc
      fun s _ => ((isPwC1ImmersionOn_halfDiscBoundary hR).finite_crossings (z₀ := s)).subset
        (inter_subset_inter_left _ (uIoc_subset_uIcc.trans hsub))
  simpa [integral_halfDiscBoundary_arc] using (hT.sub_right harc).hasCauchyPV

/-- **The identity along the real segment.** The diameter of the half-disc traces the straight line
`t ↦ t`, so the principal value can be stated along that curve directly — the form a real-axis
improper integral consumes, with no reference to the auxiliary contour. Letting `R → ∞` with an
arc bound (Jordan's lemma, say) turns this into an improper-integral evaluation that the classical
residue theorem cannot reach when the origin is a genuine pole on the line of integration. -/
theorem hasCauchyPV_realSegment_of_simple_poles {f : ℂ → ℂ} (hR : 0 < R)
    (hS : ∀ s ∈ S, 0 < s.im ∧ ‖s‖ < R)
    (hf : DifferentiableOn ℂ f (univ \ (insert (0 : ℂ) S : Finset ℂ)))
    (hmero : ∀ s ∈ insert (0 : ℂ) S, MeromorphicAt f s)
    (h_simple : ∀ s ∈ insert (0 : ℂ) S,
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV (fun t : ℝ => (t : ℂ)) (-R) R f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) +
        (Real.pi : ℂ) * Complex.I * residue f 0 -
        ∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
  refine (hasCauchyPV_halfDiscBoundary_diameter_of_simple_poles hR hS hf hmero
    h_simple).congr_curve fun t ht => ?_
  rw [uIoo_of_le (by linarith)] at ht
  exact halfDiscBoundary_of_le ht.2.le

end TauCeti.Contour

end

end
