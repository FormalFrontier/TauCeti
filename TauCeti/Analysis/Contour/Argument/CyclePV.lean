/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.HungerbuhlerWasem
public import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# The argument principle for a cycle running through the zeros

The argument principle in the form that tolerates zeros and poles **on** the contour. For `f`
whose zeros and poles in an open `U` all lie in a finite `S`, and a closed piecewise-`C¹`
*immersion* `γ` null-homologous in `U` and based off `S`, the Cauchy principal value of the
logarithmic integral is

`p.v. ∮_γ f'/f = 2πi · Σ_{z ∈ S} n_z(γ) · ord_z f`,

with the generalized (non-integer) winding numbers as weights. Where
`TauCeti.Contour.argumentPrinciple_nullHomologous` requires `γ` to avoid `S` and produces an
ordinary integral, here `γ` may run through the points of `S` — a zero on the contour is a pole
of `f'/f` on the contour, so the integral exists only as a principal value, and the point
contributes its order weighted by a winding number that need not be an integer. In the standard
configuration — a positively oriented curve with a single smooth branch through the point — that
weight is `1/2`; in general the generalized winding number at such a point is the average of the
two ordinary winding numbers on either side of the branch, so any `k ± 1/2` occurs.

The proof is the Hungerbühler–Wasem residue theorem in its simple-pole regime
(`TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles`) applied to `logDeriv f`,
whose residue at each point is the order of `f` there
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). What that regime asks for is that
`logDeriv f` have at worst a simple pole at each point of `S`, which is
`TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv`: HW's conditions (A′) and (B) are then
automatic, so no regularity hypothesis beyond the immersion survives into the statement. That
bound is not an extra assumption on `f` but a fact about logarithmic derivatives — `f'/f` has a
simple pole at a zero or pole of `f` whatever the order there — which is why the hypotheses below
are those of the classical statement with the avoidance dropped.

Immersion, rather than mere piecewise-`C¹` regularity, is what the principal value at an on-curve
singularity needs: the curve must leave the point at a definite speed for the excised integrals to
converge.

## Main results

* `TauCeti.Contour.hasCauchyPV_logDeriv_nullHomologous` — the principal-value argument principle
  for a cycle through the zeros.

## Provenance

Adapted from the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) valence-formula
development, whose `ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`.../Residue/GeneralizedTheoremBase.lean` apply the generalized residue theorem to `logDeriv f`;
here stated against Mathlib's `meromorphicOrderAt` and the raw-`γ` design of the
contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Set

namespace TauCeti.Contour

/-- **The argument principle for a cycle running through the zeros.** For `f` analytic and
non-vanishing on `U` off a finite `S`, meromorphic of order `ord` at each point of `S` lying in
`U`, and a closed piecewise-`C¹` immersion `γ` in `U`, null-homologous there and based off `S`,

`p.v. ∮_γ f'/f = 2πi · Σ_{z ∈ S} n_z(γ) · ord z`.

Unlike `TauCeti.Contour.argumentPrinciple_nullHomologous`, the curve is free to pass through the
points of `S`: where the order is nonzero `f'/f` then has a pole on the contour, the integral
exists only as a principal value, and the generalized winding number supplies the weight, which
need not be an integer — `1/2` in the standard configuration of a positively oriented curve with
a single smooth branch through the point. Of the curve, only the endpoint `γ a` is required to
avoid `S`; that restriction is inherited from the Hungerbühler–Wasem theorem, not from the
principal value, which excises symmetrically about each singularity.

Nothing is asked of `f` at a point of `S` outside `U`: null-homology forces the winding number
there to vanish, so such a term drops out whatever `ord` says. `S` may equally list regular
non-vanishing points of `f`, whose order is `0`. -/
theorem hasCauchyPV_logDeriv_nullHomologous {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {ord : ℂ → ℤ}
    (hU : IsOpen U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    {γ : ℝ → ℂ} {a b : ℝ} (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hnull : IsNullHomologous γ a b U) :
    HasCauchyPV γ a b (logDeriv f)
      (2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ)) := by
  classical
  -- Only the points of `S` inside `U` can contribute: run the residue theorem on those, and let
  -- null-homology kill the rest.
  set T : Finset ℂ := S.filter (· ∈ U) with hT
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hmemT : ∀ {z : ℂ}, z ∈ T ↔ z ∈ S ∧ z ∈ U := by
    intro z; rw [hT, Finset.mem_filter]
  have hTU : (T : Set ℂ) ⊆ U := fun z hz => (hmemT.mp hz).2
  -- On `U` the two exceptional sets agree, so the off-`S` hypothesis serves `T` unchanged.
  have hUT : U \ (↑T : Set ℂ) = U \ (↑S : Set ℂ) := by
    ext z
    exact ⟨fun hz => ⟨hz.1, fun hzS => hz.2 (hmemT.mpr ⟨hzS, hz.1⟩)⟩,
      fun hz => ⟨hz.1, fun hzT => hz.2 (hTS hzT)⟩⟩
  have hdiff : DifferentiableOn ℂ (logDeriv f) (U \ (↑T : Set ℂ)) := by
    rw [hUT]
    exact fun z hz => (analyticAt_logDeriv_of_analyticAt (hoff z hz.1 hz.2).1
      (hoff z hz.1 hz.2).2).differentiableAt.differentiableWithinAt
  have hmeroT : ∀ s ∈ T, MeromorphicAt f s := fun s hs =>
    hmero s (hTS hs) (hmemT.mp hs).2
  have hmeroL : ∀ s ∈ T, MeromorphicAt (logDeriv f) s := fun s hs =>
    (hmeroT s hs).deriv.div (hmeroT s hs)
  -- `Res_s (f'/f) = ord_s f` inside `U`, and outside it the winding number vanishes.
  have hsum : ∑ s ∈ T, windingNumber γ a b s * residue (logDeriv f) s
      = ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ) := by
    rw [Finset.sum_congr rfl fun s hs => by
      rw [residue_logDeriv_eq_meromorphicOrderAt (hmeroT s hs)
        (hord s (hTS hs) (hmemT.mp hs).2)]]
    refine Finset.sum_subset hTS fun z hzS hzT => ?_
    rw [isNullHomologous_iff.mp hnull z fun hzU => hzT (hmemT.mpr ⟨hzS, hzU⟩), zero_mul]
  rw [← hsum]
  exact hungerbuhlerWasem_residueTheorem_of_simple_poles hU T γ a b hγ_imm hTU hclosed
    (fun h => hγa (hTS h)) hγU hdiff hmeroL hnull fun s hs =>
      neg_one_le_meromorphicOrderAt_logDeriv (hmeroT s hs)

end TauCeti.Contour

end
