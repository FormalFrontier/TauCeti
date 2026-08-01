/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.PolarPart.Decomposition
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.PerWindow.HigherOrder

/-!
# The classical residue theorem for an arbitrary null-homologous cycle

For `f` differentiable on `U ∖ S` and meromorphic at each point of the finite set `S` lying in
`U`, and a **closed, null-homologous** piecewise-`C¹` curve `γ` in `U` that **avoids** `S`,

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

where `n_s(γ)` is the generalized winding number of `γ` about `s`. This is the general
arbitrary-cycle form of the classical residue theorem, and it generalizes the circle theorem
(`Contour.classicalResidueTheorem_circle`): the contour is an arbitrary
piecewise-`C¹` loop rather than a round circle, and each pole is weighted by its winding number
rather than by `1`. Null-homology is not decoration — on a general holomorphy domain `Ω`, a loop
that merely avoids the poles need not integrate to the residue sum (a loop around a hole of `Ω`
sees the function's behaviour there), so `n_w(γ) = 0` for every `w ∉ Ω` is exactly the hypothesis
that rules this out. Its `S = ∅` case is the homology Cauchy theorem, which is why the roadmap
defers this statement past Layer 2.

The proof is the classical three-line argument, over the pieces the repository already has. The
polar-part decomposition (`Contour.PolarPartDecomposition.ofMeromorphic`) writes
`f = g + ∑_{s ∈ S} P_s` on `U ∖ S`, with `g` differentiable on all of `U` and `P_s` the finite
Laurent tail at `s`. The remainder `g` integrates to zero by the homology Cauchy theorem
(`Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_analyticRemainder_eq_zero`). In each
Laurent tail the simple-pole coefficient integrates to `2πi · n_s(γ) · Res_s f`, by the very
definition of the winding number (the principal value collapses to an ordinary integral because
`γ` misses `s`), while every coefficient of order `≥ 2` integrates to zero around the closed
curve, having the primitive `−(k−1)⁻¹(z − s)^{−(k−1)}`
(`Contour.integral_pow_inv_mul_deriv_eq_zero_of_closed`).

Unlike the Hungerbühler–Wasem generalized residue theorem
(`Contour.hungerbuhlerWasem_residueTheorem`), whose singularities may lie *on* the curve, nothing
here needs an immersion, a principal value, or the conditions (A′)/(B): with the poles off the
contour every integral in sight is an ordinary interval integral. Conversely this statement is
*not* a specialization of the HW theorem, which asks for the strictly stronger
`Contour.IsPwC1ImmersionOn` regularity, so a piecewise-`C¹` loop with a zero-speed seam is covered
here and not there.

## Main results

* `TauCeti.Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_polarPart` — the contour
  integral of a polar part around such a curve is `2πi · n_s(γ) · Res_s f`.
* `PolarPartDecomposition.intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue` — the
  residue theorem for a fixed decomposition, assuming nothing about `f` beyond it.
* `TauCeti.Contour.classicalResidueTheorem_nullHomologous` — the residue theorem for an arbitrary
  null-homologous cycle avoiding the poles.

This is the "general arbitrary-cycle case" of the contour-integration roadmap, which that roadmap
defers to Layer 3+.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), §3.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI (the homology form of the residue theorem).

## Provenance

No formal source is vendored: the statement is assembled here from the repository's polar-part
decomposition, homology Cauchy theorem, and antiderivative lemma for higher-order Laurent terms,
which are themselves migrated from the AINTLIB `LeanModularForms` development.
-/

public section

open MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The contour integral of a polar part is the winding-weighted residue.** Around a closed
piecewise-`C¹` curve missing the pole `s`, the finite Laurent tail of `f` at `s` integrates to
`2πi · n_s(γ) · Res_s f`: the simple-pole coefficient contributes the index integral, which is
`2πi` times the generalized winding number since the principal value collapses to an ordinary
integral off the curve, and every higher-order coefficient contributes zero
(`Contour.integral_pow_inv_mul_deriv_eq_zero_of_closed`). -/
theorem intervalIntegral_deriv_smul_polarPart (decomp : PolarPartDecomposition f S U) (s : S)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (h_ne : ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ)) :
    ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b := hγ.intervalIntegrable_deriv
  have hne' : ∀ t ∈ uIcc a b, γ t - (s : ℂ) ≠ 0 := fun t ht => sub_ne_zero.mpr (h_ne t ht)
  have hindex : ∫ t in a..b, (γ t - (s : ℂ))⁻¹ * deriv γ t
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s := by
    rw [windingNumber_eq_integral_of_avoidance hcont h_ne
        (intervalIntegrable_inv_sub_mul_deriv hcont h_ne hderiv), ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  have hterm : ∀ k : Fin (decomp.order s), IntervalIntegrable
      (fun t => decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t) volume a b :=
    fun k => hderiv.continuousOn_mul (continuousOn_const.div
      ((hcont.sub continuousOn_const).pow _) fun t ht => pow_ne_zero _ (hne' t ht))
  have hsplit : ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = ∑ k : Fin (decomp.order s),
          ∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t := by
    rw [← intervalIntegral.integral_finsetSum fun k _ => hterm k]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [smul_eq_mul, mul_comm, decomp.polarPart_eq s (γ t), Finset.sum_mul]
  have hval : ∀ k : Fin (decomp.order s),
      (∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t)
        = if k.val = 0 then
            decomp.coeff s k * (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s)
          else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk_pos
    · rw [if_pos hk0, ← hindex, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hk0]
      ring
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hk_pos)]
      exact integral_pow_inv_mul_deriv_eq_zero_of_closed (by omega) _ hγ hclosed h_ne
  rw [hsplit, Finset.sum_congr rfl fun k _ => hval k, decomp.sum_ite_coeff_eq_residue_mul s]
  ring

/-- **The residue theorem for a fixed polar-part decomposition.** Once `f` is presented on `U` as
an analytic remainder plus finite Laurent tails at the points of `S`, a closed null-homologous
piecewise-`C¹` curve in `U` avoiding `S` integrates to the winding-weighted residue sum. This is
the sum of the two preceding facts: the remainder contributes nothing
(`intervalIntegral_deriv_smul_analyticRemainder_eq_zero`) and the tail at `s` contributes
`2πi · n_s(γ) · Res_s f` (`intervalIntegral_deriv_smul_polarPart`).

Nothing is assumed about `f` beyond the decomposition itself: no differentiability or meromorphy
hypothesis appears, a decomposition already carrying everything the argument uses. When `decomp`
is obtained from `ofMeromorphic`, those hypotheses were consumed there. -/
theorem intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b := hγ.intervalIntegrable_deriv
  have hne : ∀ s : S, ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ) := fun s t ht h_eq =>
    hoff t ht (h_eq ▸ Finset.mem_coe.mpr s.2)
  have hpol_cont : ∀ s : S, ContinuousOn (fun t => decomp.polarPart s (γ t)) (uIcc a b) :=
    fun s => ContinuousOn.congr
      (continuousOn_finsetSum Finset.univ fun k _ => continuousOn_const.div
        ((hcont.sub continuousOn_const).pow (k.val + 1))
        fun t ht => pow_ne_zero _ (sub_ne_zero.mpr (hne s t ht)))
      fun t _ => decomp.polarPart_eq s (γ t)
  have hrem_int : IntervalIntegrable
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)) volume a b :=
    hderiv.smul_continuousOn
      (decomp.analyticRemainder_differentiableOn.continuousOn.comp hcont hγU)
  have hpol_int : ∀ s ∈ S.attach, IntervalIntegrable
      (fun t => deriv γ t • decomp.polarPart s (γ t)) volume a b :=
    fun s _ => hderiv.smul_continuousOn (hpol_cont s)
  have hsum_int : IntervalIntegrable
      (fun t => ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) volume a b := by
    have h := IntervalIntegrable.sum S.attach hpol_int
    rwa [Finset.sum_fn] at h
  have hf_eq : EqOn (fun t => deriv γ t • f (γ t))
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)
        + ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) (uIcc a b) := fun t ht => by
    simp only
    rw [decomp.f_eq (γ t) ⟨hγU t ht, hoff t ht⟩, smul_add, Finset.smul_sum]
  rw [intervalIntegral.integral_congr hf_eq, intervalIntegral.integral_add hrem_int hsum_int,
    intervalIntegral.integral_finsetSum hpol_int,
    decomp.intervalIntegral_deriv_smul_analyticRemainder_eq_zero hU hγ hγU hclosed hnull,
    zero_add, Finset.sum_congr rfl fun s _ =>
      decomp.intervalIntegral_deriv_smul_polarPart s hγ hclosed (hne s),
    Finset.mul_sum, ← Finset.sum_attach S
      fun s => 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b s * residue f s)]
  exact Finset.sum_congr rfl fun s _ => by ring

end PolarPartDecomposition

/-- **The classical residue theorem for an arbitrary null-homologous cycle.** Let `U` be open,
`S` a finite set, `f` differentiable on `U ∖ S` and meromorphic at each point of `S` lying in `U`,
and let `γ` be a closed piecewise-`C¹` curve in `U`, **null-homologous** in `U`, that **avoids**
`S`. Then

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

each pole weighted by the generalized winding number of `γ` about it.

Points of `S` outside `U` are harmless rather than excluded: null-homology forces their winding
number, hence their contribution, to vanish, so nothing at all is asked of `f` there —
meromorphicity is required only at the points of `S` that lie in `U`. Likewise `S` may list
regular points of `f`, whose residues are `0`.

Its `S = ∅` case is the homology Cauchy theorem (`Contour.homologyCauchyTheorem`), so this is
genuinely a Layer 3 statement; the round-circle case with the poles inside is
`Contour.classicalResidueTheorem_circle`, and the version admitting poles *on* the curve is the
Hungerbühler–Wasem theorem `Contour.hungerbuhlerWasem_residueTheorem`. -/
theorem classicalResidueTheorem_nullHomologous {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  classical
  -- Replace `S` by the part `T` of it lying in `U`, where `f` is meromorphic: a point outside `U`
  -- has winding number `0` by null-homology, so it drops out of the sum for free.
  obtain ⟨T, hTS, hfT, hmeroT, hsum⟩ : ∃ T : Finset ℂ, (∀ s ∈ T, s ∈ S) ∧
      DifferentiableOn ℂ f (U \ (↑T : Set ℂ)) ∧ (∀ s ∈ T, MeromorphicAt f s) ∧
      (∑ s ∈ S, windingNumber γ a b s * residue f s)
        = ∑ s ∈ T, windingNumber γ a b s * residue f s :=
    ⟨S.filter (· ∈ U), fun _ hs => (Finset.mem_filter.mp hs).1,
      hf.mono fun z hz => ⟨hz.1, fun hzS =>
        hz.2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hzS, hz.1⟩))⟩,
      fun s hs => hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2,
      (Finset.sum_filter_of_ne fun s _ hs => not_not.mp fun hsU =>
        hs (by rw [isNullHomologous_iff.mp hnull s hsU, zero_mul])).symm⟩
  rw [hsum]
  exact PolarPartDecomposition.intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue
    (.ofMeromorphic hU hfT hmeroT) hU hγ hγU hclosed
    (fun t ht h => hoff t ht (Finset.mem_coe.mpr (hTS _ (Finset.mem_coe.mp h)))) hnull

end TauCeti.Contour

end
