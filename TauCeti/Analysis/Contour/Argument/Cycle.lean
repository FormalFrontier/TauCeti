/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.IsolatedZero
public import TauCeti.Analysis.Contour.Residue.Cycle
public import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# The argument principle for an arbitrary null-homologous cycle

For `f` with all its zeros and poles inside a finite set `S`, and a closed piecewise-`C¹` curve
`γ` that is **null-homologous** in the holomorphy domain `U` and avoids `S`,

`∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · ∑_{z ∈ S} n_z(γ) · ord_z f`,

where `n_z(γ)` is the generalized winding number of `γ` about `z` and `ord_z f` is
`meromorphicOrderAt f z` — positive at a zero, negative at a pole. This is the arbitrary-cycle
form of the argument principle: the roadmap's Layer-2 statement
`TauCeti.Contour.argumentPrinciple` fixes the contour to be a round circle with every special
point strictly inside, so each order is counted exactly once; here the contour is any
piecewise-`C¹` loop and each order is counted with the multiplicity with which the loop winds
around it.

The proof is the classical one-liner over the two pieces the repository already has: the residue
theorem for a null-homologous cycle (`TauCeti.Contour.classicalResidueTheorem_nullHomologous`)
applied to `logDeriv f`, whose residue at each point is the order of `f` there
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). What has to be supplied is the input
regularity of `logDeriv f` rather than of `f`: off `S` the logarithmic derivative is holomorphic
because `f` is analytic *and non-vanishing* there (a zero of `f` is a pole of `logDeriv f`, which
is exactly why the hypothesis asks `S` to collect the zeros as well as the poles), and at each
point of `S` it is meromorphic because `f` is.

Null-homology is load-bearing, as it already is for the residue theorem: on a domain with a hole
a loop that merely avoids the zeros and poles can still see the function's behaviour in the hole,
and `n_w(γ) = 0` for every `w ∉ U` is exactly the hypothesis that rules this out.

Unlike the circle statement, no pointwise "wrong values" of `f` are tolerated. The circle proof
may replace `f` by its meromorphic normal form because a circle integral is unchanged by a change
of integrand on a set codiscrete within the sphere
(`circleIntegral.circleIntegral_congr_codiscreteWithin`); no such congruence is available for a
general piecewise-`C¹` contour, and the null-homologous residue theorem used here asks for honest
differentiability of `logDeriv f` on `U ∖ S`. Accordingly the hypotheses here ask for genuine
analyticity of `f` off `S`.

## Main results

* `TauCeti.Contour.argumentPrinciple_nullHomologous` — the argument principle for a closed
  null-homologous piecewise-`C¹` cycle: `∮_γ f'/f = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`.
* `TauCeti.Contour.argumentPrinciple_nullHomologous_local` — the one-point case
  `∮_γ f'/f = 2πi · n_{z₀}(γ) · n`, the arbitrary-cycle counterpart of
  `TauCeti.Contour.argumentPrinciple_local`.
* `TauCeti.Contour.argumentPrinciple_nullHomologous_of_analyticOnNhd` — the zero-counting
  specialisation: for `f` analytic on `U` whose zeros lie in a finite `S`,
  `∮_γ f'/f = 2πi · ∑_{z ∈ S} n_z(γ) · analyticOrderNatAt f z`, the winding-weighted count of the
  zeros of `f` with multiplicity.

This is the arbitrary-cycle upgrade of a Layer-2 target of the contour-integration roadmap; like
the residue theorem it rests on it, it is a Layer-3 statement, since its hypotheses and its proof
go through the homology Cauchy theorem.

## Provenance

No formal source is vendored: the statement is assembled here from the repository's residue
theorem for a null-homologous cycle and the local residue-form of the argument principle, which
are themselves migrated from the AINTLIB `LeanModularForms` development (where the residue
theorem is applied to `logDeriv f`).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018).
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI, §1 (the argument principle in its homology form).
-/

public section

open Set

open scoped Interval

namespace TauCeti.Contour

/-- **The argument principle for an arbitrary null-homologous cycle.** Let `U` be open, `S` a
finite set collecting every zero and pole of `f` in `U`: `f` is analytic and non-vanishing at each
point of `U ∖ S`, and meromorphic of order `ord s` at each `s ∈ S` lying in `U`. Let `γ` be a
closed piecewise-`C¹` curve in `U`, **null-homologous** in `U`, that **avoids** `S`. Then the
contour integral of the logarithmic derivative counts the orders, each weighted by the winding
number of `γ` about it:

`∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`.

Since `ord` is positive at a zero and negative at a pole, this is `2πi` times the number of zeros
minus poles counted with multiplicity *and* with winding multiplicity — for a simple loop
enclosing them once, the classical zero-minus-pole count.

As in `TauCeti.Contour.classicalResidueTheorem_nullHomologous`, points of `S` outside `U` are
harmless rather than excluded: null-homology forces their winding number, hence their
contribution, to vanish, so nothing is asked of `f` there. Likewise `S` may list regular
non-vanishing points of `f`, whose order is `0`.

The round-circle case, which asks nothing pointwise of `f` because it may pass to the meromorphic
normal form, is `TauCeti.Contour.argumentPrinciple`. -/
theorem argumentPrinciple_nullHomologous {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ} {ord : ℂ → ℤ}
    (hU : IsOpen U) (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ) := by
  -- Off `S` the function is analytic and non-vanishing, so its logarithmic derivative is
  -- holomorphic there; at a point of `S` it is meromorphic, being `deriv f / f`.
  have hdiff : DifferentiableOn ℂ (logDeriv f) (U \ (↑S : Set ℂ)) := fun z hz =>
    (analyticAt_logDeriv_of_analyticAt (hoff z hz.1 hz.2).1
      (hoff z hz.1 hz.2).2).differentiableAt.differentiableWithinAt
  have hmeroL : ∀ s ∈ S, s ∈ U → MeromorphicAt (logDeriv f) s := fun s hs hsU =>
    (hmero s hs hsU).deriv.div (hmero s hs hsU)
  rw [classicalResidueTheorem_nullHomologous hU hdiff hmeroL hγ hγU hclosed hγoff hnull]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  by_cases hsU : s ∈ U
  · -- `Res_s (f'/f) = ord_s f`.
    rw [residue_logDeriv_eq_meromorphicOrderAt (hmero s hs hsU) (hord s hs hsU)]
  · -- A point outside `U` has winding number `0`, so both summands vanish.
    rw [isNullHomologous_iff.mp hnull s hsU, zero_mul, zero_mul]

/-- **The argument principle for a cycle around a single zero or pole.** If `z₀` is the only point
of an open `U` at which `f` fails to be analytic and non-vanishing, of order `n` there, and `γ` is a
closed piecewise-`C¹` curve in `U`, null-homologous in `U`, missing `z₀`, then

`∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · n_{z₀}(γ) · n`.

This is the `S = {z₀}` case of `TauCeti.Contour.argumentPrinciple_nullHomologous`, and the
arbitrary-cycle counterpart of `TauCeti.Contour.argumentPrinciple_local`: a loop winding `k` times
around a zero of order `n` integrates `f'/f` to `2πi · k · n`.

Membership `z₀ ∈ U` is not required, and nothing at all is asked of `f` at `z₀` unless it holds:
if `z₀` lies outside `U` then `f` is analytic and non-vanishing on all of `U`, and null-homology
makes `n_{z₀}(γ)` vanish, so both sides are `0` for any `n`. Accordingly the meromorphy and the
order hypotheses are conditional on `z₀ ∈ U`, exactly as they are in
`TauCeti.Contour.argumentPrinciple_nullHomologous`. -/
theorem argumentPrinciple_nullHomologous_local {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {n : ℤ}
    (hU : IsOpen U) (hmero : z₀ ∈ U → MeromorphicAt f z₀)
    (hn : z₀ ∈ U → meromorphicOrderAt f z₀ = (n : WithTop ℤ))
    (hoff : ∀ z ∈ U, z ≠ z₀ → AnalyticAt ℂ f z ∧ f z ≠ 0)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, γ t ≠ z₀) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b z₀ * (n : ℂ)) := by
  have key := argumentPrinciple_nullHomologous (S := {z₀}) (ord := fun _ => n) hU
    (fun z hzU hzS => hoff z hzU (by simpa using hzS))
    (fun s hs hsU => by rw [Finset.mem_singleton.mp hs] at hsU ⊢; exact hmero hsU)
    (fun s hs hsU => by rw [Finset.mem_singleton.mp hs] at hsU ⊢; exact hn hsU) hγ hγU hclosed
    (fun t ht => by simpa using hγoff t ht) hnull
  simpa using key

/-- **Winding-weighted zero counting.** Let `f` be analytic on an open `U` with all its zeros in a
finite set `S`, and let `γ` be a closed piecewise-`C¹` curve in `U`, null-homologous in `U`, that
avoids `S`. Then

`∫ t in a..b, γ' t • logDeriv f (γ t) = 2πi · ∑_{z ∈ S} n_z(γ) · analyticOrderNatAt f z`:

the contour integral of `f'/f` counts the zeros of `f` with multiplicity, each weighted by the
winding number of `γ` about it. This is the pole-free specialisation of
`TauCeti.Contour.argumentPrinciple_nullHomologous`, with the orders read off by
`analyticOrderNatAt` instead of by a caller-supplied `ord`.

The zeros are automatically of finite order (`TauCeti.analyticOrderAt_ne_top_of_zeros_subset`):
confining them to a finite set already rules out `f` vanishing identically near a point of `U`. -/
theorem argumentPrinciple_nullHomologous_of_analyticOnNhd {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hzeros : ∀ z ∈ U, f z = 0 → z ∈ S)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I *
          ∑ z ∈ S, windingNumber γ a b z * (analyticOrderNatAt f z : ℂ) := by
  refine argumentPrinciple_nullHomologous (ord := fun z => (analyticOrderNatAt f z : ℤ)) hU
    (fun z hzU hzS => ⟨hf z hzU, fun h => hzS (hzeros z hzU h)⟩)
    (fun s _ hsU => (hf s hsU).meromorphicAt) (fun s _ hsU => ?_) hγ hγU hclosed hγoff hnull
  -- For an analytic function the meromorphic order is the analytic one, which is finite here.
  rw [(hf s hsU).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_zeros_subset hU hsU hzeros)]
  simp

end TauCeti.Contour

end
