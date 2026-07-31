/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Cycle

/-!
# Finite formal combinations of contours

The contour-integration roadmap defines a **cycle** as a finite formal `ℤ`-combination of closed
piecewise-`C¹` curves.  This file supplies that finite-linear-combination layer without introducing
a bundled path type: a cycle is presented by a finite index set `I`, raw curves
`γ : ι → ℝ → ℂ`, their parameter intervals `a i`, `b i`, and integer coefficients `n i`.

The two operations needed by the classical theory are evaluated termwise.  Thus the contour
integral of the cycle is

`∑ i ∈ I, n i * ∫ t in a i..b i, (γ i)' t • f (γ i t)`,

and its winding number about `z` is `∑ i ∈ I, n i * windingNumber (γ i) (a i) (b i) z`.
The results below show that the homology Cauchy theorem and the classical residue theorem respect
these evaluations.  In particular, the latter has exactly the roadmap's arbitrary-cycle formula:

`∮_C f = 2πi ∑_s n_s(C) Res_s(f)`.

This indexed presentation deliberately leaves equality of cycles unbundled.  It follows the
roadmap's raw-function convention and avoids imposing a decidable equality on functions merely to
store them in a `Finsupp`.  Repeated indices and zero coefficients are harmless, as they should be
for a formal sum.

## Main results

* `TauCeti.Contour.homologyCauchyTheorem_linearCombination` — Cauchy's theorem for a finite
  integer combination of null-homologous closed curves.
* `TauCeti.Contour.classicalResidueTheorem_linearCombination` — the winding-weighted residue
  theorem for such a finite formal cycle avoiding the poles.

## Provenance

No formal source is vendored.  These statements are the finite-additive closure of Tau Ceti's
single-curve homology Cauchy and residue theorems.  The notion of cycle and the formula follow
S. Lang, *Complex Analysis* (GTM 103), Chapter VI, and the ContourIntegration roadmap.
-/

public section

open Set

open scoped Interval

namespace TauCeti.Contour

/-- **The homology Cauchy theorem for a finite formal cycle.** Let `I` index finitely many
piecewise-`C¹` closed curves in an open set `U`, each null-homologous in `U`.  For integer
coefficients `n i`, the integer-weighted sum of their contour integrals of a holomorphic function
vanishes.

The data are kept as raw curves and endpoints rather than a bundled path type.  No regularity is
required for indices outside `I`, since they do not occur in the formal combination. -/
theorem homologyCauchyTheorem_linearCombination {ι : Type*} {U : Set ℂ} {f : ℂ → ℂ}
    (I : Finset ι) (n : ι → ℤ) (γ : ι → ℝ → ℂ) (a b : ι → ℝ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (hγ : ∀ i ∈ I, IsPiecewiseC1On (γ i) (a i) (b i))
    (hγU : ∀ i ∈ I, ∀ t ∈ uIcc (a i) (b i), γ i t ∈ U)
    (hclosed : ∀ i ∈ I, γ i (a i) = γ i (b i))
    (hnull : ∀ i ∈ I, IsNullHomologous (γ i) (a i) (b i) U) :
    ∑ i ∈ I, (n i : ℂ) * ∫ t in a i..b i, deriv (γ i) t • f (γ i t) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [homologyCauchyTheorem hU (γ i) (a i) (b i) (hγ i hi) (hγU i hi)
    (hclosed i hi) hf (hnull i hi), mul_zero]

/-- **The classical residue theorem for a finite formal cycle.** Let `I` index finitely many
piecewise-`C¹` closed curves in an open set `U`, each null-homologous in `U` and avoiding the finite
set `S`.  Weighting the curves by integers `n i`, the sum of their contour integrals is `2πi` times
the residue at each `s ∈ S`, weighted by the formal cycle's winding number
`∑ i ∈ I, n i * windingNumber (γ i) (a i) (b i) s`.

This is the finite-formal-`ℤ`-combination form requested by Layer 0 of the ContourIntegration
roadmap.  Points of `S` outside `U` are allowed, exactly as in
`classicalResidueTheorem_nullHomologous`: each component has winding number zero there. -/
theorem classicalResidueTheorem_linearCombination {ι : Type*} {U : Set ℂ} {S : Finset ℂ}
    {f : ℂ → ℂ} (I : Finset ι) (n : ι → ℤ) (γ : ι → ℝ → ℂ) (a b : ι → ℝ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hγ : ∀ i ∈ I, IsPiecewiseC1On (γ i) (a i) (b i))
    (hγU : ∀ i ∈ I, ∀ t ∈ uIcc (a i) (b i), γ i t ∈ U)
    (hclosed : ∀ i ∈ I, γ i (a i) = γ i (b i))
    (hoff : ∀ i ∈ I, ∀ t ∈ uIcc (a i) (b i), γ i t ∉ (S : Set ℂ))
    (hnull : ∀ i ∈ I, IsNullHomologous (γ i) (a i) (b i) U) :
    ∑ i ∈ I, (n i : ℂ) * ∫ t in a i..b i, deriv (γ i) t • f (γ i t) =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ s ∈ S, (∑ i ∈ I, (n i : ℂ) * windingNumber (γ i) (a i) (b i) s) * residue f s := by
  have hcomponent : ∀ i ∈ I,
      (∫ t in a i..b i, deriv (γ i) t • f (γ i t)) =
        2 * (Real.pi : ℂ) * Complex.I *
          ∑ s ∈ S, windingNumber (γ i) (a i) (b i) s * residue f s :=
    fun i hi => classicalResidueTheorem_nullHomologous hU hf hmero (hγ i hi) (hγU i hi)
      (hclosed i hi) (hoff i hi) (hnull i hi)
  rw [Finset.sum_congr rfl fun i hi => congrArg ((n i : ℂ) * ·) (hcomponent i hi)]
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  calc
    ∑ i ∈ I, (n i : ℂ) * (C * ∑ s ∈ S,
        windingNumber (γ i) (a i) (b i) s * residue f s) =
        C * ∑ i ∈ I, (n i : ℂ) * ∑ s ∈ S,
          windingNumber (γ i) (a i) (b i) s * residue f s := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    _ = C * ∑ i ∈ I, ∑ s ∈ S,
          ((n i : ℂ) * windingNumber (γ i) (a i) (b i) s) * residue f s := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
    _ = C * ∑ s ∈ S, ∑ i ∈ I,
          ((n i : ℂ) * windingNumber (γ i) (a i) (b i) s) * residue f s := by
            rw [Finset.sum_comm]
    _ = C * ∑ s ∈ S,
          (∑ i ∈ I, (n i : ℂ) * windingNumber (γ i) (a i) (b i) s) * residue f s := by
            congr 1
            exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul ..).symm

end TauCeti.Contour

end
