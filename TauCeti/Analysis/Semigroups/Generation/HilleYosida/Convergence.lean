/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Approximation

/-!
# Compact-time convergence of the Hille--Yosida approximations

This file assembles the two halves of the exponent-zero, general-`M` Hille--Yosida construction
that are already available: the uniform bound `‖exp (t A_lambda)‖ ≤ M` on the Yosida exponentials
proved in `TauCeti/Analysis/Semigroups/Generation/HilleYosida/Approximation.lean`, and the
convergence `A_lambda x -> A x` proved in
`TauCeti/Analysis/Semigroups/Generation/Yosida/Basic.lean`
from the resolvent bound alone. Together they say that for a densely defined operator whose
resolvent powers at `lambda > 0` satisfy

`‖R(lambda, A) ^ n‖ ≤ M / lambda ^ n` for every `n ≥ 1`, with `1 ≤ M`,

the orbits `exp (t A_lambda) x` are Cauchy as `lambda -> +∞`, uniformly for `t` in a compact
interval `[0, T]` and for every vector `x` of the space.

Only the first power bound `n = 1` enters the convergence `A_lambda x -> A x`; the bounds on the
higher powers are what make the exponentials uniformly bounded, and hence what lets a domain
estimate be spread over the whole space by density. The comparison estimate contributes a factor
`M ^ 2`, which is harmless here because the conclusion is a Cauchy property rather than a norm
bound, and is the reason the Hille--Yosida hypotheses are not weakened to a bound on `R(lambda, A)`
alone.

Completeness then turns this Cauchy property into a candidate pointwise limit family.
`TauCeti.Semigroups.hilleYosidaLimitSemigroup` in
`TauCeti/Analysis/Semigroups/Generation/HilleYosida/Limit.lean` packages this family into a
strongly continuous semigroup and establishes its growth bound `(0, M)`. Its generator is
identified as `A`, and the reduction from a general growth exponent is reversed, in
`TauCeti/Analysis/Semigroups/Generation/HilleYosida/Generation.lean`.

## Main results

* `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact_of_norm_resolvent_pow_le`:
  the compact-time Cauchy property, on every vector of the space.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {A : X →ₗ.[ℝ] X} {M : ℝ}

/-- **The Hille--Yosida approximations are uniformly Cauchy on compact time intervals.** For a
densely defined operator whose resolvent powers obey the exponent-zero Hille--Yosida bounds at
growth constant `M`, and for every vector `x` and every `T ≥ 0`, the vectors
`exp (t A_lambda) x` are Cauchy as `lambda -> +∞`, uniformly for `0 ≤ t ≤ T`.

This is the estimate from which a candidate pointwise limit family is defined; later arguments
establish its semigroup structure and identify its generator as `A`. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact_of_norm_resolvent_pow_le (hM : 1 ≤ M)
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hpow : ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, 0 < lambda →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      Filter.atTop (Set.Icc 0 T) :=
  exp_yosidaApproximation_uniformCauchySeqOn_compact hres
    (fun lambda hlambda => by simpa using hpow 1 le_rfl lambda hlambda)
    (fun lambda hlambda _ hs =>
      norm_exp_smul_yosidaApproximation_le hM hlambda hs fun n hn => hpow n hn lambda hlambda)
    hdense x hT

end TauCeti.Semigroups

end
