/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the real Gamma function

`Real.Gamma` is smooth away from the nonpositive integers and has a pole at each of them, so it is
neither continuous nor locally bounded on all of `ℝ`. It is nevertheless Borel measurable, because
the set of its singularities is countable.

Mathlib records the analytic side of this (`Real.differentiableAt_Gamma`,
`Real.not_continuousAt_Gamma_neg_nat`) but never draws the measurability conclusion. It is needed
as soon as a formula containing `Real.Gamma s` is integrated or measured *in the variable `s`* —
for instance for the normalizing constants of the Gamma and Beta densities, which is what
`TauCeti/Probability/Distributions/Measurability.lean` uses this for.

## Main results

* `Real.measurable_Gamma` — `Real.Gamma` is measurable.
-/

public section

namespace TauCeti

/-- **The real Gamma function is measurable.**

`Real.Gamma` is discontinuous exactly at the nonpositive integers, where it has poles; away from
them it is differentiable by `Real.differentiableAt_Gamma`. That leaves a countable set of
discontinuities, and a function continuous off a countable set is measurable
(`measurable_of_countable_not_continuousAt`). No boundedness is needed: the pole values are the
junk values of `Complex.Gamma` at those points, and a single point carries no Borel information. -/
@[fun_prop]
theorem _root_.Real.measurable_Gamma : Measurable Real.Gamma := by
  refine measurable_of_countable_not_continuousAt (Set.Countable.mono ?_
    (Set.countable_range fun m : ℕ => -(m : ℝ)))
  intro s hs
  by_contra hrange
  exact hs (Real.differentiableAt_Gamma fun m hm => hrange ⟨m, hm.symm⟩).continuousAt

end TauCeti
