/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Generic lemmas for iterated derivatives within sets

This file records calculus lemmas about `iteratedDerivWithin` that are independent of any
completely-monotone or Bernstein-function structure.

## Main declarations

* `TauCeti.ContDiffOn.hasDerivAt_iteratedDerivWithin`: differentiability of an
  `iteratedDerivWithin` on a neighbourhood inside a unique-differentiability set.
For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- At a point `x` in the interior of a unique-differentiability set `s` (`s ∈ 𝓝 x`),
the derivative of the `k`-th iterated derivative-within-`s` of a `C^(k+1)` function is the
`(k+1)`-th iterated derivative-within-`s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : 𝕜 → E} {s : Set 𝕜} {k : ℕ} (hf : ContDiffOn 𝕜 ((k + 1 : ℕ) : WithTop ℕ∞) g s)
    (hs : UniqueDiffOn 𝕜 s) {x : 𝕜} (hx : s ∈ nhds x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx]
  exact (hf.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast Nat.lt_succ_self k) hs).hasDerivAt hx

end TauCeti
