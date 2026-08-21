/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Necessary one-dimensional second-derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative.

## Main declarations

* `TauCeti.deriv_deriv_nonpos_of_isLocalMax`: the local-maximum version.
* `TauCeti.deriv_deriv_nonneg_of_isLocalMin`: the local-minimum version.
-/

public section

namespace TauCeti

open Topology

/-- **Necessary second-derivative test.** At a local maximum of a continuous function
`g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmax : IsLocalMax g t₀) :
    deriv (deriv g) t₀ ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have hd : deriv g t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g t₀ := isLocalMin_of_deriv_deriv_pos h hd hg
  -- Being both a local minimum and a local maximum, `g` is eventually constant near `t₀`.
  have hconst : g =ᶠ[𝓝 t₀] fun _ => g t₀ := by
    filter_upwards [hmax, hmin] with y hy hy' using le_antisymm hy hy'
  have hderiv : deriv g =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.deriv] with y hy
    simpa using hy
  have hzero : deriv (deriv g) t₀ = 0 := by
    rw [hderiv.deriv_eq]; simp
  linarith

/-- **Necessary second-derivative test, minimum version.** At a local minimum of a continuous
function `g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonnegative. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmin : IsLocalMin g t₀) :
    0 ≤ deriv (deriv g) t₀ := by
  have := deriv_deriv_nonpos_of_isLocalMax (g := -g) hg.neg hmin.neg
  simpa using this

end TauCeti
