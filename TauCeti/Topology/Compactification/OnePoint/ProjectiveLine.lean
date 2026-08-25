/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# When a Möbius image is the point at infinity

Mathlib's `OnePoint.smul_some_eq_ite` and `OnePoint.smul_infty_eq_ite` give the *value* of the
`GL (Fin 2) K` action on `OnePoint K`. This file adds the companion *criterion* for the
exceptional case — when an affine point is carried to `∞` — which Mathlib does not state.

## Main results

* `OnePoint.smul_some_eq_infty_iff`: `g • (k : OnePoint K) = ∞` exactly when the denominator
  `g 1 0 * k + g 1 1` vanishes.
-/

public section

namespace OnePoint

open Matrix

variable {K : Type*} [Field K] [DecidableEq K]

/-- **When a Möbius image is the point at infinity.** Mathlib's `smul_some_eq_ite` gives the
*value* of `g • (k : OnePoint K)`; this is the companion criterion for the exceptional case.

`[DecidableEq K]` is a hypothesis of the *statement*, not of the proof: Mathlib's `instGLAction`
is itself declared under `[Field K] [DecidableEq K]`
(`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`), so `g • (k : OnePoint K)` does
not elaborate without it. -/
@[simp]
lemma smul_some_eq_infty_iff {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) = ∞ ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 * k +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  rw [smul_some_eq_ite]
  split_ifs with hz
  · simp [hz]
  · simp [hz]

end OnePoint
