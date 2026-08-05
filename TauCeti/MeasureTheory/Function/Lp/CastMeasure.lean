/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Transporting an `Lp` element along an equality of measures

Equal measures give *equal* (not merely isomorphic) `Lp` types, so an element of `Lp E p μ` can be
moved to `Lp E p ν` by `cast` whenever `μ = ν`. The cast is the identity on representatives, which
is what `TauCeti.coeFn_cast_lp` records.

This is the bookkeeping a statement needs when a space is *defined* with one description of its
measure and *used* with another, for example a basis of `L²(γ)` fed to
`TauCeti.weightL2Isometry`, whose domain is spelled `L²(volume.withDensity …)`.

## Main statements

* `TauCeti.coeFn_cast_lp`: the cast does not move representatives.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

/-- **Transporting an `Lp` element along an equality of measures does not move its
representative.** The `cast` is along the equality of types `↥(Lp E p μ) = ↥(Lp E p ν)` induced by
`μ = ν`, so it acts as the identity on functions. -/
theorem coeFn_cast_lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {p : ℝ≥0∞}
    {μ ν : Measure α} (h : μ = ν) (f : Lp E p μ) (x : α) :
    ((cast (congrArg (fun m : Measure α => (Lp E p m : Type _)) h) f : Lp E p ν) : α → E) x
      = (f : α → E) x := by
  subst h
  rfl

end TauCeti
