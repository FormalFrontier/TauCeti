/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Analyticity through `ofComplex`

A function holomorphic on the upper half-plane, extended to `ℂ` by `ofComplex`, is
analytic at every point of the open upper half-plane.

## Main declarations

* `TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public section

open UpperHalfPlane

open scoped Manifold

namespace TauCeti.UpperHalfPlane

/-- A function holomorphic on `ℍ` composes with `ofComplex` to a function analytic at
every point of the open upper half-plane. -/
lemma analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

end TauCeti.UpperHalfPlane

end
