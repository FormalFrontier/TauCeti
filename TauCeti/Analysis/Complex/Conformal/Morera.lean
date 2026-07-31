/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Morera's theorem

This file provides the named scalar form of Morera's theorem required by the L0 target
"Morera as a named theorem" in `TauCetiRoadmap/ConformalMapping/README.md`. Mathlib already
proves the more general equivalence between conservativity and complex differentiability, so
the result here is a direct specialization rather than a parallel API.

## Main results

* `TauCeti.morera`: a continuous function on an open set whose rectangle integrals vanish is
  holomorphic.

## Coordination with upstream Mathlib

The conformal-mapping roadmap's L0-L3 layers overlap the in-progress Riemann mapping work in
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505). If Mathlib adds a
dedicated `morera` declaration, this named specialization should be refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, Section 6.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IV, Section 5.
-/

public section

namespace TauCeti

/-- **Morera's theorem.** A continuous function on an open set whose rectangle integrals vanish
is holomorphic. -/
theorem morera {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hcons : Complex.IsConservativeOn (E := ℂ) f U) : DifferentiableOn ℂ f U :=
  (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn (f := f) hU).mp
    ⟨hcons, hcont⟩

end TauCeti
