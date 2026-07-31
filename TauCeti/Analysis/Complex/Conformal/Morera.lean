/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Basic

/-!
# Morera's theorem

Morera's theorem is the converse to Cauchy–Goursat: a continuous function on an
open set whose integral over every rectangle contained in the set vanishes is
holomorphic there.  In Mathlib this is the equivalence

`Complex.IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn ℂ f U`

proved in `Mathlib.Analysis.Complex.HasPrimitives` as
`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`, together with the
ball and whole-plane primitive existence theorems `IsConservativeOn.isExactOn_ball`
and `IsConservativeOn.isExactOn_univ`.  Those results are stated in their natural
`E`-valued generality and are not named `morera`; this file supplies the
scalar `ℂ` named theorem and its basic API, the L0 target

> *Morera as a named theorem*

from `TauCetiRoadmap/ConformalMapping/README.md`.  It is the local-mapping-engine
counterpart to Rouché, Hurwitz and the open-mapping degree, which are proved in
`Conformal/Rouche.lean`, `Conformal/Hurwitz.lean` and `Conformal/LocalDegree.lean`.

The rectangle condition is exactly Mathlib's `Complex.IsConservativeOn`:
for `z , w : ℂ` with `Complex.Rectangle z w ⊆ U`,
`wedgeIntegral z w f = - wedgeIntegral w z f`,
i.e.

```
(∫ x in z.re..w.re, f (x + z.im * I)) - (∫ x in z.re..w.re, f (x + w.im * I))
  + I • (∫ y in z.im..w.im, f (w.re + y * I))
  - I • (∫ y in z.im..w.im, f (z.re + y * I)) = 0,
```

the integral of `f` around the boundary of the rectangle.
`DifferentiableOn.isConservativeOn` gives the forward Cauchy direction,
`IsConservativeOn.isExactOn_ball` the Morera direction on a disc
(continuous + conservative ⇒ existence of a primitive ⇒ holomorphic),
and the global equivalence `isConservativeOn_and_continuousOn_iff_isDifferentiableOn`
packages both for an arbitrary open set — what is classically called Morera's theorem.

All statements are for `f : ℂ → ℂ`, in accordance with the generality bar of
`ConformalMapping/README.md` (every theorem added in layers L0–L6 is scalar `ℂ`);
the `E`-valued Mathlib inputs are consumed, not restated.

## Main results

* `TauCeti.differentiableOn_of_continuousOn_of_isConservativeOn` — Morera:
  continuous + conservative on an open set ⇒ holomorphic.
* `TauCeti.morera` — the same statement, named `morera`.
* `TauCeti.isConservativeOn_of_differentiableOn` — the Cauchy converse.
* `TauCeti.isConservativeOn_and_continuousOn_iff_differentiableOn` — the equivalence.
* `TauCeti.isExactOn_ball_of_continuousOn_of_isConservativeOn` — Morera on a disc gives a
  primitive, hence holomorphy.
* `TauCeti.morera_ball` — Morera explicitly on a ball via rectangle integrals.
* `TauCeti.morera_univ` — Morera on `ℂ`.

## Coordination with upstream Mathlib

Mathlib proves the `E`-valued equivalence in `HasPrimitives.lean` and names the ball
case `Complex.IsConservativeOn.isExactOn_ball` as "Morera's Theorem" in its module doc.
What was missing for the conformal-mapping roadmap was a *named* theorem `morera`
in the scalar library together with the discoverable wrapper API that `ConformalMapping`
consumes.  Per the coordination clause of `ConformalMapping/README.md`, L0 material overlaps
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves
Hurwitz-type results internally; this file is not a temporary shim for that effort, but if
Mathlib adds a dedicated `morera` name, this wrapper should be refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §6.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IV §5.
-/

public section

namespace TauCeti

open Complex Metric Set Topology

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- **Morera's theorem (conservative form).**  If `f` is continuous on an open set `U ⊆ ℂ`
and conservative on `U` — i.e. its integral over every rectangle contained in `U` vanishes —
then `f` is holomorphic on `U`.

`Complex.IsConservativeOn f U` is exactly the rectangle-integral vanishing condition:
`wedgeIntegral z w f = - wedgeIntegral w z f` for all `z w` with `Rectangle z w ⊆ U`.
This is one direction of `isConservativeOn_and_continuousOn_iff_isDifferentiableOn`. -/
theorem differentiableOn_of_continuousOn_of_isConservativeOn
    (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hcons : Complex.IsConservativeOn (E := ℂ) f U) :
    DifferentiableOn ℂ f U := by
  exact (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn (f := f) hU).mp
    ⟨hcons, hcont⟩

/-- **Morera's theorem**, named.  A continuous function on an open set whose rectangle
integrals vanish is holomorphic.  Alias for
`TauCeti.differentiableOn_of_continuousOn_of_isConservativeOn`. -/
theorem morera (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hcons : Complex.IsConservativeOn (E := ℂ) f U) :
    DifferentiableOn ℂ f U :=
  differentiableOn_of_continuousOn_of_isConservativeOn hU hcont hcons

/-- The forward Cauchy direction: a holomorphic function on a set is conservative there —
its rectangle integrals vanish. -/
theorem isConservativeOn_of_differentiableOn {s : Set ℂ}
    (hf : DifferentiableOn ℂ f s) :
    Complex.IsConservativeOn (E := ℂ) f s :=
  hf.isConservativeOn

/-- **Morera's theorem as an equivalence** on an open set:
`ContinuousOn f U ∧ IsConservativeOn f U ↔ DifferentiableOn ℂ f U`,
stated with `IsConservativeOn` first to match Mathlib's
`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`. -/
theorem isConservativeOn_and_continuousOn_iff_differentiableOn
    (hU : IsOpen U) :
    Complex.IsConservativeOn (E := ℂ) f U ∧ ContinuousOn f U ↔ DifferentiableOn ℂ f U := by
  constructor
  · rintro ⟨hcons, hcont⟩
    exact differentiableOn_of_continuousOn_of_isConservativeOn hU hcont hcons
  · intro hf
    exact ⟨hf.isConservativeOn, hf.continuousOn⟩

/-- The same equivalence with the continuous hypothesis first, the form most callers use. -/
theorem continuousOn_and_isConservativeOn_iff_differentiableOn
    (hU : IsOpen U) :
    ContinuousOn f U ∧ Complex.IsConservativeOn (E := ℂ) f U ↔ DifferentiableOn ℂ f U := by
  rw [and_comm]
  exact isConservativeOn_and_continuousOn_iff_differentiableOn hU

/-- **Morera's theorem on a disc gives a primitive.**  If `f` is continuous and conservative
on `ball c r`, then it has a primitive there — in particular it is holomorphic on the ball.
This is Mathlib's `IsConservativeOn.isExactOn_ball` followed by the primitive-to-holomorphic
implication. -/
theorem isExactOn_ball_of_continuousOn_of_isConservativeOn {c : ℂ} {r : ℝ}
    (hcont : ContinuousOn f (Metric.ball c r))
    (hcons : Complex.IsConservativeOn (E := ℂ) f (Metric.ball c r)) :
    Complex.IsExactOn f (Metric.ball c r) :=
  hcons.isExactOn_ball hcont

/-- **Morera's theorem on a ball**, holomorphy form. -/
theorem morera_ball {c : ℂ} {r : ℝ}
    (hcont : ContinuousOn f (Metric.ball c r))
    (hcons : Complex.IsConservativeOn (E := ℂ) f (Metric.ball c r)) :
    DifferentiableOn ℂ f (Metric.ball c r) :=
  differentiableOn_of_continuousOn_of_isConservativeOn isOpen_ball hcont hcons

/-- **Morera's theorem on the whole plane.**  A continuous function on `ℂ` whose rectangle
integrals vanish is entire and has a primitive on `ℂ`. -/
theorem morera_univ (hcont : Continuous f)
    (hcons : Complex.IsConservativeOn (E := ℂ) f univ) :
    DifferentiableOn ℂ f univ ∧ Complex.IsExactOn f univ := by
  constructor
  · exact differentiableOn_of_continuousOn_of_isConservativeOn isOpen_univ hcont.continuousOn hcons
  · exact hcons.isExactOn_univ hcont

/-- The rectangle-integral vanishing hypothesis spelled out as the usual boundary integral.
For any rectangle `Rectangle z w ⊆ U`,

```
(∫ x in z.re..w.re, f (x + z.im * I)) - (∫ x in z.re..w.re, f (x + w.im * I))
  + I • (∫ y in z.im..w.im, f (w.re + y * I))
  - I • (∫ y in z.im..w.im, f (z.re + y * I)) = 0,
```

then `f` is holomorphic on `U`, provided it is continuous there.  This is Morera's theorem
with the definition of `IsConservativeOn` unfolded via `wedgeIntegral_add_wedgeIntegral_eq`. -/
theorem morera_of_forall_rect_integral_eq_zero (hU : IsOpen U)
    (hcont : ContinuousOn f U)
    (hrect : ∀ z w : ℂ, Rectangle z w ⊆ U →
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 0) :
    DifferentiableOn ℂ f U := by
  apply differentiableOn_of_continuousOn_of_isConservativeOn hU hcont
  intro z w hzw
  have hsum : wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
    rw [wedgeIntegral_add_wedgeIntegral_eq]
    exact hrect z w hzw
  rwa [add_eq_zero_iff_eq_neg] at hsum

end TauCeti
