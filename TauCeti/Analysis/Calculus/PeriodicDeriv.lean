/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LogDeriv

import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Periodicity of the derivative and the logarithmic derivative

Differentiation commutes with translation of the domain, so the Fréchet and the
one-variable derivative of a periodic function are periodic with the same period, and
hence so is the logarithmic derivative. All three statements are unconditional:
`fderiv`, `deriv`, and with them `logDeriv` take their junk values at non-differentiable
points, and the translation identities hold there too.

## Main declarations

* `TauCeti.Function.Periodic.fderiv`: the Fréchet derivative of a periodic function is
  periodic.
* `TauCeti.Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `TauCeti.Function.Periodic.logDeriv`: the logarithmic derivative of a periodic
  function is periodic.
-/

public section

namespace TauCeti

namespace Function

namespace Periodic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The Fréchet derivative of a periodic function is periodic. -/
protected theorem fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {c : E}
    (hf : _root_.Function.Periodic f c) :
    _root_.Function.Periodic (fderiv 𝕜 f) c := fun x ↦ by
  rw [← fderiv_comp_add_right, hf.funext]

/-- The derivative of a periodic function is periodic. -/
protected theorem deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F}
    {c : 𝕜} (hf : _root_.Function.Periodic f c) :
    _root_.Function.Periodic (_root_.deriv f) c := fun x ↦ by
  rw [← deriv_comp_add_const, hf.funext]

/-- The logarithmic derivative of a periodic function is periodic. -/
protected theorem logDeriv {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    {f : 𝕜 → 𝕜'} {c : 𝕜} (hf : _root_.Function.Periodic f c) :
    _root_.Function.Periodic (_root_.logDeriv f) c :=
  (Periodic.deriv hf).div hf

end Periodic

end Function

end TauCeti

end
