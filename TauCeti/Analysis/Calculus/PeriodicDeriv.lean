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

These extensions of Mathlib's periodicity API live in the root `Function` namespace as
`Periodic.*`, so that `hf.deriv` and its analogues resolve by receiver notation. They remain
protected so that opening `Function.Periodic` does not shadow `deriv` and `logDeriv` themselves.

## Main declarations

* `Function.Periodic.fderiv`: the Fréchet derivative of a periodic function is
  periodic.
* `Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `Function.Periodic.logDeriv`: the logarithmic derivative of a periodic
  function is periodic.
-/

public section

namespace Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The Fréchet derivative of a periodic function is periodic. -/
protected theorem Periodic.fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {c : E}
    (hf : Periodic f c) : Periodic (fderiv 𝕜 f) c := fun x ↦ by
  rw [← fderiv_comp_add_right, hf.funext]

/-- The derivative of a periodic function is periodic. -/
protected theorem Periodic.deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → F} {c : 𝕜} (hf : Periodic f c) : Periodic (deriv f) c := fun x ↦ by
  rw [← deriv_comp_add_const, hf.funext]

/-- The logarithmic derivative of a periodic function is periodic. -/
protected theorem Periodic.logDeriv {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {c : 𝕜} (hf : Periodic f c) :
    Periodic (logDeriv f) c :=
  hf.deriv.div hf

end Function

end
