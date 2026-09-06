/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Integral powers of a `C^n` function

Mathlib provides `ContDiffAt.pow` for natural powers and `ContDiffAt.inv` for the inverse of a
nonvanishing function, but no lemma for an integral power. This file supplies the missing
combination: an integral power of `f` is as smooth as `f` is, either away from a zero of `f` or
for a nonnegative exponent. The hypothesis is the one carried by Mathlib's
`DifferentiableAt.zpow`.

## Main results

* `ContDiffAt.zpow`: `fun z ↦ f z ^ (m : ℤ)` is `C^n` at a point where `f` is `C^n` and either
  `f` does not vanish or `m` is nonnegative.
-/

public section

namespace ContDiffAt

variable {𝕜 E 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f : E → 𝕜'} {x : E} {m : ℤ} {n : WithTop ℕ∞}

/-- An integral power of a `C^n` function is `C^n` at a point where the function does not vanish,
and also, whatever the value there, for a nonnegative exponent. -/
theorem zpow (hf : ContDiffAt 𝕜 n f x) (h : f x ≠ 0 ∨ 0 ≤ m) :
    ContDiffAt 𝕜 n (fun z ↦ f z ^ m) x := by
  obtain ⟨i, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa [zpow_natCast] using hf.pow i
  · rcases eq_or_ne i 0 with rfl | hi
    · simpa using contDiffAt_const
    · have hx : f x ≠ 0 := h.resolve_right fun hm ↦ hi (by omega)
      simpa [zpow_neg, zpow_natCast, Pi.inv_def] using (hf.pow i).inv (pow_ne_zero _ hx)

end ContDiffAt
