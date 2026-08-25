/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic facts about normed algebras

This file provides small pieces of generic normed-algebra infrastructure used across Tau Ceti.
-/

public section

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [NormedAlgebra ℝ R]

/-- A real normed algebra regarded as a rational normed algebra. -/
noncomputable local instance normedAlgebraRatOfReal : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

end TauCeti
