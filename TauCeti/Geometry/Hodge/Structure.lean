namespace TauCeti

import Mathlib

/-- Pure Hodge structure of weight n, L0 definition. -/
structure HodgeStructure (V : Type*) [AddCommGroup V] [Module ℤ V] (hℂ : IsBaseChange ℂ (ℤ) (V →+* ℂ)) (n : ℤ) where
  piece : ℤ → Submodule ℂ (TensorProduct ℤ ℂ V)
  isInternal : ∀ p, IsCompl (piece p) (piece (n - p))

end TauCeti
