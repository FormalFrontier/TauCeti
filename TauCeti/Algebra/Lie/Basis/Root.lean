/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic

/-!
# Root vectors of a Lie algebra basis

This file records the root spaces containing the raising and lowering generators of a
`LieAlgebra.Basis`.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

variable {ι K L : Type*} [Fintype ι] [CommRing K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] (b : LieAlgebra.Basis ι H)

/-- The raising generator `eᵢ` of a Lie algebra basis is a root vector for its simple root. -/
theorem lieBasis_e_mem_rootSpace (i : ι) : b.e i ∈ rootSpace H (⇑(b.baseSupp i)) :=
  (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp⟩

/-- The lowering generator `fᵢ` of a Lie algebra basis is a root vector for minus its simple
root. -/
theorem lieBasis_f_mem_rootSpace (i : ι) : b.f i ∈ rootSpace H (-⇑(b.baseSupp i)) :=
  (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp [← eq_neg_iff_add_eq_zero]⟩

end TauCeti
