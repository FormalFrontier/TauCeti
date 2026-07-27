/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Totally real factors of the standard product almost complex structure

The general doubled-module lemmas in `TauCeti.LinearAlgebra.TotallyReal.Basic` are phrased for the
Mathlib map `LinearEquiv.skewSwap`, which sends `(x, y)` to `(-y, x)`. The symplectic layer has
its own bundled version of the same map, `TauCeti.AlmostComplexStructure.product`. This file
bridges the two so the geometric standard structure reuses the algebraic results rather than
restating them.

## Main declarations

* `TauCeti.AlmostComplexStructure.product_toLinearMap_eq_skewSwap`: the standard product almost
  complex structure is the `skewSwap` doubled-module complex structure.
* `TauCeti.Submodule.isMaximalTotallyReal_prod_top_bot_product` and
  `TauCeti.Submodule.isMaximalTotallyReal_prod_bot_top_product`: the two coordinate factors of
  `V × V` are maximal totally real for the standard product almost complex structure.
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace AlmostComplexStructure

/-- The standard product almost complex structure on `V × V` is the `skewSwap` doubled-module
complex structure: both send `(x, y)` to `(-y, x)`. -/
theorem product_toLinearMap_eq_skewSwap :
    (product V).toLinearMap = (LinearEquiv.skewSwap ℝ V V).toLinearMap := by
  ext x <;> simp

end AlmostComplexStructure

namespace Submodule

/-- The first factor in `V × V` is maximal totally real for the standard product almost complex
structure. -/
theorem isMaximalTotallyReal_prod_top_bot_product :
    IsMaximalTotallyReal (AlmostComplexStructure.product V).toLinearMap
      ((⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ V)) := by
  rw [AlmostComplexStructure.product_toLinearMap_eq_skewSwap]
  exact isMaximalTotallyReal_prod_top_bot_skewSwap

/-- The second factor in `V × V` is maximal totally real for the standard product almost complex
structure. -/
theorem isMaximalTotallyReal_prod_bot_top_product :
    IsMaximalTotallyReal (AlmostComplexStructure.product V).toLinearMap
      ((⊥ : Submodule ℝ V).prod (⊤ : Submodule ℝ V)) := by
  rw [AlmostComplexStructure.product_toLinearMap_eq_skewSwap]
  exact isMaximalTotallyReal_prod_bot_top_skewSwap

end Submodule

end TauCeti
