/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# The enveloping-algebra representation on a standard `sl₂`-module

This file records how the canonical representation of the universal enveloping algebra acts on
the standard basis of `sl (Fin 2)` in the module `TauCeti.Sl2Std K n`.

## Main result

* `TauCeti.Sl2Std.representation_ι'`: the simp-normal specialization of the canonical
  enveloping representation on every `sl₂` generator.
* `TauCeti.Sl2Std.representation_ι_slFinTwoBasis`: the canonical enveloping representation sends
  the standard `sl₂` basis to the raising, lowering, and Cartan operators.
-/

public section

namespace TauCeti.Sl2Std

open scoped Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The simp-normal specialization of the canonical enveloping-algebra representation on an
element of `sl (Fin 2) K`. -/
@[simp]
theorem representation_ι' (x : LieAlgebra.SpecialLinear.sl (Fin 2) K) :
    LieModule.toEnd K (LieAlgebra.SpecialLinear.sl (Fin 2) K) (Sl2Std K n) x = rep K n x := by
  ext v
  rw [LieModule.toEnd_apply_apply, lie_eq_rep_apply]

/-- The canonical enveloping-algebra representation sends the standard `sl₂` basis elements to
the raising, lowering, and Cartan operators. -/
theorem representation_ι_slFinTwoBasis (i : Fin 3) :
    TauCeti.UniversalEnvelopingAlgebra.representation K
        (LieAlgebra.SpecialLinear.sl (Fin 2) K) (Sl2Std K n)
        (_root_.UniversalEnvelopingAlgebra.ι K (slFinTwoBasis K i)) =
      ![raise K n, lower K n, diag K n] i := by
  rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι, representation_ι', rep_apply_basis]

end TauCeti.Sl2Std
