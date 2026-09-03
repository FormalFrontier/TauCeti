/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# The differential of a cochain complex as a cochain

Mathlib's `CochainComplex.HomComplex.Cochain.diff K` is the differential of a cochain complex `K`
read as a degree `1` cochain from `K` to itself, and `CochainComplex.HomComplex.δ` is the
differential of the Hom complex.  This file records the elementary calculus relating the two:
`δ` is composition with the differential cochains on either side, a morphism of cochain complexes
commutes with them, and they square to zero.

These are general facts about Mathlib's Hom complex, independent of any particular use.

## Main results

* `TauCeti.δ_eq_comp_diff_add_diff_comp`: the differential of the Hom complex is
  `δ z = z d + (-1)^(n+1) d z`.
* `TauCeti.ofHom_comp_diff`: a morphism of cochain complexes commutes with the differential
  cochains.
* `TauCeti.diff_comp_diff`: the differential cochain squares to zero.
-/

public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : CochainComplex C ℤ}

-- The output degree argument of `Cochain.comp` is not always inferable from its cochain arguments.
-- The typed proof terms below pin that index while keeping the arithmetic proof routine.

/-- The differential of the Hom complex, written through composition with the differential
cochains of the source and of the target: `δ z = z d + (-1)^(n+1) d z`. -/
theorem δ_eq_comp_diff_add_diff_comp (n m : ℤ) (hnm : n + 1 = m) (z : Cochain F G n) :
    δ n m z = z.comp (Cochain.diff G) (by lia) +
      m.negOnePow • (Cochain.diff F).comp z (by lia) := by
  ext p q hpq
  rw [δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl, Cochain.add_v,
    Cochain.comp_v z (Cochain.diff G) (by lia) p (q - 1) q (by lia) (by lia),
    Cochain.units_smul_v,
    Cochain.comp_v (Cochain.diff F) z (by lia) p (p + 1) q (by lia) (by lia),
    Cochain.diff_v, Cochain.diff_v]

/-- A morphism of cochain complexes commutes with the differential cochains. -/
theorem ofHom_comp_diff (φ : F ⟶ G) :
    (Cochain.ofHom φ).comp (Cochain.diff G) (zero_add 1) =
      (Cochain.diff F).comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.diff_v, Cochain.diff_v,
    Cochain.ofHom_v, Cochain.ofHom_v, φ.comm]

variable (F) in
/-- The differential cochain squares to zero. -/
@[simp]
theorem diff_comp_diff :
    (Cochain.diff F).comp (Cochain.diff F) (by lia : (1 : ℤ) + 1 = 2) = 0 := by
  ext p q hpq
  rw [Cochain.comp_v (Cochain.diff F) (Cochain.diff F) (by lia : (1 : ℤ) + 1 = 2)
      p (p + 1) q (by lia) (by lia),
    Cochain.diff_v, Cochain.diff_v, Cochain.zero_v, HomologicalComplex.d_comp_d]

end TauCeti
