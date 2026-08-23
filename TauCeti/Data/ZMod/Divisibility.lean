/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Solving the linear congruence `j b ≡ a` modulo `n`

A linear congruence with unit coefficient is solvable: if `b` is a unit modulo `n`, then some
residue `j : ZMod n` satisfies `n ∣ a - j.val * b` over `ℤ`. The solution is `j = a b⁻¹`, and it
is returned as a residue class together with its canonical representative `j.val`, which is the
form a coset representative indexed by `Fin n` needs.

Extracted from `TauCeti/NumberTheory/ModularForms/CongruenceSubgroups.lean`, where it was private;
that index calculation was ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean`, Chris Birkbeck, Apache-2.0). The lemma is
consumed there and in `HeckeRing/GL2/Gamma1/CoprimeCosets.lean`.

## Main results

* `ZMod.exists_dvd_sub_val_mul`: the congruence `j b ≡ a (mod n)` has a solution `j : ZMod n`
  whenever `b` is a unit modulo `n`.
-/

public section

namespace ZMod

/-- **A linear congruence with unit coefficient is solvable.** If `b` is a unit modulo `n`, then
`n ∣ a - j.val * b` for some `j : ZMod n`, namely `j = a b⁻¹`. -/
lemma exists_dvd_sub_val_mul (n : ℕ) [NeZero n] (a b : ℤ)
    (hb : IsUnit ((b : ℤ) : ZMod n)) : ∃ j : ZMod n, (n : ℤ) ∣ a - (j.val : ℤ) * b := by
  obtain ⟨u, hu⟩ := hb
  refine ⟨(a : ZMod n) * ↑u⁻¹, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc]
  -- the coerced product collapses: `↑b = ↑u` by `hu`, and `u⁻¹ * u = 1` in the units
  have hunit : (↑u⁻¹ * ((b : ℤ) : ZMod n) : ZMod n) = 1 := by rw [← hu, Units.inv_mul]
  rw [hunit, mul_one, sub_self]

end ZMod
