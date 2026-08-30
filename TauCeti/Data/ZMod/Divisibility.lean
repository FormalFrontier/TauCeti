/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.ZMod.Basic

/-!
# Integer divisibility read off congruences modulo `n`

Two `ℤ`-divisibility facts extracted from congruences in `ZMod n`.

A linear congruence with unit coefficient is solvable: if `b` is a unit modulo `n`, then some
residue `j : ZMod n` satisfies `n ∣ a - j.val * b` over `ℤ`. The solution is `j = a b⁻¹`, and it
is returned as a residue class together with its canonical representative `j.val`, which is the
form a coset representative indexed by `Fin n` needs.

`ZMod.exists_dvd_sub_val_mul` was extracted from
`TauCeti/NumberTheory/ModularForms/CongruenceSubgroups.lean`, where it was private; that index
calculation was ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean`, Chris Birkbeck, Apache-2.0). The lemma is
consumed there and in `HeckeRing/GL2/Gamma1/CoprimeCosets.lean`.

`ZMod.natCast_dvd_val_sub_of_unitsMap_eq` is adapted from the same project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`natCast_val_sub_dvd_of_unitsMap_eq` (:665). Two departures from the source: it is stated for an
arbitrary divisor `d ∣ N` rather than only for the reduction modulo `N / l`, which is all its
proof uses, and the name places the divisibility in Mathlib's operand order.

## Main results

* `ZMod.exists_dvd_sub_val_mul`: the congruence `j b ≡ a (mod n)` has a solution `j : ZMod n`
  whenever `b` is a unit modulo `n`.
* `ZMod.natCast_dvd_val_sub_of_unitsMap_eq`: two units with the same image under `ZMod.unitsMap`
  along `d ∣ N` have representatives congruent modulo `d`, as integers.
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

/-- **From equal reductions to an integer congruence.** Two units with the same image under the
reduction `(ZMod N)ˣ → (ZMod d)ˣ` along `d ∣ N` have representatives congruent modulo `d`, as
integers. This is the bridge from unit bookkeeping to statements about integer matrix entries. -/
theorem natCast_dvd_val_sub_of_unitsMap_eq {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    (u u' : (ZMod N)ˣ) (h_eq : unitsMap hd u = unitsMap hd u') :
    (d : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have h_cast : castHom hd (ZMod d) (u : ZMod N) = castHom hd (ZMod d) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rwa [unitsMap_val, unitsMap_val] at hh
  rw [← intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [natCast_val (u' : ZMod N), natCast_val (u : ZMod N),
    ← castHom_apply (h := hd) (u' : ZMod N), ← castHom_apply (h := hd) (u : ZMod N), h_cast]

end ZMod
