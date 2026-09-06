/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# A character that does not factor is not a function of the reduction

If `χ` mod `N` does not factor through `d ∣ N`, then knowing a unit's reduction modulo `d` does
not determine its character value: every unit has a partner in the same fibre of
`ZMod.unitsMap` on which `χ` takes a different value. This is the form the level-lowering
argument for the conductor theorem consumes, and it is stated for characters valued in any
`CommMonoidWithZero`, which is the generality of
`DirichletCharacter.factorsThrough_iff_ker_unitsMap`.

## Main results

* `DirichletCharacter.not_factorsThrough_of_not_forall`: a character non-trivial somewhere on
  the kernel of the reduction does not factor through it.
* `DirichletCharacter.exists_alt_unit_in_coset_with_char_separation`: character separation within
  a fibre of the reduction map.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`exists_alt_unit_in_coset_with_char_separation` (:656). The source reaches it through an
intermediate shift form (`exists_kernel_unit_with_char_shift`, :646) and a separate
non-factorisation witness (`exists_unit_of_not_factorsThrough`, :542); each is a one-line
consequence of the other, so only this form is ported and the extraction is done inline.
-/

public section

namespace DirichletCharacter

/-- **A character nontrivial on the kernel does not factor.** A unit homomorphism `χ` that is
not identically `1` on the kernel of `ZMod.unitsMap : (ZMod N)ˣ →* (ZMod d)ˣ` gives a Dirichlet
character that does not factor through `d`. This is the hypothesis of
`exists_alt_unit_in_coset_with_char_separation` in the form callers usually hold it. -/
theorem not_factorsThrough_of_not_forall {R : Type*} [CommMonoidWithZero R] {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) {χ : (ZMod N)ˣ →* Rˣ}
    (hχ : ¬ ∀ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 → χ u = 1) :
    ¬ DirichletCharacter.FactorsThrough (MulChar.ofUnitHom χ) d := by
  refine fun hfac ↦ hχ fun v hv ↦ ?_
  simpa using MonoidHom.mem_ker.mp
    ((factorsThrough_iff_ker_unitsMap hd).mp hfac (MonoidHom.mem_ker.mpr hv))

/-- **Character separation within a coset.** If `χ` does not factor through `d ∣ N`, then every
unit `u` has a partner `u'` with the same reduction modulo `d` but a different character value —
so the character cannot be read off the reduction alone. -/
theorem exists_alt_unit_in_coset_with_char_separation {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    [NeZero N] {d : ℕ} (hd : d ∣ N) {χ : DirichletCharacter R N}
    (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  rw [factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨v, hv_ker, hv_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  have hv_ker' : ZMod.unitsMap hd v = 1 := MonoidHom.mem_ker.mp hv_ker
  have hv_chi' : χ.toUnitHom v ≠ 1 := hv_chi ∘ MonoidHom.mem_ker.mpr
  exact ⟨u * v, by rw [map_mul, hv_ker', mul_one],
    by rw [map_mul, Ne, mul_eq_left]; exact hv_chi'⟩

end DirichletCharacter
