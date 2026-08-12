/-
Copyright (c) 2026 TauCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# The parity lemma for nebentypus character spaces

The weight and the nebentypus of a nonzero modular form determine each other's parity:
`M_k(Γ₁(N), χ) ≠ 0` forces `χ(-1) = (-1)^k`. This is the emptiness criterion that odd
weights and Eisenstein constructions consume, and the ModularForms roadmap pins it at
Layer 0, alongside the diamond operators and character spaces of
`TauCeti.NumberTheory.ModularForms.DiamondOperators` on which it is stated.

The mechanism is `-I`. It lies in `Γ₀(N)` at every level, and its lower-right entry is the
unit `-1`, so it represents the diamond operator `⟨-1⟩`. On the other hand `-I` acts
trivially on `ℍ` and has determinant `1`, so slashing by it is multiplication by the scalar
`(-1)^k` (`ModularForm.slash_neg_one`). Comparing the two readings gives
`⟨-1⟩ = (-1)^k` as an operator (`diamondOp_neg_one`), and hence `χ(-1) = (-1)^k` on any
nonzero element of the `χ`-eigenspace.

The criterion is one-directional: matching parities do not make the space nonzero, and
nothing here claims they do. At the degenerate levels `N ∣ 2`, where `-I` lies in `Γ₁(N)`
itself (`CongruenceSubgroup.neg_one_mem_Gamma1_iff`), the same computation kills the whole of
`M_k(Γ₁(N))` in odd weight (`ModularForm.eq_zero_of_odd_of_dvd_two`, deduced from Mathlib's
`ModularForm.eq_zero_of_neg_one_mem`). That is consistent with the parity lemma rather than
additional to it: there `-1 = 1` in `(ZMod N)ˣ`, so every `χ` has `χ(-1) = 1 ≠ -1 = (-1)^k`.

## Main results

* `diamondOp_neg_one`, `diamondOpCusp_neg_one`: the diamond operator `⟨-1⟩` is the scalar
  `(-1)^k`.
* `char_neg_one_of_mem_modFormCharSpace`, `char_neg_one_of_mem_cuspFormCharSpace`: the parity
  lemma, `χ(-1) = (-1)^k` for a nonzero form in the `χ`-eigenspace.
* `modFormCharSpace_eq_bot_of_char_neg_one_ne`, `cuspFormCharSpace_eq_bot_of_char_neg_one_ne`:
  its contrapositive, the emptiness criterion; `char_neg_one_of_modFormCharSpace_ne_bot` and
  `char_neg_one_of_cuspFormCharSpace_ne_bot` restate the lemma on the space itself.
* `modFormCharSpace_one_eq_bot_of_odd`: there are no odd-weight forms with trivial nebentypus,
  the classical `M_k(Γ₀(N)) = 0` for odd `k`.
* `ModularForm.eq_zero_of_odd_of_dvd_two`: at the levels `N ∣ 2` all of `M_k(Γ₁(N))` vanishes
  in odd weight.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.1 (the remark following the
  definition of `M_k(N, χ)`)
* Miyake, *Modular forms*, §4.3
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### The diamond operator at `-1` -/

/-- The diamond operator `⟨-1⟩` acts on `M_k(Γ₁(N))` as the scalar `(-1)^k`: it is
represented by `-I ∈ Γ₀(N)`, and slashing by `-I` is multiplication by `(-1)^k`. -/
theorem coe_diamondOp_neg_one (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOp k (-1 : (ZMod N)ˣ) f) = (-1 : ℂ) ^ k • ⇑f := by
  rw [coe_diamondOp k (-1 : (ZMod N)ˣ) (Gamma0.negOne N) Gamma0Map_toHomUnits_negOne f,
    Gamma0.coe_negOne, mapGL_neg_one, ModularForm.slash_neg_one]

/-- The diamond operator `⟨-1⟩` on `M_k(Γ₁(N))` is the scalar `(-1)^k`. -/
@[simp]
theorem diamondOp_neg_one (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp k (-1 : (ZMod N)ˣ) f = ((-1 : ℂ) ^ k) • f :=
  ModularForm.ext fun z ↦ congr_fun (coe_diamondOp_neg_one k f) z

/-- The diamond operator `⟨-1⟩` acts on `S_k(Γ₁(N))` as the scalar `(-1)^k`. -/
theorem coe_diamondOpCusp_neg_one (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOpCusp k (-1 : (ZMod N)ˣ) f) = (-1 : ℂ) ^ k • ⇑f := by
  rw [coe_diamondOpCusp k (-1 : (ZMod N)ˣ) (Gamma0.negOne N) Gamma0Map_toHomUnits_negOne f,
    Gamma0.coe_negOne, mapGL_neg_one, ModularForm.slash_neg_one]

/-- The diamond operator `⟨-1⟩` on `S_k(Γ₁(N))` is the scalar `(-1)^k`. -/
@[simp]
theorem diamondOpCusp_neg_one (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOpCusp k (-1 : (ZMod N)ˣ) f = ((-1 : ℂ) ^ k) • f :=
  CuspForm.ext fun z ↦ congr_fun (coe_diamondOpCusp_neg_one k f) z

/-! ### The parity lemma -/

/-- **The parity lemma.** If `M_k(Γ₁(N), χ)` contains a nonzero form then `χ(-1) = (-1)^k`.

Equivalently: the nebentypus of a nonzero modular form has the parity of its weight. The
proof compares the two descriptions of `-I`, as the representative of the diamond operator
`⟨-1⟩` (which acts by `χ(-1)` on the `χ`-eigenspace) and as a scalar matrix (which slashes
by `(-1)^k`). -/
theorem char_neg_one_of_mem_modFormCharSpace {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (hf0 : f ≠ 0) : (χ (-1) : ℂ) = (-1 : ℂ) ^ k := by
  have hne : (⇑f : ℍ → ℂ) ≠ 0 := fun h ↦ hf0 (DFunLike.coe_injective (by simpa using h))
  have h : ((-1 : ℂ) ^ k) • (⇑f : ℍ → ℂ) = (χ (-1) : ℂ) • (⇑f : ℍ → ℂ) := by
    rw [← coe_diamondOp_neg_one k f, diamondOp_apply_of_mem_modFormCharSpace k χ (-1) hf]
    simp
  exact ((smul_left_inj hne).mp h).symm

/-- **The parity lemma for cusp forms.** If `S_k(Γ₁(N), χ)` contains a nonzero form then
`χ(-1) = (-1)^k`. -/
theorem char_neg_one_of_mem_cuspFormCharSpace {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hf0 : f ≠ 0) : (χ (-1) : ℂ) = (-1 : ℂ) ^ k := by
  have hne : (⇑f : ℍ → ℂ) ≠ 0 := fun h ↦ hf0 (DFunLike.coe_injective (by simpa using h))
  have h : ((-1 : ℂ) ^ k) • (⇑f : ℍ → ℂ) = (χ (-1) : ℂ) • (⇑f : ℍ → ℂ) := by
    rw [← coe_diamondOpCusp_neg_one k f,
      diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ (-1) hf]
    simp
  exact ((smul_left_inj hne).mp h).symm

/-! ### The emptiness criterion -/

/-- If the parities of `χ` and `k` disagree, `M_k(Γ₁(N), χ)` is zero. -/
theorem modFormCharSpace_eq_bot_of_char_neg_one_ne (h : (χ (-1) : ℂ) ≠ (-1 : ℂ) ^ k) :
    modFormCharSpace (N := N) k χ = ⊥ :=
  Submodule.eq_bot_iff _ |>.mpr fun _f hf ↦
    not_not.mp fun hf0 ↦ h (char_neg_one_of_mem_modFormCharSpace hf hf0)

/-- If the parities of `χ` and `k` disagree, `S_k(Γ₁(N), χ)` is zero. -/
theorem cuspFormCharSpace_eq_bot_of_char_neg_one_ne (h : (χ (-1) : ℂ) ≠ (-1 : ℂ) ^ k) :
    cuspFormCharSpace (N := N) k χ = ⊥ :=
  Submodule.eq_bot_iff _ |>.mpr fun _f hf ↦
    not_not.mp fun hf0 ↦ h (char_neg_one_of_mem_cuspFormCharSpace hf hf0)

/-- **The parity lemma**, in the form the roadmap states it: if `M_k(Γ₁(N), χ)` is nonzero
then `χ(-1) = (-1)^k`. -/
theorem char_neg_one_of_modFormCharSpace_ne_bot (h : modFormCharSpace (N := N) k χ ≠ ⊥) :
    (χ (-1) : ℂ) = (-1 : ℂ) ^ k :=
  not_not.mp fun hne ↦ h (modFormCharSpace_eq_bot_of_char_neg_one_ne hne)

/-- **The parity lemma for cusp forms**, in the form the roadmap states it. -/
theorem char_neg_one_of_cuspFormCharSpace_ne_bot (h : cuspFormCharSpace (N := N) k χ ≠ ⊥) :
    (χ (-1) : ℂ) = (-1 : ℂ) ^ k :=
  not_not.mp fun hne ↦ h (cuspFormCharSpace_eq_bot_of_char_neg_one_ne hne)

/-- An even weight admits only even nebentypus: `χ(-1) = 1`. -/
theorem char_neg_one_eq_one_of_even {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (hf0 : f ≠ 0) (hk : Even k) : (χ (-1) : ℂ) = 1 := by
  rw [char_neg_one_of_mem_modFormCharSpace hf hf0, hk.neg_one_zpow]

/-- An odd weight admits only odd nebentypus: `χ(-1) = -1`. -/
theorem char_neg_one_eq_neg_one_of_odd {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (hf0 : f ≠ 0) (hk : Odd k) : (χ (-1) : ℂ) = -1 := by
  rw [char_neg_one_of_mem_modFormCharSpace hf hf0, hk.neg_one_zpow]

/-- There are no nonzero odd-weight forms with trivial nebentypus: `M_k(N, 1) = 0` for `k`
odd. This is the classical statement that `M_k(Γ₀(N))` vanishes in odd weight, since
`-I ∈ Γ₀(N)` acts on it by `(-1)^k = -1`. -/
theorem modFormCharSpace_one_eq_bot_of_odd (hk : Odd k) :
    modFormCharSpace (N := N) k 1 = ⊥ :=
  modFormCharSpace_eq_bot_of_char_neg_one_ne (by norm_num [hk.neg_one_zpow])

/-- There are no nonzero odd-weight cusp forms with trivial nebentypus. -/
theorem cuspFormCharSpace_one_eq_bot_of_odd (hk : Odd k) :
    cuspFormCharSpace (N := N) k 1 = ⊥ :=
  cuspFormCharSpace_eq_bot_of_char_neg_one_ne (by norm_num [hk.neg_one_zpow])

/-! ### The degenerate levels `N ∣ 2` -/

/-- At the levels `N ∣ 2`, exactly those with `-I ∈ Γ₁(N)`, every odd-weight modular form for
`Γ₁(N)` vanishes. -/
theorem ModularForm.eq_zero_of_odd_of_dvd_two (hN : N ∣ 2) (hk : Odd k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f = 0 :=
  _root_.ModularForm.eq_zero_of_neg_one_mem
    (Subgroup.mem_map.mpr ⟨-1, neg_one_mem_Gamma1_iff.mpr hN, mapGL_neg_one⟩) hk f

end TauCeti
