/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.CuspRing
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Ring

/-!
# The diamond operators are the Hecke operators of the `Γ₀(N)`-cosets

`ModularForms/DiamondOperators.lean` builds `⟨d⟩` by hand, as slashing by any `Γ₀(N)` matrix
with lower-right entry `d`, and shows the result is well defined on `M_k(Γ₁(N))` and on
`S_k(Γ₁(N))`. `HeckeRing/GL2/Gamma1/DiamondCosets.lean` builds, from the same matrix, an
element of the Hecke ring `𝕋 Δ₀(N) Γ₁(N) ℤ`. This file identifies the two:

`heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N γ) = diamondOp k d`,

and the same on cusp forms, and — through the `ℤ`-linear action of the Hecke ring — the
unit-indexed form `heckeSlashGamma1RingModularFormLinearMap k (diamondHeckeElem N d) =
diamondOp k d`, again on both modular and cusp forms. So the diamond operators are not a
construction parallel to the Hecke operators: they are the Hecke operators of the double cosets
`Γ₁(N) γ Γ₁(N)` with `γ ∈ Γ₀(N)`, and the identification is a theorem rather than a
definition.

## Why it is a one-term sum

Slashing by a double coset means summing over its right cosets. A diamond coset has exactly
one, `Γ₁(N) γ` (`HeckeRing.GL2.doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets`,
which holds because `Γ₁(N)` is normal in `Γ₀(N)`), so the sum
`heckeSlashSum k (diamondCosetGamma1 N γ) f` has a single summand `f ∣[k] γ` — and that is the
defining formula of `⟨d⟩`. The only remaining step is the `ℚ`-to-`ℝ` bridge
`ModularForm.rat_slash_mapGL`, since the Hecke triples live over `ℚ` and the slash action of a
modular form over `ℝ`.

Nothing here needs the choice-freeness of `⟨d⟩` to be reproved: both sides are computed at the
same representative `γ`, and their independence of it is `DiamondOperators.lean`'s
`coe_diamondOp` on one side and `HeckeRing.GL2.diamondCosetGamma1_eq_iff` on the other.

## Main results

* `HeckeRing.GL2.heckeSlashSum_diamondCosetGamma1`: the slash sum of a diamond coset is the
  single slash `f ∣[k] γ`, for a form of any of the level-`Γ₁(N)` form classes.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diamondCosetGamma1` and
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_diamondCosetGamma1`: **the identification**, on
  `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `HeckeRing.GL2.heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem` and
  `HeckeRing.GL2.heckeSlashGamma1CuspRingLinearMap_diamondHeckeElem`: the same statement read on
  the Hecke ring, at the unit-indexed element `⟨d⟩`.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diamondCosetGamma1_apply_of_mem_modFormCharSpace`
  and its cusp-form counterpart: on a nebentypus space the diamond coset acts by the scalar
  `χ(d)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ) (g : ↥(Gamma0 N))

/-- **The slash sum of a diamond coset is a single slash.** The double coset `Γ₁(N) γ Γ₁(N)`
decomposes into the one right coset `Γ₁(N) γ`, so the Hecke sum attached to it has one
summand. -/
@[simp] theorem heckeSlashSum_diamondCosetGamma1 {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    heckeSlashSum k (diamondCosetGamma1 N g) ⇑f = ⇑f ∣[k] (mapGL ℚ (g : SL(2, ℤ))) := by
  refine (heckeSlashSum_coe_eq_sum_of_rightCosets k (diamondCosetGamma1 N g)
    (fun _ : Unit ↦ mapGL ℚ (g : SL(2, ℤ)))
    (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g)
    (fun _ _ _ ↦ Subsingleton.elim _ _) f).trans ?_
  simp

/-- **The diamond operator on `M_k(Γ₁(N))` is the Hecke operator of the double coset
`Γ₁(N) γ Γ₁(N)`.** Both sides are slashing by `γ`; the left-hand side arrives as a one-term
Hecke sum over `GL₂(ℚ)`, the right-hand side as the definition of `⟨d⟩` over `GL₂(ℝ)`. -/
@[simp] theorem heckeSlashGamma1ModularFormEnd_diamondCosetGamma1 :
    heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N g) =
      diamondOp k ((Gamma0Map N).toHomUnits g) :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1ModularFormEnd, heckeSlashSum_diamondCosetGamma1,
      ModularForm.rat_slash_mapGL, coe_diamondOp k _ g rfl]

/-- **The diamond operator on `S_k(Γ₁(N))` is the Hecke operator of the double coset
`Γ₁(N) γ Γ₁(N)`.** -/
@[simp] theorem heckeSlashGamma1CuspFormEnd_diamondCosetGamma1 :
    heckeSlashGamma1CuspFormEnd k (diamondCosetGamma1 N g) =
      diamondOpCusp k ((Gamma0Map N).toHomUnits g) :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1CuspFormEnd, heckeSlashSum_diamondCosetGamma1,
      ModularForm.rat_slash_mapGL, coe_diamondOpCusp k _ g rfl]

/-- **On a nebentypus space the diamond coset acts by the scalar `χ(d)`.** This is the shape
the character-space action of the Hecke ring consumes: on `M_k(N, χ)` the diamond direction of
the ring contributes no new operator, only multiplication by `χ(d)`. -/
theorem heckeSlashGamma1ModularFormEnd_diamondCosetGamma1_apply_of_mem_modFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N g) f =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := by
  rw [heckeSlashGamma1ModularFormEnd_diamondCosetGamma1]
  exact diamondOp_apply_of_mem_modFormCharSpace k χ _ hf

/-- **On a nebentypus cusp-form space the diamond coset acts by the scalar `χ(d)`.** -/
theorem heckeSlashGamma1CuspFormEnd_diamondCosetGamma1_apply_of_mem_cuspFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeSlashGamma1CuspFormEnd k (diamondCosetGamma1 N g) f =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := by
  rw [heckeSlashGamma1CuspFormEnd_diamondCosetGamma1]
  exact diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf

/-- **The diamond element of the Hecke ring acts by the diamond operator.** Read through the
`ℤ`-linear action `heckeSlashGamma1RingModularFormLinearMap` of the Hecke ring on `M_k(Γ₁(N))`,
the element `⟨d⟩` of `HeckeRing/GL2/Gamma1/DiamondCosets.lean` is the operator `⟨d⟩` of
`ModularForms/DiamondOperators.lean`. -/
@[simp] theorem heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem (d : (ZMod N)ˣ) :
    heckeSlashGamma1RingModularFormLinearMap k (diamondHeckeElem N d) = diamondOp k d := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  rw [diamondHeckeElem_eq_single γ hγ, heckeSlashGamma1RingModularFormLinearMap_single,
    heckeSlashGamma1ModularFormEnd_diamondCosetGamma1, hγ, one_smul]

/-- **The diamond element of the Hecke ring acts on cusp forms by the diamond operator**: the
cusp-form counterpart of `heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem`, read
through the `ℤ`-linear action `heckeSlashGamma1CuspRingLinearMap` on `S_k(Γ₁(N))`. -/
@[simp] theorem heckeSlashGamma1CuspRingLinearMap_diamondHeckeElem (d : (ZMod N)ˣ) :
    heckeSlashGamma1CuspRingLinearMap k (diamondHeckeElem N d) = diamondOpCusp k d := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  rw [diamondHeckeElem_eq_single γ hγ, heckeSlashGamma1CuspRingLinearMap_single,
    heckeSlashGamma1CuspFormEnd_diamondCosetGamma1, hγ, one_smul]

end HeckeRing.GL2

end
