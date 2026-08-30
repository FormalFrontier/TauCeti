/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Basic

/-!
# The `ℤ`-linear extension of the twisted slash sum, and the `χ`-invariant function space

`HeckeSlash/Nebentypus/Basic.lean` attaches a `ℂ`-linear endomorphism `twistedHeckeSlashSumEnd` of
`ℍ → ℂ` to a single double coset of `Γ₀(N)`, weighting each summand by the nebentypus character
of its own representative. This file does the two things that assignment needs before it can be
called an action of the Hecke ring on a space of forms.

First it extends the assignment `ℤ`-linearly over the basis of the Hecke ring
`𝕋 Δ₀(N) Γ₀(N) ℤ`, exactly as `HeckeSlash/Ring.lean` does for the untwisted `Γ₁(N)` sum: the
extension is `Finsupp.linearCombination` at the coefficient ring `ℤ`, so linearity in the ring
element is inherited rather than reproved — `map_zero` and `map_add` apply directly, and the one
lemma proved here is the value on a basis element.

Second it names the subspace of `ℍ → ℂ` that the twisting exists to serve: the functions
satisfying the nebentypus relation `f ∣[k] g = χ(d_g) • f` for `g ∈ Γ₀(N)`.

## This is not yet a ring action, and not yet an operator on the character space

Two things are deliberately absent. Multiplicativity of the extension is Shimura §3.4 and is not
proved here, so what is delivered is the `ℤ`-linear assignment only. And the twisted sum is *not*
shown to preserve `functionCharSpace` — that is the pay-off of the weighting and the content of
the next rung; here the extension lands in `Module.End ℂ (ℍ → ℂ)`, endomorphisms of *all*
functions.

## Why the character space is stated for plain functions

`modFormCharSpace` (`ModularForms/DiamondOperators.lean`) is the same condition on bundled
`ModularForm`s, cut out as a joint diamond eigenspace. The twisted slash sum acts on plain
functions and is not yet known to preserve modularity, so it needs the condition at the level of
functions. To keep that from becoming a second, unrelated spelling of a relation the library
already has, `functionCharSpace` is defined by *the very relation* that
`mem_modFormCharSpace_iff_nebentypus` puts on the right-hand side, and
`coe_mem_functionCharSpace_iff` records that a modular form lies in the character space exactly
when its underlying function lies here.

## Main definitions

* `functionCharSpace`: the `χ`-invariant functions `ℍ → ℂ` for `Γ₀(N)`.
* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap`: the `ℤ`-linear extension of
  `twistedHeckeSlashSumEnd` to the Hecke ring.

## Main results

* `coe_mem_functionCharSpace_iff`: the bridge to `modFormCharSpace`.
* `HeckeRing.GL2.twistedHeckeSlashRingLinearMap_single`: the value on a basis element is the
  scaled twisted sum of that double coset. With `map_zero`/`map_add` this determines the map.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 (the action of the Hecke ring on automorphic forms).

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSlashExtGen` and `gamma0TwistedInvariantFunctionSubmodule` these realize. The source
extends by a hand-rolled `Finsupp.sum` and proves additivity separately; here the extension is a
bundled `Finsupp.linearCombination`, so that additivity is `map_add`. The source's
`IsGamma0TwistedInvariant` predicate is not reproduced: its relation is already the right-hand
side of `mem_modFormCharSpace_iff_nebentypus`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm HeckeCosetModule

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- **The `χ`-invariant functions for `Γ₀(N)`**: those `f : ℍ → ℂ` with
`f ∣[k] g = χ(d_g) • f` for every `g ∈ Γ₀(N)`.

This is the nebentypus relation of `mem_modFormCharSpace_iff_nebentypus` read on plain functions
rather than on bundled modular forms, which is the generality the twisted slash sum acts in. -/
def functionCharSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | ∀ g : ↥(Gamma0 N),
    f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f}
  zero_mem' := by simp
  add_mem' := by
    intro f₁ f₂ hf₁ hf₂ g
    rw [SlashAction.add_slash, hf₁ g, hf₂ g, smul_add]
  smul_mem' := by
    intro c f hf g
    rw [ModularForm.smul_slash_of_det_pos k
      (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨_, rfl⟩)), hf g]
    exact smul_comm c _ f

/-- Membership in `functionCharSpace` is the nebentypus relation, by definition.

The carrier is that relation verbatim -- main's own vocabulary for it -- and *not* a joint
eigenspace: unlike `modFormCharSpace`, this is not `⨅ d, eigenspace ...`, because the diamond
operators are built from the slash as a bundled endomorphism of `ModularForm` and have no
counterpart on plain functions. `coe_mem_functionCharSpace_iff` is what ties the two together. -/
@[simp] lemma mem_functionCharSpace_iff (f : ℍ → ℂ) :
    f ∈ functionCharSpace k χ ↔ ∀ g : ↥(Gamma0 N),
      f ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := Iff.rfl

/-- **Bridge to the modular-form character space**: a modular form lies in `modFormCharSpace k χ`
exactly when its underlying function is `χ`-invariant. Both sides are the same relation; this
records that `functionCharSpace` is not a second notion. -/
lemma coe_mem_functionCharSpace_iff (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑f) ∈ functionCharSpace k χ ↔ f ∈ modFormCharSpace k χ :=
  (mem_modFormCharSpace_iff_nebentypus k χ f).symm

namespace HeckeRing.GL2

-- `twistedHeckeSlashSumEnd` needs `[NeZero N]` to know its index type is finite; the
-- function-space material above does not, so the instance is introduced only here.
variable [NeZero N]

/-- The `ℤ`-linear extension of `twistedHeckeSlashSumEnd` to formal `ℤ`-combinations of double
cosets of `Γ₀(N)`: `ℤ`-linear in the ring element, but not known to be multiplicative, so this is
not yet a ring action.

`𝕋 Δ H ℤ` unfolds to `HeckeCoset Δ H H →₀ ℤ` carrying the transported module structure, which is
why `Finsupp.linearCombination` applies at this type. -/
noncomputable def twistedHeckeSlashRingLinearMap :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (ℍ → ℂ) :=
  -- Eta-expanded on purpose: `Nebentypus.lean` introduces `[NeZero N]` *after* the double
  -- coset in its `variable` block, so the partial application `twistedHeckeSlashSumEnd k χ`
  -- still expects the instance and does not have the function type `linearCombination` wants.
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashSumEnd k χ D

/-- The value on a basis element is the scaled twisted slash sum of that double coset. -/
@[simp] lemma twistedHeckeSlashRingLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
    (c : ℤ) :
    twistedHeckeSlashRingLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashSumEnd k χ D :=
  -- Mirrors `heckeSlashGamma1RingModularFormLinearMap_single`: `Finsupp.linearCombination_single`
  -- does not apply, since `HeckeCosetModule.single` is a separate, non-exposed `def`.
  (Finsupp.linearCombination_apply (R := ℤ) (v := fun D ↦ twistedHeckeSlashSumEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

end HeckeRing.GL2

end
