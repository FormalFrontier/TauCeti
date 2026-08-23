/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# The Hecke ring acting on cusp forms

`heckeSlashGamma1CuspFormEnd` attaches a `ℂ`-linear endomorphism of `S_k(Γ₁(N))` to a single
double coset. This file extends that assignment `ℤ`-linearly to the whole Hecke ring
`𝕋 Δ₀(N) Γ₁(N) ℤ`, so that the abstract ring acts on the space of cusp forms.

The extension is `Finsupp.linearCombination` at the coefficient ring `ℤ`, so linearity in the
ring element is inherited rather than reproved: `map_zero` and `map_add` apply directly. What
is specific to this setting is the value on a basis element and on the ring identity, proved
below. Multiplicativity — Shimura's Proposition 3.37 — is *not* proved here, so this is
deliberately a `ℤ`-linear map and not yet a `RingHom`.

## Main definitions

* `heckeSlashGamma1CuspRingLinearMap`: the `ℤ`-linear extension of
  `heckeSlashGamma1CuspFormEnd` to the Hecke ring.

## Main results

* `heckeSlashGamma1CuspRingLinearMap_single`: the value on a basis element is the scaled
  operator of that double coset.
* `heckeSlashGamma1CuspRingLinearMap_one`: the ring identity acts by the operator of the
  identity double coset.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

public section

variable {N : ℕ} [NeZero N] (k : ℤ)

/-- **The Hecke ring acting on cusp forms**: the `ℤ`-linear extension of
`heckeSlashGamma1CuspFormEnd` from a single double coset to a formal `ℤ`-combination of
them.

Multiplicativity is Shimura's Proposition 3.37 and is not available yet, so the Hecke ring
acts `ℤ`-linearly here rather than by a `RingHom`. -/
noncomputable def heckeSlashGamma1CuspRingLinearMap :
    𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ →ₗ[ℤ]
      Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Finsupp.linearCombination ℤ (heckeSlashGamma1CuspFormEnd k)

/-- The action on a basis element is the scaled operator of that double coset. -/
@[simp] lemma heckeSlashGamma1CuspRingLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
    (c : ℤ) :
    heckeSlashGamma1CuspRingLinearMap (N := N) k (HeckeCosetModule.single ℤ D c) =
      c • heckeSlashGamma1CuspFormEnd k D :=
  HeckeCosetModule.sum_single_index ℤ (by simp)

/-- The identity of the Hecke ring acts by the operator of the identity double coset. -/
@[simp] lemma heckeSlashGamma1CuspRingLinearMap_one :
    heckeSlashGamma1CuspRingLinearMap (N := N) k 1 =
      heckeSlashGamma1CuspFormEnd k (1 : HeckeCoset (Delta0 N)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))) := by
  rw [HeckeCosetModule.one_def, heckeSlashGamma1CuspRingLinearMap_single, one_smul]

end

end HeckeRing.GL2
