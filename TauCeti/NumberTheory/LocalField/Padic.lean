/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# The `p`-adic numbers are a nonarchimedean local field

Mathlib equips `ℚ_[p]` with a `ValuativeRel`, coming from `Padic.mulValuation`, but leaves the
comparison with the `p`-adic metric open: nothing says that the topology of `ℚ_[p]` is the one
its valuation prescribes. This file supplies that comparison and the resulting instance
`IsNonarchimedeanLocalField ℚ_[p]`, which is what makes `ℚ_[p]` a model of the general
local-field theory rather than an unrelated normed field.

Two consequences worth naming are recorded afterwards. The valuation integers `𝒪[ℚ_[p]]` are the
subring `ℤ_[p]`, and the residue field `𝓀[ℚ_[p]]` is `ZMod p`, so the residue cardinality of
`ℚ_[p]` is `p`.

## Main results

* `TauCeti.Padic.instIsValuativeTopology`: the `p`-adic metric topology is the valuative topology.
* `TauCeti.Padic.instIsNonarchimedeanLocalField`: `ℚ_[p]` is a nonarchimedean local field.
* `TauCeti.Padic.integer_eq_padicIntSubring` and `TauCeti.Padic.integerRingEquiv`: the valuation
  integers of `ℚ_[p]` are `ℤ_[p]`.
* `TauCeti.Padic.residueFieldEquiv` and `TauCeti.Padic.card_residueField`: the residue field of
  `ℚ_[p]` is `ZMod p`, of cardinality `p`.

The uniform structure carried by `ℚ_[p]` is the metric one, whereas the uniform-space
consequences of `IsNonarchimedeanLocalField` — `CompleteSpace ℚ_[p]`, `CompleteSpace 𝒪[ℚ_[p]]`
and `IsAdicComplete 𝓂[ℚ_[p]] 𝒪[ℚ_[p]]` — are stated for an arbitrary uniformity making the
addition uniformly continuous. `IsUniformAddGroup.rightUniformSpace_eq` says that such a
uniformity is the one of the underlying topological group, so no comparison specific to `ℚ_[p]`
is needed and those instances are found by inference; the `example`s at the end of the file
check that they are.
-/

public section

open ValuativeRel

namespace TauCeti.Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic norm defines the same valuative relation on `ℚ_[p]` as `Padic.mulValuation`. -/
instance instCompatibleNormedFieldValuation :
    (_root_.NormedField.valuation (K := ℚ_[p])).Compatible where
  vle_iff_le x y := by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation)]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hx]
    · rw [_root_.NormedField.valuation_apply, _root_.NormedField.valuation_apply,
        ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Padic.norm_eq_zpow_neg_valuation hx,
        Padic.norm_eq_zpow_neg_valuation hy, zpow_le_zpow_iff_right₀ (mod_cast hp.out.one_lt)]
      simp [Padic.mulValuation, hx, hy]

/-- The `p`-adic metric topology on `ℚ_[p]` is the topology of its valuation. -/
instance instIsValuativeTopology : IsValuativeTopology ℚ_[p] :=
  NormedField.isValuativeTopology

/-- `ℚ_[p]` is a nonarchimedean local field. -/
instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where

/-- The valuation integers of `ℚ_[p]` are the subring `ℤ_[p]` of `ℚ_[p]`. -/
theorem integer_eq_padicIntSubring : 𝒪[ℚ_[p]] = PadicInt.subring p := by
  ext x
  simp [NormedField.mem_integer_iff_norm_le_one]

/-- The ring of integers of the local field `ℚ_[p]` is the ring `ℤ_[p]` of `p`-adic integers. -/
noncomputable def integerRingEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p] :=
  (RingEquiv.refl ℚ_[p]).restrict _ (PadicInt.subring p) fun _ ↦
    NormedField.mem_integer_iff_norm_le_one.trans (PadicInt.mem_subring_iff p).symm

/-- `integerRingEquiv` is the identity on the underlying `p`-adic numbers. -/
@[simp]
theorem coe_integerRingEquiv (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquiv p x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) := (rfl)

/-- The inverse of `integerRingEquiv` is the identity on the underlying `p`-adic numbers. -/
@[simp]
theorem coe_integerRingEquiv_symm (x : ℤ_[p]) :
    (((integerRingEquiv p).symm x : 𝒪[ℚ_[p]]) : ℚ_[p]) = (x : ℚ_[p]) := (rfl)

/-- The residue field of `ℚ_[p]` is `ZMod p`. -/
noncomputable def residueFieldEquiv : 𝓀[ℚ_[p]] ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (integerRingEquiv p)).trans PadicInt.residueField

/-- `residueFieldEquiv` sends the residue of `x` to the reduction of `x` modulo `p`. -/
@[simp]
theorem residueFieldEquiv_residue (x : 𝒪[ℚ_[p]]) :
    residueFieldEquiv p (IsLocalRing.residue _ x) = PadicInt.toZMod (integerRingEquiv p x) := by
  simp [residueFieldEquiv, IsLocalRing.ResidueField.map_residue,
    PadicInt.toZMod_eq_residueField_comp_residue]

/-- The residue cardinality of `ℚ_[p]` is `p`. -/
@[simp]
theorem card_residueField : Nat.card 𝓀[ℚ_[p]] = p := by
  rw [Nat.card_congr (residueFieldEquiv p).toEquiv, Nat.card_zmod]

-- The uniform-space consequences of `IsNonarchimedeanLocalField` fire for the metric uniformity
-- of `ℚ_[p]`, with no comparison of uniformities supplied by hand.
example : CompleteSpace ℚ_[p] := inferInstance
example : CompleteSpace 𝒪[ℚ_[p]] := inferInstance
example : IsAdicComplete 𝓂[ℚ_[p]] 𝒪[ℚ_[p]] := inferInstance

end TauCeti.Padic
