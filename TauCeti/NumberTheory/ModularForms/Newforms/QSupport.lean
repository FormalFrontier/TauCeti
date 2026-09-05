/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Cusp forms whose `q`-expansion is supported on multiples of `d`

A power series is *supported on multiples of `d`* when every coefficient at an index not
divisible by `d` vanishes. This is the coefficient condition behind the Atkin–Lehner description
of the old subspace, and this file bundles it on cusp forms: the forms of level `Γ₁(N)` whose
period-1 `q`-expansion satisfies it form a submodule, and the image of the level-raising operator
`V_d` lies inside it. That containment is the **forward inclusion**; the converse — that every
such form is in the image, which is what would make the description exact — is not proved here
and needs hypotheses this file does not carry.

Neither half of the underlying material is stated here. The power-series predicate is generic and
lives in `TauCeti/RingTheory/PowerSeries/Support.lean`, from which this file pulls
`PowerSeries.supportedOnDvdSubmodule` back along the `q`-expansion; the fact that a level-raise
satisfies it is a statement about `V_d` and lives beside `V_d` in
`TauCeti/NumberTheory/ModularForms/Degeneracy.lean`, as
`CuspForm.isSupportedOnDvd_qExpansion_levelRaise`.

## Main definitions

* `TauCeti.QExpansionSupportedOnDvd`: the support condition on the period-1 `q`-expansion of a
  cusp form.
* `TauCeti.qSupportedOnDvdSubmodule`: the cusp forms satisfying it, as the pullback of
  `PowerSeries.supportedOnDvdSubmodule` along the `q`-expansion.

## Main results

* `TauCeti.levelRaise_mem_qSupportedOnDvdSubmodule`: for `d * M ∣ N`, the operator `V_d` carries
  `S_k(Γ₁(M))` into the submodule — the forward half of the Atkin–Lehner description of the old
  subspace.
* `TauCeti.range_levelRaise_le_qSupportedOnDvdSubmodule`: the same statement for the `ℂ`-linear
  map, which is the shape `TauCeti.cuspFormsOld` is assembled from.
* `TauCeti.iSup_range_levelRaise_le_qSupportedOnDvdSubmodule`: at a fixed `d`, the span of those
  ranges over **every** `M` with `d * M ∣ N` lies in the submodule.

The source reaches the same conclusion through a cast between cusp-form spaces at equal levels
(`castCuspFormLinearEquiv`, `castLevelRaise`); that scaffolding is not ported, because this
repository's `CuspForm.levelRaiseₗ` accepts the divisibility hypothesis directly via
`Gamma1_map_le_conjAct_scaleGL_of_dvd` and lands at `Γ₁(N)` with no cast — exactly as
`cuspFormsOld` itself does.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean`, declarations
`QExpansionSupportedOnDvd`, `qSupportedOnDvdSubmodule` and
`levelRaise_mem_qSupportedOnDvdSubmodule`, with
`range_levelRaise_le_qSupportedOnDvdSubmodule` the cast-free form of the source's
`range_castLevelRaise_le_qSupportedOnDvdSubmodule`.

Two further declarations of the source, `qExpansion_modularFormLevelRaise_isSupportedOnDvd` and
`qExpansion_levelRaise_isSupportedOnDvd`, are in `Degeneracy.lean` as
`ModularForm.isSupportedOnDvd_qExpansion_levelRaise` and its cusp-form counterpart; the
underlying power-series predicate `PowerSeries.IsSupportedOnDvd` comes from the same source file
but is in `TauCeti/RingTheory/PowerSeries/Support.lean`. Each carries its own AINTLIB
provenance where it lives — `Degeneracy.lean`'s References for the two `V_d` lemmas,
`Support.lean`'s Provenance for the predicate.

`qSupportedOnDvdSubmodule` is not a transcription: the source builds the submodule by hand,
discharging `zero_mem'`, `add_mem'` and `smul_mem'` from the predicate's closure lemmas, whereas
here it is the `comap` of `PowerSeries.supportedOnDvdSubmodule` along the `q`-expansion, so that
closure is inherited from the linearity already bundled into `ModularForm.qExpansionLinearMap`.

The source's `modularFormLevelRaise`/`levelRaise` name pair is this repository's
`ModularForm.levelRaise`/`CuspForm.levelRaise`, distinguished by namespace rather than by prefix.

The source keeps the predicate and its modular-form consequences in one file, inside its
`HeckeRing.GL2.AtkinLehner` namespace. Here the predicate is a statement about power series
alone and the level-raising statement belongs with `V_d`, so what the source keeps together is
split across three files.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7.
* Atkin–Lehner, *Hecke operators on* `Γ₀(m)`, Math. Ann. **185** (1970).
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

section QExpansion

variable {M d : ℕ} [NeZero M] [NeZero d] {k : ℤ}

/-- A cusp form is **`q`-supported on multiples of `d`** when its period-1 `q`-expansion is. -/
def QExpansionSupportedOnDvd (d : ℕ) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : Prop :=
  PowerSeries.IsSupportedOnDvd d (qExpansion 1 f)

omit [NeZero M] [NeZero d] in
/-- `QExpansionSupportedOnDvd` restated as an `Iff`, so it rewrites onto the power-series
predicate rather than being unfolded by defeq. -/
theorem qExpansionSupportedOnDvd_iff {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    QExpansionSupportedOnDvd d f ↔ PowerSeries.IsSupportedOnDvd d (qExpansion 1 f) := (Iff.rfl)

/-- The submodule of cusp forms of level `Γ₁(M)` whose period-1 `q`-expansion is supported on
multiples of `d`, as the pullback of `PowerSeries.supportedOnDvdSubmodule` along the
`q`-expansion. Taking it as a `comap` is what supplies closure under the module operations: that
is the linearity already bundled into `ModularForm.qExpansionLinearMap`, which holds because `1`
is a strict period. -/
noncomputable def qSupportedOnDvdSubmodule (M : ℕ) (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :=
  (PowerSeries.supportedOnDvdSubmodule ℂ d).comap
    ((ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map M) k).comp
      CuspForm.toModularFormₗ)

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule` is the `q`-support condition. -/
@[simp]
theorem mem_qSupportedOnDvdSubmodule {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔ QExpansionSupportedOnDvd d f := by
  -- The `comap` is taken along the inclusion into `ModularForm`, which changes nothing
  -- pointwise, so the two `q`-expansions are the same function.
  have hcoe : ⇑(CuspForm.toModularFormₗ f) = ⇑f := funext (CuspForm.toModularFormₗ_apply f)
  simp [qSupportedOnDvdSubmodule, QExpansionSupportedOnDvd,
    ModularForm.qExpansionLinearMap_apply, hcoe]

omit [NeZero M] [NeZero d] in
/-- Membership in `qSupportedOnDvdSubmodule`, spelled out on coefficients. -/
theorem mem_qSupportedOnDvdSubmodule_iff {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} :
    f ∈ qSupportedOnDvdSubmodule M k d ↔
      ∀ n : ℕ, ¬ d ∣ n → (qExpansion 1 f).coeff n = 0 :=
  mem_qSupportedOnDvdSubmodule.trans PowerSeries.isSupportedOnDvd_iff

/-- **Level-raising into a divisible level lands in the supported submodule.** For `d * M ∣ N`,
the operator `V_d` carries `S_k(Γ₁(M))` into the cusp forms whose `q`-expansion is supported on
multiples of `d` — the forward half of the Atkin–Lehner description of the old subspace. -/
theorem levelRaise_mem_qSupportedOnDvdSubmodule {N : ℕ} (M : ℕ)
    (h : d * M ∣ N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g ∈
      qSupportedOnDvdSubmodule N k d :=
  mem_qSupportedOnDvdSubmodule.mpr <|
    CuspForm.isSupportedOnDvd_qExpansion_levelRaise (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map N) (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g

/-- **The range of `V_d` lies in the supported submodule.** Stated for the `ℂ`-linear map, which is
the shape `TauCeti.cuspFormsOld` is assembled from, so the old subspace is contained in the
supported submodule divisor by divisor. -/
theorem range_levelRaise_le_qSupportedOnDvdSubmodule {N : ℕ} (M : ℕ) (h : d * M ∣ N) :
    LinearMap.range (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h)) ≤
      qSupportedOnDvdSubmodule N k d := by
  rintro _ ⟨g, rfl⟩
  simpa only [CuspForm.levelRaiseₗ_apply] using levelRaise_mem_qSupportedOnDvdSubmodule M h g

/-- **At a fixed `d`, every level-raise into `Γ₁(N)` is supported on multiples of `d`.** The span
of the ranges of `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))` over every `M` with `d * M ∣ N` lies in the
supported submodule.

This is deliberately *not* the fixed-`d` summand family of `TauCeti.cuspFormsOld`: that one
carries the proper-level condition `M ≠ N`, which the supremum here does not, so at `d = 1` this
one includes `M = N` and hence the identity range. It is the wider statement, and it is what the
Atkin–Lehner Main Lemma consumes at a fixed `d > 1`. No bound of this kind holds for
`cuspFormsOld` itself, whose supremum also runs over `d = 1`, where `V₁` is restriction and
imposes no support condition. -/
theorem iSup_range_levelRaise_le_qSupportedOnDvdSubmodule (N : ℕ) :
    ⨆ (M : ℕ) (h : d * M ∣ N),
      LinearMap.range (CuspForm.levelRaiseₗ (k := k) d (Gamma1_map_le_conjAct_scaleGL_of_dvd h)) ≤
        qSupportedOnDvdSubmodule N k d :=
  iSup_le fun M ↦ iSup_le fun h ↦ range_levelRaise_le_qSupportedOnDvdSubmodule M h

end QExpansion

end TauCeti

end
