/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.NumberTheory.ModularForms.Norm.Trace

/-!
# The coset data of the norm map to level one

The general-level valence formula reduces to level one along the norm map
`ModularForm.norm`: the norm of a form `f` on a finite-index subgroup `Γ ≤ SL(2, ℤ)` is a
level-one form, and the orders of `f` distribute over its factors. This file sets up the
multiplicative shape of that reduction for a subgroup of `SL(2, ℤ)`: the coset space `Q Γ`
indexing the factors, the product `restProd` of the nontrivial factors — so that the norm
is `f` times `restProd f` — with its boundedness at `Im z → ∞`, and the strict cusp width
of `Γ` as a strict period at level one.

## Main declarations

* `TauCeti.ModularForm.NormReduction.G`, `TauCeti.ModularForm.NormReduction.Q`: a subgroup
  `Γ ≤ SL(2, ℤ)` viewed in `GL(2, ℝ)` (arithmetic for finite index, by Mathlib's instance),
  and the coset space indexing the norm factors.
* `TauCeti.ModularForm.NormReduction.restProd`: the product of the nontrivial slash
  translates, characterized by `restProd_apply` and bounded at `Im z → ∞`.
* `TauCeti.ModularForm.NormReduction.strictWidthInfty_mem_strictPeriods_levelOne`: the
  strict cusp width of `G Γ` is a strict period of the full level-one group.

## References

Reduced from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, the file
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/NormReduction.lean`),
atop Mathlib's `ModularForm.norm` coset API and this repository's `Norm/Trace` helpers.
-/

open scoped MatrixGroups
open UpperHalfPlane

namespace TauCeti.ModularForm.NormReduction

noncomputable section
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- View a subgroup `Γ ≤ SL(2, ℤ)` as a subgroup of `GL(2, ℝ)` via the standard coercion. -/
@[expose, reducible] public def G (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  (Γ : Subgroup (GL (Fin 2) ℝ))

/-- The quotient indexing the factors in the norm product. -/
@[expose, reducible] public def Q (Γ : Subgroup SL(2, ℤ)) : Type :=
  𝒮ℒ ⧸ ((G Γ).subgroupOf 𝒮ℒ)

/-- The strict cusp width of `G Γ` is a strict period of the full level-one group `𝒮ℒ`. -/
public lemma strictWidthInfty_mem_strictPeriods_levelOne (Γ : Subgroup SL(2, ℤ)) :
    (G Γ).strictWidthInfty ∈ ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  have hle : G Γ ≤ 𝒮ℒ := by
    simpa [G] using Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) (H := Γ)
  exact Subgroup.mem_strictPeriods_iff.2 <| hle <|
    Subgroup.mem_strictPeriods_iff.1 (Subgroup.strictWidthInfty_mem_strictPeriods (𝒢 := G Γ))

section RestProd

variable [Γ.FiniteIndex]

/-- The product of all nontrivial quotient factors appearing in the norm formula: the
factors of `ModularForm.norm 𝒮ℒ f` other than `f` itself, so that the norm is
`f * restProd f`. Its value is `restProd_apply`. -/
public noncomputable def restProd (f : ModularForm (G Γ) k) : ℍ → ℂ := by
  let _ : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  let _ : DecidableEq (Q Γ) := Classical.decEq _
  exact (Finset.univ.erase (⟦(1 : 𝒮ℒ)⟧ : Q Γ)).prod fun q ↦
    SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q

/-- The value of `restProd`: the product of the nontrivial quotient factors, for any
choice of the finiteness and decidability instances on the coset space. -/
@[simp] public lemma restProd_apply [Fintype (Q Γ)] [DecidableEq (Q Γ)]
    (f : ModularForm (G Γ) k) (τ : ℍ) :
    restProd f τ = (Finset.univ.erase (⟦(1 : 𝒮ℒ)⟧ : Q Γ)).prod
      (fun q ↦ SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q) τ := by
  unfold restProd
  congr!

/-- The norm of `f` splits off the identity coset: it is `f` times the product of the
nontrivial factors. -/
public lemma norm_apply_eq_mul_restProd (f : ModularForm (G Γ) k) (τ : ℍ) :
    _root_.ModularForm.norm 𝒮ℒ f τ = f τ * restProd f τ := by
  let _ : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  let _ : DecidableEq (Q Γ) := Classical.decEq _
  have hone : SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f
      (⟦(1 : 𝒮ℒ)⟧ : Q Γ) τ = f τ := by
    simp [SlashInvariantForm.quotientFunc_mk]
  calc
    _root_.ModularForm.norm 𝒮ℒ f τ =
        ∏ q : Q Γ, SlashInvariantForm.quotientFunc (ℋ := 𝒮ℒ) (𝒢 := G Γ) (k := k) f q τ := by
      simp [_root_.ModularForm.coe_norm]
    _ = f τ * restProd f τ := by
      rw [restProd_apply, Finset.prod_apply, ← hone]
      exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ _)).symm

/-- The product `restProd` is bounded at `Im z → ∞`. -/
public lemma isBoundedAtImInfty_restProd (f : ModularForm (G Γ) k) :
    IsBoundedAtImInfty (restProd f) := by
  have : Fact (IsCusp OnePoint.infty (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (by simp)⟩
  let _ : Fintype (Q Γ) := Fintype.ofFinite (Q Γ)
  let _ : DecidableEq (Q Γ) := Classical.decEq _
  simpa [IsBoundedAtImInfty, restProd] using
    Filter.BoundedAtFilter.prod (l := atImInfty)
      (s := Finset.univ.erase (⟦(1 : 𝒮ℒ)⟧ : Q Γ)) fun q _ ↦ by
      simpa [IsBoundedAtImInfty] using
        TauCeti.SlashInvariantForm.isBoundedAtImInfty_quotientFunc f q

end RestProd

end

end TauCeti.ModularForm.NormReduction
