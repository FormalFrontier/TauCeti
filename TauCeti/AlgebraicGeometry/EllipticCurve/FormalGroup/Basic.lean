/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Fin2
public import Mathlib.RingTheory.FormalGroup.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The formal group law of a Weierstrass curve

The chord construction at the point at infinity gives an addition series `formalAdd W`. This file
packages that series as Mathlib's one-dimensional `FormalGroup`: the two variables are reindexed
from the named sum `Unit ⊕ Unit` to `Fin 2`, and the previously established constant, linear, and
associativity identities supply the structure fields.

The resulting formal group is commutative because the chord addition series is symmetric. Thus
Mathlib's `FormalGroup.Point` construction gives an additive commutative monoid of nilpotent
parameters in every multivariate power-series ring.

## Main definitions

* `WeierstrassCurve.formalGroup`: the one-dimensional formal group law attached to a Weierstrass
  curve.

## Main results

* `WeierstrassCurve.formalGroup_isComm`: the elliptic formal group law is commutative.
* `WeierstrassCurve.map_formalGroup`: the construction commutes with base change.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

The addition series and its laws are adapted in the imported modules from Michael Stoll's
`EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`. The packaging here is original: that source uses its
own formal-group-law structure, whereas this development refounds the construction on Mathlib's
`RingTheory/FormalGroup` API.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R]

private def unitSumUnitSumUnitEquivFinThree : (Unit ⊕ Unit ⊕ Unit) ≃ Fin 3 :=
  (Equiv.sumCongr finOneEquiv.symm unitSumUnitEquivFinTwo).trans finSumFinEquiv

/-- The one-dimensional commutative formal group law of a Weierstrass curve, obtained by
reindexing the chord addition series from `Unit ⊕ Unit` to Mathlib's `Fin 2` convention. -/
noncomputable def formalGroup (W : WeierstrassCurve R) : FormalGroup R where
  toPowerSeries := rename unitSumUnitEquivFinTwo (formalAdd W)
  zero_constantCoeff := by simp
  lin_coeff_X := coeff_single_zero_rename_unitSumUnitEquivFinTwo_formalAdd W
  lin_coeff_Y := coeff_single_one_rename_unitSumUnitEquivFinTwo_formalAdd W
  assoc := by
    -- First expose both nested substitutions through `subst_rename`; these are the two sides of
    -- Mathlib's `FormalGroup.assoc`, still expressed on the original two-variable index.
    have hzero : constantCoeff (rename unitSumUnitEquivFinTwo (formalAdd W)) = 0 := by simp
    obtain hleft := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hzero
    obtain hright := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hzero
    rw [MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ hleft,
      MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ hright]
    rw [MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X,
      MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
    have h₀₁ : HasSubst
        (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
          (fun _ ↦ X (Sum.inr (Sum.inl ())))) := hasSubst_pair (by simp) (by simp)
    have h₁₂ : HasSubst
        (Sum.elim (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
          MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)) (fun _ ↦ X (Sum.inr (Sum.inr ())))) :=
      hasSubst_pair (by simp) (by simp)
    have hz₀₁ : constantCoeff (subst
        (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
          (fun _ ↦ X (Sum.inr (Sum.inl ())))) (formalAdd W)) = 0 :=
      constantCoeff_subst_eq_zero h₀₁ (by rintro (u | u) <;> simp) (constantCoeff_formalAdd W)
    have hz₁₂ : constantCoeff (subst
        (Sum.elim (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
          MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)) (fun _ ↦ X (Sum.inr (Sum.inr ()))))
          (formalAdd W)) = 0 :=
      constantCoeff_subst_eq_zero h₁₂ (by rintro (u | u) <;> simp) (constantCoeff_formalAdd W)
    have hsourceLeft : HasSubst
        (Sum.elim (fun _ ↦ subst
            (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
              (fun _ ↦ X (Sum.inr (Sum.inl ())))) (formalAdd W))
          (fun _ ↦ X (Sum.inr (Sum.inr ())))) := hasSubst_pair hz₀₁ (by simp)
    have hsourceRight : HasSubst
        (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
          (fun _ ↦ subst
            (Sum.elim (fun _ ↦ X (Sum.inr (Sum.inl ())))
              (fun _ ↦ X (Sum.inr (Sum.inr ())))) (formalAdd W))) :=
      hasSubst_pair (by simp) hz₁₂
    have hrename : HasSubst
        (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
    -- Rename the proved three-variable identity. Substitution composition pushes that renaming
    -- through each outer occurrence of `formalAdd`.
    have h := congrArg (rename unitSumUnitSumUnitEquivFinThree) (formalAdd_assoc W)
    simp only [rename_eq_subst] at h
    rw [subst_comp_subst_apply hsourceLeft hrename,
      subst_comp_subst_apply hsourceRight hrename] at h
    -- Expose the outer `finSumFinEquiv` so its left/right evaluation lemmas apply directly.
    have he₀ : unitSumUnitSumUnitEquivFinThree (Sum.inl ()) = 0 := by
      change finSumFinEquiv (Sum.inl (finOneEquiv.symm ())) = 0
      rw [finSumFinEquiv_apply_left]
      rfl
    have he₁ : unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inl ())) = 1 := by
      change finSumFinEquiv (Sum.inr (unitSumUnitEquivFinTwo (Sum.inl ()))) = 1
      rw [unitSumUnitEquivFinTwo_inl]
      rw [finSumFinEquiv_apply_right]
      rfl
    have he₂ : unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inr ())) = 2 := by
      change finSumFinEquiv (Sum.inr (unitSumUnitEquivFinTwo (Sum.inr ()))) = 2
      rw [unitSumUnitEquivFinTwo_inr]
      rw [finSumFinEquiv_apply_right]
      rfl
    -- The remaining two equalities only say that the chosen equivalences send the named first,
    -- second, and third variables to `0`, `1`, and `2` respectively.
    have hfamilyLeft :
        (![subst (![X 0, X 1] ∘ unitSumUnitEquivFinTwo) (formalAdd W), X 2] ∘
            unitSumUnitEquivFinTwo) =
          (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
            (Sum.elim (fun _ ↦ subst
                (Sum.elim (fun _ ↦ (X (Sum.inl ()) :
                  MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
                  (fun _ ↦ X (Sum.inr (Sum.inl ())))) (formalAdd W))
              (fun _ ↦ X (Sum.inr (Sum.inr ()))) s)) := by
      funext s
      rcases s with u | u <;> cases u
      · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl, Matrix.cons_val_zero,
          Sum.elim_inl]
        rw [subst_comp_subst_apply h₀₁ hrename]
        congr 1
        funext t
        rcases t with v | v <;> cases v
        · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl,
            Matrix.cons_val_zero, Sum.elim_inl]
          rw [subst_X hrename, Function.comp_apply, he₀]
        · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, Sum.elim_inr]
          rw [subst_X hrename, Function.comp_apply, he₁]
      · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Sum.elim_inr]
        rw [subst_X hrename, Function.comp_apply, he₂]
    have hfamilyRight :
        (![X 0, subst (![X 1, X 2] ∘ unitSumUnitEquivFinTwo) (formalAdd W)] ∘
            unitSumUnitEquivFinTwo) =
          (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
            (Sum.elim (fun _ ↦ (X (Sum.inl ()) :
                MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
              (fun _ ↦ subst
                (Sum.elim (fun _ ↦ X (Sum.inr (Sum.inl ())))
                  (fun _ ↦ X (Sum.inr (Sum.inr ())))) (formalAdd W)) s)) := by
      funext s
      rcases s with u | u <;> cases u
      · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl, Matrix.cons_val_zero,
          Sum.elim_inl]
        rw [subst_X hrename, Function.comp_apply, he₀]
      · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Sum.elim_inr]
        rw [subst_comp_subst_apply h₁₂ hrename]
        congr 1
        funext t
        rcases t with v | v <;> cases v
        · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl,
            Matrix.cons_val_zero, Sum.elim_inl]
          rw [subst_X hrename, Function.comp_apply, he₁]
        · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, Sum.elim_inr]
          rw [subst_X hrename, Function.comp_apply, he₂]
    rw [hfamilyLeft, hfamilyRight]
    exact h

/-- The underlying `Fin 2`-indexed series of the formal group law is the reindexed chord addition
series. -/
@[simp]
theorem formalGroup_toPowerSeries (W : WeierstrassCurve R) :
    (formalGroup W).toPowerSeries = rename unitSumUnitEquivFinTwo (formalAdd W) :=
  by simp [formalGroup]

/-- Base change of a Weierstrass curve commutes with passage to its formal group law. -/
@[simp]
theorem map_formalGroup {S : Type*} [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S) :
    formalGroup (W.map φ) = (formalGroup W).map φ := by
  apply FormalGroup.ext
  simp [formalGroup, MvPowerSeries.rename_map]

/-- The formal group law of a Weierstrass curve is commutative. This makes its nilpotent
power-series-valued points an additive commutative monoid through Mathlib's standard instance. -/
noncomputable instance formalGroup_isComm (W : WeierstrassCurve R) :
    (formalGroup W).IsComm where
  comm := by
    rw [formalGroup_toPowerSeries,
      MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
    nth_rw 1 [← rename_swap_formalAdd W]
    rw [rename_rename, rename_eq_subst]
    congr 1
    funext s
    rcases s with u | u <;> cases u <;>
      simp [Function.comp_def]

end WeierstrassCurve
