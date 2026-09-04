/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Sum
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Renaming the variables of a multivariate power series

Two gaps in Mathlib's `rename` API, each about comparing a renaming with another operation on the
same series, and one consequence of them: that reindexing a two-variable series along
`unitSumUnitEquivFinTwo` carries an associativity identity with it.

Substituting after renaming is the substitution along the renamed index: Mathlib has both
operations and the law that lets them be compared — `rename_eq_subst`, which says a renaming *is*
the substitution sending each variable to a variable — but not the comparison itself, which is
what a caller reindexing a series needs.

Reading the coefficient of a single-variable monomial through a renaming along an embedding is
likewise available only through `coeff_embDomain_rename`, which speaks about `Finsupp.embDomain`;
at one variable raised to an arbitrary power the `single (e i) n` spelling is the more usable one.

Associativity is where the two spellings of a two-variable series genuinely diverge: the named
form substitutes an already-substituted series through `Sum.elim`, the `Fin 2` form through a
`Matrix.cons` family over `Fin 3`. Transporting the identity therefore means reindexing the
three-variable ambient ring as well, along `unitSumUnitSumUnitEquivFinThree`.

## Main results

* `MvPowerSeries.subst_rename`: substituting into `rename e p` reindexes the family, i.e. it is
  substituting `g ∘ e` into `p`.
* `MvPowerSeries.coeff_single_rename`: the coefficient of `rename e p` at the single-variable
  monomial `single (e i) n` is the coefficient of `p` at `single i n`, for any exponent `n`.
* `MvPowerSeries.rename_unitSumUnitEquivFinTwo_assoc`: reindexing a two-variable associative
  series from `Unit ⊕ Unit` to `Fin 2` preserves its associativity identity.

## Provenance

No external source. The first two statements are gaps in Mathlib's `MvPowerSeries` API and each
proof is a few steps of that same API; the third is the reindexing they were extracted for, and
its proof rewrites both sides of the identity through the three-variable renaming. All three are
recorded here rather than inside their callers because they carry no elliptic content.
-/

public section

namespace MvPowerSeries

open Filter Finsupp

variable {σ τ υ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- **A single-variable monomial's coefficient survives a renaming along an embedding**, for any
exponent `n`. Mathlib's `coeff_embDomain_rename` states this through `Finsupp.embDomain`; at one
variable the `single (e i) n` spelling is the one a caller meets. -/
@[simp]
theorem coeff_single_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (i : σ) (n : ℕ) :
    coeff (single (e i) n) (rename e p) = coeff (single i n) p := by
  rw [← embDomain_single, coeff_embDomain_rename]

end CommSemiring

section CommRing

variable [CommRing R]

private theorem rename_unitSumUnitEquivFinTwo_assoc_left_family
    (p : MvPowerSeries (Unit ⊕ Unit) R) :
    (![subst (![X 0, X 1] ∘ unitSumUnitEquivFinTwo) p, X 2] ∘
        unitSumUnitEquivFinTwo) =
      (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
        (Sum.elim (fun _ ↦ subst
            (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
              (fun _ ↦ X (Sum.inr (Sum.inl ())))) p)
          (fun _ ↦ X (Sum.inr (Sum.inr ()))) s)) := by
  have h₀₁ : HasSubst
      (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
        (fun _ ↦ X (Sum.inr (Sum.inl ())))) := hasSubst_pair (by simp) (by simp)
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  funext s
  rcases s with u | u <;> cases u
  · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl, Matrix.cons_val_zero,
      Sum.elim_inl]
    rw [subst_comp_subst_apply h₀₁ hrename]
    congr 1
    funext t
    rcases t with v | v <;> cases v
    · simp [subst_X hrename]
    · simp [subst_X hrename]
  · simp [subst_X hrename]

private theorem rename_unitSumUnitEquivFinTwo_assoc_right_family
    (p : MvPowerSeries (Unit ⊕ Unit) R) :
    (![X 0, subst (![X 1, X 2] ∘ unitSumUnitEquivFinTwo) p] ∘
        unitSumUnitEquivFinTwo) =
      (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
        (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
          (fun _ ↦ subst
            (Sum.elim (fun _ ↦ X (Sum.inr (Sum.inl ())))
              (fun _ ↦ X (Sum.inr (Sum.inr ())))) p) s)) := by
  have h₁₂ : HasSubst
      (Sum.elim (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)) (fun _ ↦ X (Sum.inr (Sum.inr ())))) :=
    hasSubst_pair (by simp) (by simp)
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  funext s
  rcases s with u | u <;> cases u
  · simp [subst_X hrename]
  · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Sum.elim_inr]
    rw [subst_comp_subst_apply h₁₂ hrename]
    congr 1
    funext t
    rcases t with v | v <;> cases v
    · simp [subst_X hrename]
    · simp [subst_X hrename]

/-- **Substituting into a renamed series reindexes the family**: `rename e p` followed by
substituting `g` is `p` with `g ∘ e` substituted.

Both hypotheses are the ones the two operations already carry: `rename` needs `e` to have finite
fibres (`TendstoCofinite`) for the renamed coefficients to be well defined, and `subst` needs
`HasSubst g`. Nothing is assumed about `e` beyond that — in particular it need not be injective,
since a collision merely substitutes the same series for two variables. -/
theorem subst_rename (e : σ → τ) [TendstoCofinite e] (p : MvPowerSeries σ R)
    {g : τ → MvPowerSeries υ R} (hg : HasSubst g) :
    (rename e p).subst g = p.subst (g ∘ e) := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hg]
  simp [subst_X hg, Function.comp_def]

/-- Reindexing an associative two-variable series from `Unit ⊕ Unit` to `Fin 2` preserves
associativity in Mathlib's three-variable convention.

The source identity uses the named left, middle, and right variables supplied by the nested sum;
the target is exactly the identity expected by `FormalGroup.assoc`. -/
theorem rename_unitSumUnitEquivFinTwo_assoc (p : MvPowerSeries (Unit ⊕ Unit) R)
    (hp : constantCoeff p = 0)
    (hassoc :
      subst (Sum.elim
          (fun _ ↦ subst (Sum.elim
              (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
              (fun _ ↦ X (Sum.inr (Sum.inl ())))) p)
          (fun _ ↦ X (Sum.inr (Sum.inr ())))) p =
        subst (Sum.elim
          (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
          (fun _ ↦ subst
            (Sum.elim (fun _ ↦ X (Sum.inr (Sum.inl ())))
              (fun _ ↦ X (Sum.inr (Sum.inr ())))) p)) p) :
    subst ![subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1]
        (rename unitSumUnitEquivFinTwo p), X 2]
        (rename unitSumUnitEquivFinTwo p) =
      subst ![(X 0 : MvPowerSeries (Fin 3) R),
        subst ![X 1, X 2] (rename unitSumUnitEquivFinTwo p)]
        (rename unitSumUnitEquivFinTwo p) := by
  have hzero : constantCoeff (rename unitSumUnitEquivFinTwo p) = 0 := by simp [hp]
  obtain hleft := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hzero
  obtain hright := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hzero
  rw [subst_rename unitSumUnitEquivFinTwo _ hleft,
    subst_rename unitSumUnitEquivFinTwo _ hright]
  rw [subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X,
    subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
  have h₀₁ : HasSubst
      (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
        (fun _ ↦ X (Sum.inr (Sum.inl ())))) := hasSubst_pair (by simp) (by simp)
  have h₁₂ : HasSubst
      (Sum.elim (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)) (fun _ ↦ X (Sum.inr (Sum.inr ())))) :=
    hasSubst_pair (by simp) (by simp)
  have hz₀₁ : constantCoeff (subst
      (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
        (fun _ ↦ X (Sum.inr (Sum.inl ())))) p) = 0 :=
    constantCoeff_subst_eq_zero h₀₁ (by rintro (u | u) <;> simp) hp
  have hz₁₂ : constantCoeff (subst
      (Sum.elim (fun _ ↦ (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)) (fun _ ↦ X (Sum.inr (Sum.inr ())))) p) = 0 :=
    constantCoeff_subst_eq_zero h₁₂ (by rintro (u | u) <;> simp) hp
  have hsourceLeft : HasSubst
      (Sum.elim (fun _ ↦ subst
          (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
            (fun _ ↦ X (Sum.inr (Sum.inl ())))) p)
        (fun _ ↦ X (Sum.inr (Sum.inr ())))) := hasSubst_pair hz₀₁ (by simp)
  have hsourceRight : HasSubst
      (Sum.elim (fun _ ↦ (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R))
        (fun _ ↦ subst
          (Sum.elim (fun _ ↦ X (Sum.inr (Sum.inl ())))
            (fun _ ↦ X (Sum.inr (Sum.inr ())))) p)) := hasSubst_pair (by simp) hz₁₂
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  have h := congrArg (rename unitSumUnitSumUnitEquivFinThree) hassoc
  simp only [rename_eq_subst] at h
  rw [subst_comp_subst_apply hsourceLeft hrename,
    subst_comp_subst_apply hsourceRight hrename] at h
  rw [rename_unitSumUnitEquivFinTwo_assoc_left_family p,
    rename_unitSumUnitEquivFinTwo_assoc_right_family p]
  exact h

end CommRing

end MvPowerSeries
