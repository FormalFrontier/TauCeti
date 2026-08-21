/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# The upper-triangular Hecke slash sum is invariant under `T`

The classical upper-triangular Hecke sum `heckeSlashUpperTri k p f = ∑ b < p, f ∣[k] !![1, b; 0, p]`
preserves invariance under the translation matrix `T = !![1, 1; 0, 1]`.

Right multiplication of the representative `!![1, b; 0, p]` by `T` produces `!![1, b + 1; 0, p]`.
For `b < p - 1`, this is the `(b + 1)`-st representative; for `b = p - 1`, it factors as
`T · !![1, 0; 0, p]`. When `f` is `T`-slash invariant (`f ∣[k] T = f`), the `T` factor on the
boundary term is absorbed, so slashing the whole sum by `T` cyclically permutes the summands via
`finRotate p` and recovers `heckeSlashUpperTri k p f`.

Pointwise on `ℍ`, `f ∣[k] T = f` is the 1-periodicity `f(τ + 1) = f(τ)`, so the upper-triangular
sum sends 1-periodic functions to 1-periodic functions.

## Main results

* `HeckeRing.GL2.upperTriRep_mul_mapGL_T_of_lt`: for `b.val + 1 < p`,
  `upperTriRep p b * mapGL ℚ ModularGroup.T = upperTriRep p ⟨b.val + 1, _⟩`.
* `HeckeRing.GL2.upperTriRep_last_mul_mapGL_T`: for `b.val + 1 = p`,
  `upperTriRep p b * mapGL ℚ ModularGroup.T = mapGL ℚ ModularGroup.T * upperTriRep p ⟨0, _⟩`.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_T`: if `f ∣[k] mapGL ℚ ModularGroup.T = f`, then
  `heckeSlashUpperTri k p f ∣[k] mapGL ℚ ModularGroup.T = heckeSlashUpperTri k p f`.
* `HeckeRing.GL2.heckeSlashUpperTri_shift_one`: if `f((1 : ℝ) +ᵥ τ) = f(τ)` for all `τ`, then
  `heckeSlashUpperTri k p f ((1 : ℝ) +ᵥ τ) = heckeSlashUpperTri k p f τ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (p : ℕ)

/-- For `b.val + 1 < p`, right multiplication of `upperTriRep p b` by `T` shifts the offset
to `b + 1`. -/
lemma upperTriRep_mul_mapGL_T_of_lt (b : Fin p) (hb : b.val + 1 < p) :
    upperTriRep p b * mapGL ℚ ModularGroup.T = upperTriRep p ⟨b.val + 1, hb⟩ := by
  apply Units.ext
  rw [Units.val_mul, coe_upperTriRep, coe_upperTriRep]
  ext ⟨_ | _ | _, _⟩ ⟨_ | _ | _, _⟩ <;> try contradiction
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm, mapGL_coe_matrix,
    ModularGroup.coe_T]

/-- For the last representative `b.val + 1 = p`, right multiplication by `T` factors as
`T · upperTriRep p 0`. -/
lemma upperTriRep_last_mul_mapGL_T (b : Fin p) (hb : b.val + 1 = p) :
    upperTriRep p b * mapGL ℚ ModularGroup.T =
      mapGL ℚ ModularGroup.T * upperTriRep p ⟨0, b.pos⟩ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_upperTriRep, coe_upperTriRep]
  have hbp : (b : ℚ) + 1 = (p : ℚ) := by
    have : (b.val : ℚ) + 1 = (p : ℚ) := by exact_mod_cast hb
    exact this
  ext ⟨_ | _ | _, _⟩ ⟨_ | _ | _, _⟩ <;> try contradiction
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix, ModularGroup.coe_T]
  linarith

/-- Slashing by `upperTriRep (n + 1) b` followed by `T` permutes the representative by
`finRotate (n + 1)` when `f` is `T`-invariant. -/
private lemma slash_upperTriRep_mul_T (n : ℕ) (f : ℍ → ℂ)
    (hfT : f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) = f) (b : Fin (n + 1)) :
    (f ∣[k] (upperTriRep (n + 1) b : GL (Fin 2) ℚ)) ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) =
      f ∣[k] (upperTriRep (n + 1) (finRotate (n + 1) b) : GL (Fin 2) ℚ) := by
  rw [← SlashAction.slash_mul]
  by_cases hb : b.val < n
  · rw [finRotate_of_lt hb, upperTriRep_mul_mapGL_T_of_lt (n + 1) b (Nat.succ_lt_succ hb)]
  · have hbn : b = ⟨n, Nat.lt_succ_self n⟩ := by ext; dsimp; omega
    rw [hbn, finRotate_last']
    have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).val + 1 = n + 1 := rfl
    rw [upperTriRep_last_mul_mapGL_T (n + 1) _ hlast,
      SlashAction.slash_mul, hfT]

/-- **The upper-triangular Hecke slash sum preserves `T`-invariance.** -/
theorem heckeSlashUpperTri_slash_T (f : ℍ → ℂ)
    (hfT : f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) =
      heckeSlashUpperTri k p f := by
  rcases p with _ | n
  · rw [heckeSlashUpperTri_def]
    simp [SlashAction.zero_slash]
  · rw [heckeSlashUpperTri_def, SlashAction.sum_slash]
    have hsum : (∑ b : Fin (n + 1),
        (f ∣[k] (upperTriRep (n + 1) b : GL (Fin 2) ℚ)) ∣[k]
          (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ)) =
        ∑ b : Fin (n + 1),
          f ∣[k] (upperTriRep (n + 1) (finRotate (n + 1) b) : GL (Fin 2) ℚ) := by
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      exact slash_upperTriRep_mul_T k (n := n) f hfT b
    rw [hsum]
    exact Equiv.sum_comp (finRotate (n + 1)) (fun b ↦ f ∣[k] (upperTriRep (n + 1) b : GL (Fin 2) ℚ))

/-- **Pointwise 1-periodicity**: `heckeSlashUpperTri` preserves translation invariance
`f((1 : ℝ) +ᵥ τ) = f(τ)`. -/
lemma heckeSlashUpperTri_shift_one (f : ℍ → ℂ) (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (τ : ℍ) :
    heckeSlashUpperTri k p f ((1 : ℝ) +ᵥ τ) = heckeSlashUpperTri k p f τ := by
  have hfT : f ∣[k] (mapGL ℚ (ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℚ) = f := by
    ext x
    rw [ModularForm.rat_slash, map_mapGL, ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      ← _root_.ModularForm.SL_slash]
    have ht := TauCeti.ModularForm.slash_T_zpow_apply k 1 f x
    rw [zpow_one, Int.cast_one] at ht
    exact ht.trans (hf x)
  have hTinv := heckeSlashUpperTri_slash_T k p f hfT
  have hT_eval : (heckeSlashUpperTri k p f ∣[k]
      (mapGL ℚ (ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℚ)) τ =
        heckeSlashUpperTri k p f ((1 : ℝ) +ᵥ τ) := by
    rw [ModularForm.rat_slash, map_mapGL, ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      ← _root_.ModularForm.SL_slash]
    have ht := TauCeti.ModularForm.slash_T_zpow_apply k 1 (heckeSlashUpperTri k p f) τ
    rw [zpow_one, Int.cast_one] at ht
    exact ht
  rw [← hT_eval, hTinv]

end HeckeRing.GL2

end
