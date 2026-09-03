/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Data.ZMod.FinEquiv
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum

/-!
# The upper-triangular Hecke slash sum under `T`-invariance

The classical upper-triangular Hecke sum `heckeSlashUpperTri k p f = ∑ b < p, f ∣[k] !![1, b; 0, p]`
preserves invariance under the translation matrix `T = !![1, 1; 0, 1]`.

Right multiplication of the representative `!![1, b; 0, p]` by `T` produces `!![1, b + 1; 0, p]`.
For `b < p - 1`, this is the `(b + 1)`-st representative; for `b = p - 1`, it factors as
`T · !![1, 0; 0, p]`. When `f` is `T`-slash invariant (`f ∣[k] T = f`), the `T` factor on the
boundary term is absorbed, so slashing the whole sum by `T` cyclically permutes the summands via
`finRotate p` and recovers `heckeSlashUpperTri k p f`.

Pointwise on `ℍ`, `f ∣[k] T = f` is the 1-periodicity `f(τ + 1) = f(τ)`, so the upper-triangular
sum sends 1-periodic functions to 1-periodic functions.

The same absorption proves a second statement about a `T`-invariant `f`: the sum commutes with the
slash by `scaleRep d = diag(d, 1)` for `d` coprime to `p`. The two slashes do **not** commute
termwise — `diag(d, 1) · !![1, b; 0, p]` is `!![1, d b; 0, p] · diag(d, 1)`, whose upper entry
`d b` leaves the range `b < p` — but writing `d b = q p + r` puts the excess into a shift `T ^ q`,
which the invariance absorbs, and coprimality makes `b ↦ r` a permutation of `Fin p`, so the sum is
merely reindexed. This is the level-raising half of `Tₚ ∘ V_d = V_d ∘ Tₚ`
(`HeckeSlash/Degeneracy.lean`).

## Main results

* `HeckeRing.GL2.upperTriRep_mul_mapGL_T_of_lt`: for `b.val + 1 < p`,
  `upperTriRep p b * mapGL ℚ ModularGroup.T = upperTriRep p ⟨b.val + 1, _⟩`.
* `HeckeRing.GL2.upperTriRep_last_mul_mapGL_T`: for `b.val + 1 = p`,
  `upperTriRep p b * mapGL ℚ ModularGroup.T = mapGL ℚ ModularGroup.T * upperTriRep p ⟨0, _⟩`.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_T`: if `f ∣[k] mapGL ℚ ModularGroup.T = f`, then
  `heckeSlashUpperTri k p f ∣[k] mapGL ℚ ModularGroup.T = heckeSlashUpperTri k p f`.
* `HeckeRing.GL2.heckeSlashUpperTri_shift_one`: if `f((1 : ℝ) +ᵥ τ) = f(τ)` for all `τ`, then
  `heckeSlashUpperTri k p f ((1 : ℝ) +ᵥ τ) = heckeSlashUpperTri k p f τ`.
* `HeckeRing.GL2.heckeSlashUpperTri_slash_scaleRep_comm`: if `f ∣[k] mapGL ℚ ModularGroup.T = f`
  and `d` is coprime to `p`, then `heckeSlashUpperTri k p (f ∣[k] scaleRep d)` equals
  `heckeSlashUpperTri k p f ∣[k] scaleRep d`.

## Provenance

`heckeSlashUpperTri_slash_scaleRep_comm` and its helpers adapt the reindexing step of the
level-raising comparison in the AINTLIB
[`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project, file
`LeanModularForms/HeckeRIngs/GL2/Newforms/LevelRaiseComm.lean`, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck, lines 66–190
(`T_p_upper_mod`, `levelRaise_mul_T_p_upper` and `sum_reindex_mul_mod`, feeding
`heckeT_p_ut_levelRaise`). No proof code is transcribed: that development sums over
`Finset.range p` by `Finset.sum_nbij` and assumes `p` prime, whereas the statement here indexes by
`Fin p` through an explicit `Equiv`, assumes only `0 < p` with `Nat.Coprime d p`, and is about a
bare function rather than a cusp form. Its consumer, and the provenance note for the level-raising
theorem itself, is `HeckeSlash/Degeneracy.lean`.

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

/-! ### The sum against `diag(d, 1)` -/

section Scale

variable {d : ℕ}

/-- **The commutation of `scaleRep d = diag(d, 1)` past an upper-triangular representative.**
Both sides are `!![d, d b; 0, p]`: on the right, `d b = q p + r` is split so that the
representative index `r` is again in range, at the cost of the shift `T ^ q`. -/
private lemma scaleRep_mul_upperTriRep (hd : 0 < d) (b : Fin p) {q r : ℕ} (hr : r < p)
    (hqr : d * (b : ℕ) = q * p + r) :
    scaleRep d * upperTriRep p b =
      mapGL ℚ (ModularGroup.T ^ q) * (upperTriRep p ⟨r, hr⟩ * scaleRep d) := by
  have hmod : (d : ℚ) * ((b : ℕ) : ℚ) = (q : ℚ) * (p : ℚ) + (r : ℚ) := by exact_mod_cast hqr
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scaleRep d hd, coe_upperTriRep,
    coe_upperTriRep]
  ext i j
  -- three of the four entries close by `simp`; the bullet makes the surviving one explicit, so a
  -- change in the simp set fails here rather than silently redirecting `linarith`.
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linarith

/-- Multiplication by `d` modulo `p` permutes `Fin p` when `d` and `p` are coprime. It *is*
multiplication by the unit `ZMod.unitOfCoprime d hdp` of `ZMod p`, read through
`ZMod.finEquiv`, so the permutation property is the unit's and nothing is proved here. -/
private noncomputable def mulModEquiv (hp : 0 < p) (hdp : Nat.Coprime d p) : Fin p ≃ Fin p :=
  haveI : NeZero p := ⟨hp.ne'⟩
  (ZMod.finEquiv p).toEquiv.trans <|
    (Units.mulLeft (ZMod.unitOfCoprime d hdp)).trans (ZMod.finEquiv p).toEquiv.symm

/-- The index the permutation sends `b` to, as a natural number. This is what
`ZMod.finEquiv_symm_apply_val` is for: the `Fin p` representative of a residue has that
residue's `val`. -/
@[simp]
private lemma coe_mulModEquiv (hp : 0 < p) (hdp : Nat.Coprime d p) (b : Fin p) :
    (mulModEquiv p hp hdp b : ℕ) = d * (b : ℕ) % p := by
  have : NeZero p := ⟨hp.ne'⟩
  simp [mulModEquiv, ZMod.coe_unitOfCoprime, ← Nat.cast_mul, ZMod.val_natCast]

/-- **The upper-triangular slash sum commutes with the slash by `scaleRep d = diag(d, 1)`**, for
`d` coprime to `p` and any `T`-invariant function. This is the level-raising half of
`heckeTCuspNat_levelRaise`, stated before the normalising scalar of `V_d` is introduced.

Invariance under `T` alone is all the reindexing consumes: the shift it produces is `T ^ q` for
the quotient `q` of `d b` by `p`, and those powers are derived from `hT` inside the proof, so no
level and no explicit power enters the statement. A form invariant under a congruence subgroup
containing `T` — every `Γ₁(M)` — meets the hypothesis; `HeckeSlash/Degeneracy.lean` is the
consumer. -/
@[grind =]
theorem heckeSlashUpperTri_slash_scaleRep_comm (hd : 0 < d) (hp : 0 < p)
    (hdp : Nat.Coprime d p) {f : ℍ → ℂ}
    (hT : f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) = f) :
    heckeSlashUpperTri k p (f ∣[k] (scaleRep d : GL (Fin 2) ℚ)) =
      heckeSlashUpperTri k p f ∣[k] (scaleRep d : GL (Fin 2) ℚ) := by
  have hTpow (q : ℕ) : f ∣[k] (mapGL ℚ (ModularGroup.T ^ q) : GL (Fin 2) ℚ) = f := by
    rw [ModularForm.rat_slash_mapGL, map_pow, ← zpow_natCast]
    exact slash_zpow_eq_self_of_slash_eq k f (by rwa [ModularForm.rat_slash_mapGL] at hT) q
  rw [heckeSlashUpperTri_def, heckeSlashUpperTri_def, SlashAction.sum_slash]
  rw [← Equiv.sum_comp (mulModEquiv p hp hdp) fun b ↦ (f ∣[k] upperTriRep p b) ∣[k]
    (scaleRep d : GL (Fin 2) ℚ)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  -- the reindexed representative is `d b mod p`, by the defining lemma of `mulModEquiv`
  have hb : mulModEquiv p hp hdp b = ⟨d * (b : ℕ) % p, Nat.mod_lt _ hp⟩ :=
    Fin.ext (coe_mulModEquiv p hp hdp b)
  rw [← SlashAction.slash_mul,
    scaleRep_mul_upperTriRep p hd b (Nat.mod_lt _ hp) (Nat.div_add_mod' (d * (b : ℕ)) p).symm,
    SlashAction.slash_mul, hTpow, SlashAction.slash_mul, hb]

end Scale

end HeckeRing.GL2

end
