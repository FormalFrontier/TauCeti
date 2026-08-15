/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CosetDecomposition

/-!
# The upper-triangular entry assignments at `n = 2`

`GLn/CosetDecomposition.lean` indexes the upper-triangular coset representatives by the bounded
entry assignments `UpperTriEntries n a`, a dependent function on the ordered index pairs
`{ij : Fin n × Fin n // ij.1 < ij.2}`. At `n = 2` there is exactly one such pair, `(0, 1)`, so an
assignment carries a single coordinate and `UpperTriEntries 2 a` is just `Fin (a 1 / a 0)`.

This file records that identification, and its specialisation to `a = ![1, p]`, where the
coordinate is an offset `b ∈ Fin p` and `upperTriGL` runs over the classical `!![1, b; 0, p]`.
It is the adapter between the general-`n` decomposition and the classical `T_p` bookkeeping,
which sums over `b` directly: a sum over `UpperTriEntries 2 ![1, p]` transfers along this
equivalence rather than being restated.

Nothing here involves a level or a congruence subgroup; the level-`N` membership statements for
these representatives are in `GL2/UpperTriangularDelta0.lean`.

## Main definitions

* `HeckeRing.GL2.uniqueIndexPair`: `(0, 1)` is the only ordered index pair at `n = 2`.
* `HeckeRing.GL2.upperTriEntriesEquiv`: `UpperTriEntries 2 a ≃ Fin (a 1 / a 0)`, for an
  arbitrary tuple `a`.
* `HeckeRing.GL2.upperTriEntriesEquivFin`: its specialisation `UpperTriEntries 2 ![1, p] ≃ Fin p`.

## Main results

* `HeckeRing.GL2.upperTriEntriesEquiv_apply`, `upperTriEntriesEquiv_symm_apply_default`: the
  equivalence reads off, and installs, the coordinate at the unique index pair.
* `HeckeRing.GL2.upperTriEntriesEquivFin_apply_val` and
  `upperTriEntriesEquivFin_symm_apply_default_val`: the same for
  `a = ![1, p]`, as an identity of natural numbers — the two fibres `Fin (![1, p] 1 / ![1, p] 0)`
  is `Fin (p / 1)`, which `finCongr` carries to `Fin p` along `p / 1 = p`.

* `HeckeRing.GL2.upperTriRep_coe_matrix`: the entrywise description of the representative:
  `!![1, b; 0, p]`.
* `HeckeRing.GL2.upperTriRep_apply_one_zero`: the representatives are upper triangular — the
  hypothesis mathlib's `IsBoundedAtImInfty.slash` asks for.
* `HeckeRing.GL2.det_upperTriRep_pos`: they have determinant `p > 0`, which is what lets scalars
  pass through a slash by them without the `σ` twist.

## Provenance

No code is ported: the equivalence is a fact about this repository's own `UpperTriEntries`. The
"classical `T_p` bookkeeping" it adapts to is that of the AINTLIB `LeanModularForms` project
(Chris Birkbeck, Apache-2.0), `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, whose `heckeT_p_ut` sums over `b ∈ Finset.range p`
and whose `T_p_upper p _ b = !![1, b; 0, p]` is `upperTriGL` at `n = 2`, `a = ![1, p]`. This file
exists so that such a sum transfers onto the existing general-`n` decomposition instead of
restating the index.
-/

public section

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (p : ℕ)

/-- At `n = 2` there is exactly one ordered index pair, `(0, 1)`, so `UpperTriEntries` is a
function on a one-element type. -/
instance uniqueIndexPair : Unique {ij : Fin 2 × Fin 2 // ij.1 < ij.2} where
  default := ⟨(0, 1), by decide⟩
  uniq := by rintro ⟨ij, h⟩; apply Subtype.ext; revert h; revert ij; decide

@[simp]
lemma default_indexPair_val : (default : {ij : Fin 2 × Fin 2 // ij.1 < ij.2}).val = (0, 1) := rfl

/-- **An entry assignment at `n = 2` is a single coordinate.** `UpperTriEntries 2 a` is a
dependent function on the ordered index pairs, and by `uniqueIndexPair` there is only the pair
`(0, 1)`; the fibre over it is `Fin (a 1 / a 0)`.

The fibre over `default` reduces to the fibre over `(0, 1)`, namely `Fin (a 1 / a 0)`, because
`default` is the field of `uniqueIndexPair`. The specialisation to `a = ![1, p]` is a separate
matter: it leaves the bound `p / 1`, and `finCongr (by simp)` transports along the
*propositional* equality `p / 1 = p`. -/
def upperTriEntriesEquiv (a : Fin 2 → ℕ) : UpperTriEntries 2 a ≃ Fin (a 1 / a 0) :=
  Equiv.piUnique _

/-- The equivalence reads off the coordinate at the unique index pair. -/
@[simp]
lemma upperTriEntriesEquiv_apply {a : Fin 2 → ℕ} (B : UpperTriEntries 2 a) :
    upperTriEntriesEquiv a B = B default := (rfl)

/-- Its inverse installs a given coordinate at the unique index pair. -/
@[simp]
lemma upperTriEntriesEquiv_symm_apply_default {a : Fin 2 → ℕ} (b : Fin (a 1 / a 0)) :
    (upperTriEntriesEquiv a).symm b default = b := (rfl)

/-- **The classical index of the upper-triangular representatives.** For `a = ![1, p]` the entry
assignments are just the offsets `b ∈ Fin p`, so `upperTriGL` at these entries runs over the
familiar `!![1, b; 0, p]`. -/
def upperTriEntriesEquivFin (p : ℕ) : UpperTriEntries 2 ![1, p] ≃ Fin p :=
  (upperTriEntriesEquiv _).trans (finCongr (by simp))

/-- At `a = ![1, p]` the offset read off is the coordinate, as natural numbers: the fibres
`Fin (![1, p] 1 / ![1, p] 0)` is `Fin (p / 1)`, carried to `Fin p` by `finCongr`. -/
@[simp]
lemma upperTriEntriesEquivFin_apply_val {p : ℕ} (B : UpperTriEntries 2 ![1, p]) :
    (upperTriEntriesEquivFin p B : ℕ) = (B default : ℕ) := (rfl)

/-- At `a = ![1, p]` the coordinate installed is the offset, as natural numbers. -/
@[simp]
lemma upperTriEntriesEquivFin_symm_apply_default_val {p : ℕ} (b : Fin p) :
    (((upperTriEntriesEquivFin p).symm b default : ℕ)) = (b : ℕ) := (rfl)

/-- The `b`-th upper-triangular representative `!![1, b; 0, p]`, as an element of this
repository's general-`n` family at `a = ![1, p]`. -/
noncomputable def upperTriRep (b : Fin p) : GL (Fin 2) ℚ :=
  upperTriGL ((upperTriEntriesEquivFin p).symm b)

lemma upperTriRep_def (b : Fin p) :
    upperTriRep p b = upperTriGL ((upperTriEntriesEquivFin p).symm b) := (rfl)

/-- The matrix of `upperTriRep p b` is `!![1, b; 0, p]`. -/
lemma upperTriRep_coe_matrix (hp : 0 < p) (b : Fin p) :
    (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![1, (b : ℚ); 0, (p : ℚ)] := by
  have ha : ∀ i : Fin 2, 0 < ![1, p] i := fun i ↦ by fin_cases i <;> simp [hp]
  set B := (upperTriEntriesEquivFin p).symm b
  ext ⟨_ | _ | _, _⟩ ⟨_ | _ | _, _⟩ <;> try contradiction
  · change (upperTriGL B : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = 1
    rw [upperTriGL_apply_diag ha B 0]
    rfl
  · change (upperTriGL B : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = (b : ℚ)
    rw [upperTriGL_apply_lt ha B (by decide)]
    have hdef : (⟨(0, 1), by decide⟩ : {ij : Fin 2 × Fin 2 // ij.1 < ij.2}) = default :=
      Subtype.ext rfl
    have hb := upperTriEntriesEquivFin_symm_apply_default_val b
    rw [hdef]
    change ((1 : ℕ) : ℚ) * ((B default : ℕ) : ℚ) = (b : ℚ)
    rw [hb]
    simp
  · change (upperTriGL B : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
    rw [upperTriGL_apply_eq_zero_of_lt ha B (by decide)]
  · change (upperTriGL B : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (p : ℚ)
    rw [upperTriGL_apply_diag ha B 1]
    rfl

/-- **The representatives are upper triangular** — the hypothesis mathlib's
`IsBoundedAtImInfty.slash` asks for. At `n = 2` this is the `(1, 0)` entry of
`upperTriGL_apply_eq_zero_of_lt`. -/
@[simp] lemma upperTriRep_apply_one_zero (b : Fin p) :
    (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 :=
  upperTriGL_apply_eq_zero_of_lt (fun i ↦ by fin_cases i <;> simp [b.pos]) _ (by decide)

/-- The representatives have positive determinant: `det !![1, b; 0, p] = p > 0`. -/
lemma det_upperTriRep_pos (b : Fin p) :
    0 < (↑(upperTriRep p b) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  have hpos : ∀ i : Fin 2, 0 < ![1, p] i := fun i ↦ by fin_cases i <;> simp [b.pos]
  have hdiag : (0 : ℚ) < (↑(natDiagGL 2 ![1, p]) : Matrix (Fin 2) (Fin 2) ℚ).det :=
    natDiagGL_det_pos 2 ![1, p] hpos
  have hunit := RingHom.map_det (Int.castRingHom ℚ)
    (unitriMat ((upperTriEntriesEquivFin p).symm b))
  rw [det_unitriMat] at hunit
  have hunit' : ((unitriMat ((upperTriEntriesEquivFin p).symm b)).map
      (Int.cast : ℤ → ℚ)).det = 1 := by simpa using hunit.symm
  rw [upperTriRep, upperTriGL_def, Units.val_mul, Matrix.det_mul]
  simpa [hunit'] using hdiag

end HeckeRing.GL2

end
