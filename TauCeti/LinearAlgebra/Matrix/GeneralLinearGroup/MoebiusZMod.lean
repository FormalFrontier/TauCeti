/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Data.ZMod.FinEquiv
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The Möbius permutation of `Fin p` attached to an integer matrix

An integer matrix `M` whose determinant is a unit mod `p` permutes `Fin p` by the Möbius rule

`b ↦ (M 0 1 + b * M 1 1) / (M 0 0 + b * M 1 0)  (mod p)`   **where the denominator is nonzero**,

and by `b ↦ M 1 1 / M 1 0` at the **at most one** index where it vanishes. Such an index exists
exactly when `M 1 0 ≢ 0 (mod p)`, and is then `-M 0 0 / M 1 0`; when `M 1 0 ≡ 0` the determinant
forces `M 0 0 ≢ 0`, the denominator never vanishes, and there is no pole at all (take `M = 1`).

The second clause is *not* the first evaluated at a zero denominator: division by zero in `ZMod p`
is `0`, whereas the pole is genuinely carried to the image of `∞` by the projective action.

This is Mathlib's Möbius action of `GL (Fin 2) (ZMod p)` on `OnePoint (ZMod p)` restricted to the
affine part: `Equiv.removeNone` deletes the point at infinity from the induced permutation,
patching the pole to the image of `∞`. Transporting along `ZMod.finEquiv` gives a permutation of
`Fin p`.

The `GL` element and its action are set up over an **arbitrary field**; only the passage to
`Fin p` needs `ZMod p`, where the determinant hypothesis transfers along Mathlib's
`Int.cast_det`.

Nothing here is specific to any one application. The motivating consumer is the `Γ₁(N)`-invariance
of the Hecke operator, where `Fin p` indexes the upper-triangular representatives `!![1, b; 0, p]`.
This permutation is the *index* bookkeeping in that argument; it is **not** by itself the claim
that slashing the representative sum by `M` permutes the summands, which is false in general —
when `M 1 0 ≢ 0 (mod p)` one representative leaves the upper-triangular family altogether, and the
argument there needs the pole case, not a permutation. The statements below mention no Hecke
notion.

## Main definitions

* `TauCeti.moebiusGL`: the `GL (Fin 2) K` element, over any field, whose action gives the rule
  above.
* `TauCeti.moebiusFin`: the reindexing, as an `Equiv.Perm (Fin p)`.

## Main results

* `TauCeti.moebiusGL_smul_some` and `TauCeti.moebiusGL_smul_infty`: the two values of the action,
  in the entries of `M`. The second is what `Equiv.removeNone` splices in at the pole.
The pole criterion itself is `OnePoint.smul_some_eq_infty_iff`, which this file adds to Mathlib's
action API in `TauCeti/Topology/Compactification/OnePoint/ProjectiveLine.lean`; the two value
lemmas come straight from Mathlib's `smul_some_eq_ite` / `smul_infty_eq_ite`.
* `TauCeti.natCast_moebiusFin_of_ne_zero` and `TauCeti.natCast_moebiusFin_of_eq_zero`: the two
  evaluation branches, read in `ZMod p` through the natural cast of the index — the affine
  quotient where the denominator does not vanish, and the image of `∞` at the single index where
  it does.

Uniqueness of the pole is not stated here. That exactly one residue solves `c * i + a = 0` in
`ZMod n` for a unit `c` mentions no matrix, so it belongs with the generic `ZMod` arithmetic
rather than in this file; a Möbius consumer instantiates it at `a := M 0 0` and `c := M 1 0`,
and wrapping that instantiation in a matrix-level restatement would add no content.
The two evaluation lemmas above are the elimination API for `moebiusFin`: its body is sealed
across the module boundary, so `unfold` is not available to a consumer, and the equation they are
proved from is private scaffold rather than public surface.

Injectivity is not stated separately: `moebiusFin` is an `Equiv`, so consumers use
`Equiv.injective`.

## Provenance

The statement being realised is AINTLIB's `moebiusFin` / `moebiusFin_injective`
([`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB), commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, lines 124-242, Apache-2.0, Chris Birkbeck).

The two pole lemmas AINTLIB also states are not here: being arithmetic in `ZMod p` with no matrix
or determinant in sight, they belong with the generic `ZMod` arithmetic and are not part of this
refactor.

`ZMod.finEquiv_apply` and `ZMod.finEquiv_symm_apply_val` (in `TauCeti/Data/ZMod/FinEquiv.lean`)
have no AINTLIB counterpart either: the source writes its reindexing directly in `ZMod p` and so
never needs the `Fin`/`ZMod` bridge in either direction.

**No code is transcribed.** The source builds the map by hand as an `if`-split on whether the
denominator vanishes, and proves injectivity by a four-way case analysis resting on five
supporting lemmas. All of that is already Mathlib's: the map is `Equiv.removeNone` applied to
`instGLAction` (`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`), and injectivity
is `Equiv.injective`. The entries are permuted along the anti-diagonal because Mathlib's affine
rule is `k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` (`smul_some_eq_ite`) while the source reads
`M` in the other order.
-/

public section

namespace TauCeti

open Matrix OnePoint

section Field

variable {K : Type*} [Field K]

/-- **The matrix whose Möbius action is the reindexing.** The entries of `M` are reflected along
the anti-diagonal, so that Mathlib's affine rule
`k ↦ (g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)` reads as
`k ↦ (M 0 1 + k * M 1 1) / (M 0 0 + k * M 1 0)` — on `OnePoint K`, where a vanishing denominator
sends `k` to `∞` rather than to a quotient by zero.

The reflection leaves the determinant alone, so the only hypothesis is invertibility. -/
noncomputable def moebiusGL (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![M 1 1, M 0 1; M 1 0, M 0 0]
    (by
      rw [Matrix.det_fin_two_of]
      rw [Matrix.det_fin_two] at h
      intro hz
      exact h (by linear_combination hz))

@[simp]
lemma moebiusGL_coe (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) :
    (moebiusGL M h : Matrix (Fin 2) (Fin 2) K) = !![M 1 1, M 0 1; M 1 0, M 0 0] := (rfl)

section Action

-- `[DecidableEq K]` is a hypothesis of the *statements* below, not of their proofs: Mathlib's
-- `instGLAction` — the action they are about — is itself declared under
-- `[Field K] [DecidableEq K]` (`Topology/Compactification/OnePoint/ProjectiveLine.lean:124`), so
-- `g • (k : OnePoint K)` does not elaborate without it. `moebiusGL` above needs no such
-- assumption, and is stated without one.
variable [DecidableEq K]

/-- **The value at an affine point**, in the entries of `M`. Together with `moebiusGL_smul_infty`
this is the whole action: `Equiv.removeNone` chooses between the two according to whether this
`ite` takes its first branch, which is what `OnePoint.smul_some_eq_infty_iff` decides.

Not `@[simp]`, matching Mathlib's deliberate choice for `smul_some_eq_ite` / `smul_infty_eq_ite`:
rewriting to an `ite` pre-empts the pole criterion rather than helping it. -/
lemma moebiusGL_smul_some (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) (k : K) :
    moebiusGL M h • (k : OnePoint K) =
      if M 1 0 * k + M 0 0 = 0 then ∞
      else ((M 1 1 * k + M 0 1) / (M 1 0 * k + M 0 0) : K) := by
  rw [smul_some_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

/-- **The value at the point at infinity**, in the entries of `M`. This is the value
`Equiv.removeNone` splices in at the pole, so it is the ingredient `moebiusGL_smul_some` and the
pole criterion do not supply. -/
lemma moebiusGL_smul_infty (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) :
    moebiusGL M h • (∞ : OnePoint K) =
      if M 1 0 = 0 then ∞ else ((M 1 1 / M 1 0 : K)) := by
  rw [smul_infty_eq_ite, moebiusGL_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero]

end Action

end Field

variable {p : ℕ} [Fact p.Prime]

/-- The mapped matrix is invertible when the cast determinant is nonzero. This is `Int.cast_det`
read in the direction the `moebiusGL` argument needs; it is stated once because seven call sites
below need it. -/
private lemma det_map_ne_zero (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    (M.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  rwa [Int.cast_det] at h

/-- **The Möbius reindexing of `Fin p`.** Mathlib's action of `moebiusGL` on `OnePoint (ZMod p)`
is a permutation; `Equiv.removeNone` deletes `∞` from it, patching the pole to the image of `∞`,
and `Equiv.permCongr` along `ZMod.finEquiv` transports the result to `Fin p`. -/
noncomputable def moebiusFin (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ((M.det : ℤ) : ZMod p) ≠ 0) :
    Equiv.Perm (Fin p) :=
  (ZMod.finEquiv p).toEquiv.symm.permCongr
    (Equiv.removeNone (MulAction.toPerm
      (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)) :
        Equiv.Perm (OnePoint (ZMod p))))

/-- **The reindexing at an index**, cast into `ZMod p` and with the conjugation cancelled.
`moebiusFin` is `Equiv.removeNone` of Mathlib's action, conjugated along `ZMod.finEquiv`; stating
it after the cast strips the conjugation and leaves exactly the shape the value lemmas above apply
to (`moebiusGL_smul_some` off the pole, `moebiusGL_smul_infty` at it, with
`OnePoint.smul_some_eq_infty_iff` deciding which).

The cast is part of the statement rather than something a caller reintroduces, so both evaluation
lemmas rewrite with it directly. -/
private lemma natCast_moebiusFin (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) (b : Fin p) :
    ((moebiusFin M h b : ℕ) : ZMod p) =
      Equiv.removeNone (MulAction.toPerm
        (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)) :
          Equiv.Perm (OnePoint (ZMod p))) (((b : ℕ) : ZMod p)) := by
  -- Both sides go into `ZMod.finEquiv` form before `simp`. An explicit `simp only` chain would
  -- be preferable, but after `Equiv.permCongr_apply` the goal carries `(ZMod.finEquiv p).symm.symm`
  -- — `moebiusFin` is built from `(ZMod.finEquiv p).toEquiv.symm`, so that double symm is on the
  -- `Equiv`, not the `RingEquiv` — and neither `Equiv.symm_symm` nor `RingEquiv.symm_symm`
  -- discharges it inside `simp only`. Until a lemma set closes it, this route stays.
  rw [← ZMod.finEquiv_apply, ← ZMod.finEquiv_apply]
  simp [moebiusFin, Equiv.permCongr_apply]
/-- **The reindexing off the pole.** Where the denominator does not vanish, the index goes to the
affine Möbius value, read in `ZMod p` through the natural cast of its index. -/
@[simp]
lemma natCast_moebiusFin_of_ne_zero (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) (b : Fin p)
    (hb : ((M 1 0 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 0 : ℤ) : ZMod p) ≠ 0) :
    ((moebiusFin M h b : ℕ) : ZMod p) =
      (((M 1 1 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 1 : ℤ) : ZMod p)) /
        (((M 1 0 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 0 : ℤ) : ZMod p)) := by
  have hval : (MulAction.toPerm
      (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)) :
        Equiv.Perm (OnePoint (ZMod p))) ((((b : ℕ) : ZMod p) : ZMod p) : OnePoint (ZMod p)) =
      ((((M 1 1 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 1 : ℤ) : ZMod p)) /
        (((M 1 0 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 0 : ℤ) : ZMod p)) :
          ZMod p) := by
    simpa [Matrix.map_apply, hb] using
      moebiusGL_smul_some (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)
        ((b : ℕ) : ZMod p)
  have := Equiv.removeNone_some _ ⟨_, hval⟩
  rw [natCast_moebiusFin]
  exact Option.some_inj.mp (this.trans hval)

/-- **The reindexing at the pole.** At the single index where the denominator vanishes, the value
is the image of `∞`. The denominator's leading entry cannot also vanish there: if it did the
determinant would vanish mod `p`, so the quotient below is not a division by zero. -/
@[simp]
lemma natCast_moebiusFin_of_eq_zero (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ((M.det : ℤ) : ZMod p) ≠ 0) (b : Fin p)
    (hb : ((M 1 0 : ℤ) : ZMod p) * ((b : ℕ) : ZMod p) + ((M 0 0 : ℤ) : ZMod p) = 0) :
    ((moebiusFin M h b : ℕ) : ZMod p) =
      ((M 1 1 : ℤ) : ZMod p) / ((M 1 0 : ℤ) : ZMod p) := by
  have h10 : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_mul, zero_add] at hb
    rw [Matrix.det_fin_two] at h
    push_cast at h
    exact h (by rw [hb, hz]; ring)
  have hinf : (MulAction.toPerm
      (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)) :
        Equiv.Perm (OnePoint (ZMod p))) ((((b : ℕ) : ZMod p) : ZMod p) : OnePoint (ZMod p)) =
      (∞ : OnePoint (ZMod p)) := by
    simp [Matrix.map_apply, hb]
  have hnone := Equiv.removeNone_none _ hinf
  have hval : (MulAction.toPerm
      (moebiusGL (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)) :
        Equiv.Perm (OnePoint (ZMod p))) (∞ : OnePoint (ZMod p)) =
      ((((M 1 1 : ℤ) : ZMod p) / ((M 1 0 : ℤ) : ZMod p) : ZMod p) : OnePoint (ZMod p)) := by
    simpa [Matrix.map_apply, h10] using
      moebiusGL_smul_infty (M.map (Int.cast : ℤ → ZMod p)) (det_map_ne_zero M h)
  rw [natCast_moebiusFin]
  exact Option.some_inj.mp (hnone.trans hval)

end TauCeti
