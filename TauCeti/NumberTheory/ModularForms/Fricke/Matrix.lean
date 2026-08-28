/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The Fricke matrix

The Fricke matrix `W = !![0, -1; N, 0]`, as an element of `GL (Fin 2) K` for a field `K` in
which `N` is invertible. Its determinant is `N`, which is nonzero exactly under the standing
`[NeZero (N : K)]` hypothesis, so `W` is a unit.

The base field is a parameter rather than `ℚ`: the two consumers sit over different fields.
The weight-`k` slash is an action of `GL (Fin 2) ℝ`, while the `GL (Fin 2) ℚ` Hecke-ring stack
of `TauCeti/NumberTheory/HeckeRing/GL2/Delta0.lean` wants the rational form; both are
`frickeGL _ N`, with no transport lemmas between them. Over `ℚ` and `ℝ` a caller holding
`[NeZero N]` on the natural number gets the standing `[NeZero (N : K)]` by instance search,
through `NeZero.charZero`; the instance runs only in that direction.

This file is only the matrix. `TauCeti/NumberTheory/ModularForms/Fricke/Operator.lean` builds
the Fricke *slash operator* on `M_k(Γ₁(N))` on top of it: the raw `f ↦ f ∣[k] W`, carrying no
normalizing scalar and so not an involution. The normalized `𝒲_N = (√N) ^ (2 - k) • (· ∣[k] W)`,
which rescales that map and is an involution in even weight, is a later rung.

## Main definitions

* `TauCeti.frickeGL`: the Fricke matrix as an element of `GL (Fin 2) K`.

## Main results

* `TauCeti.coe_frickeGL`: the underlying matrix is `!![0, -1; N, 0]`.
* `TauCeti.val_det_frickeGL`: the determinant is `N`.
* `TauCeti.val_det_frickeGL_pos`: over an ordered ring, that determinant is positive. This is
  about the single matrix `W`, deliberately not a general statement about `SL`-type elements.
* `TauCeti.coe_inv_frickeGL`: `W⁻¹ = !![0, N⁻¹; -1, 0]`.
* `TauCeti.coe_frickeGL_sq`: `W² = (-N) • 1` as matrices.

## Relation to the Atkin–Lehner anti-involution

Both this matrix and the conjugating matrix of
`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` are called "Atkin–Lehner" in the
literature, and they are **different matrices**. That file conjugates by `natDiagGL 2 ![1, N]`,
the diagonal rescaling repairing the transpose's failure to preserve `Γ₀(N)`; its docstring
already records that it is *not* `!![0, -1; N, 0]`. This file is the latter.

At `N = 1` the Fricke matrix coincides numerically with the level-one `S = !![0, -1; 1, 0]` of
`TauCeti/NumberTheory/ModularForms/STransform.lean` and with `TauCeti.SU2.weylMatrix`. Those are
different objects in different settings — neither carries a determinant-`N` normalization — so
`frickeGL` is not a restatement of either.

Ported from the AINTLIB `LeanModularForms` project
(`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Fricke.lean`, Chris Birkbeck,
Apache-2.0, <https://github.com/CBirkbeck/AINTLIB>), realizing part of Layer 6 of the
ModularForms roadmap.
-/

open Matrix

namespace TauCeti

variable {K : Type*} [Field K] {N : ℕ} [NeZero (N : K)]

/-- The Fricke matrix `W = !![0, -1; N, 0]` as an element of `GL (Fin 2) K`, of determinant
`N`. -/
public noncomputable def frickeGL (K : Type*) [Field K] (N : ℕ) [NeZero (N : K)] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : K), 0]
    (by rw [det_fin_two_of]; simpa using NeZero.ne (N : K))

/-- The underlying matrix of `frickeGL K N`. -/
@[simp]
public theorem coe_frickeGL :
    (↑(frickeGL K N) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; (N : K), 0] := by
  simp [frickeGL]

/-- The determinant of `frickeGL K N` is `N`. -/
public theorem val_det_frickeGL : ((frickeGL K N).det : K) = N := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_frickeGL, det_fin_two_of]
  ring

/-- Over an ordered ring the determinant of `frickeGL K N` is positive. This is about the
single matrix `W`; it is deliberately not a general statement about determinants of `SL`-type
elements. -/
public theorem val_det_frickeGL_pos [PartialOrder K] [IsOrderedRing K] :
    0 < ((frickeGL K N).det : K) := by
  rw [val_det_frickeGL]
  exact (Nat.cast_nonneg N).lt_of_ne' (NeZero.ne (N : K))

/-- `W⁻¹ = !![0, N⁻¹; -1, 0]`.

Deliberately not `@[simp]`: `Matrix.coe_units_inv` is itself `simp`, so simp rewrites this
left-hand side to `(!![0, -1; N, 0])⁻¹` and it is not in simp-normal form. -/
public theorem coe_inv_frickeGL :
    (↑(frickeGL K N)⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![0, (N : K)⁻¹; -1, 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, coe_frickeGL, Matrix.adjugate_fin_two_of,
    Ring.inverse_eq_inv]
  simp [Matrix.det_fin_two_of, NeZero.ne (N : K)]

/-- `W² = (-N) • 1` as matrices. This is the entrywise identity behind the centrality of `W²`
— its consumer is `frickeGL_sq_mul_comm` of
`TauCeti/NumberTheory/ModularForms/Fricke/Conjugation.lean` — and, later, behind the scalar the
normalized Fricke operator divides out. It is not itself a statement that `W²` is central.

Deliberately not `@[simp]`: the left-hand side `↑(W ^ 2)` is not in simp-normal form, since
`Units.val_pow_eq_pow_val` and the in-file simp lemma `coe_frickeGL` already rewrite its head to
`(!![0, -1; N, 0]) ^ 2`. Tagging it would put a non-normal left-hand side in the simp set. -/
public theorem coe_frickeGL_sq :
    (↑(frickeGL K N ^ 2) : Matrix (Fin 2) (Fin 2) K) =
      (-(N : K)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [sq, Units.val_mul, coe_frickeGL, Matrix.mul_fin_two]
  simp [Matrix.one_fin_two]

end TauCeti
