/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.EulerForm
import Mathlib.Tactic.Linarith

/-!
# The Euler and Tits forms of the generalized Kronecker quiver

This file evaluates the Euler and Tits forms of the generalized Kronecker quiver in the
coordinates of its two vertices. The arithmetic of the Tits form pins down exactly where the
boundary of Gabriel's theorem lies: writing `n` for the number of arrows,

* `titsForm d = d src ^ 2 + d tgt ^ 2 - n * (d src * d tgt)`;
* it is positive definite iff `n ≤ 1`;
* it is positive semidefinite iff `n ≤ 2`, and for `n = 2` it is the perfect square
  `(d src - d tgt) ^ 2`, whose radical is the line spanned by the constant vector `(1, 1)` -- the
  null root of the affine root system `Ã₁`.

## Main results

* `TauCeti.Quiver.Kronecker.eulerForm_apply` and `TauCeti.Quiver.Kronecker.titsForm_apply`: the
  Euler and Tits forms in coordinates.
* `TauCeti.Quiver.Kronecker.titsForm_posDef_iff` and
  `TauCeti.Quiver.Kronecker.titsForm_nonneg_iff`: the two thresholds `n ≤ 1` and `n ≤ 2`.
* `TauCeti.Quiver.Kronecker.titsForm_eq_zero_iff_exists_smul` and
  `TauCeti.Quiver.Kronecker.titsForm_eq_one_iff`: for the Kronecker quiver the radical of the Tits
  form is the line spanned by `(1, 1)`, and the vectors of Tits norm one are those whose two
  coordinates differ by one.

## References

This file supplies the positive semidefinite Tits form `(a - b) ^ 2` with radical `(1, 1)` asked
for by the “Kronecker quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v

namespace Quiver.Kronecker

variable {A : Type v} [Fintype A]

/-- The Euler form of the generalized Kronecker quiver, in the coordinates of its two vertices. -/
-- Deliberately not `@[simp]`: `TauCeti.eulerForm_def` together with `sum_univ` and
-- `card_hom_src_tgt` already rewrites `eulerForm (Kronecker A) d e` to the right-hand side below,
-- so tagging this lemma would only duplicate that normal form.
theorem eulerForm_apply (d e : Kronecker A → ℤ) :
    eulerForm (Kronecker A) d e =
      d src * e src + d tgt * e tgt - (Fintype.card A : ℤ) * (d src * e tgt) := by
  rw [eulerForm_eq_sum_card]
  simp only [sum_univ, card_hom_src_tgt, Fintype.card_eq_zero, Nat.cast_zero]
  ring

/-- The Tits form of the generalized Kronecker quiver on `n` arrows is
`q(d) = d₁ ^ 2 + d₂ ^ 2 - n * d₁ * d₂`. -/
-- Deliberately not `@[simp]`: `TauCeti.titsForm_def` is already `simp`, so `simp` rewrites
-- `titsForm` to `eulerForm` and reaches the same normal form as `eulerForm_apply` above; tagging
-- this lemma too would only add one that never fires.
theorem titsForm_apply (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d =
      d src ^ 2 + d tgt ^ 2 - (Fintype.card A : ℤ) * (d src * d tgt) := by
  rw [titsForm_def, eulerForm_apply]
  ring

/-- The Tits form on the constant dimension vector `(1, 1)` is `2 - n`. This single value decides
both thresholds below. -/
private theorem titsForm_one : titsForm (Kronecker A) 1 = 2 - (Fintype.card A : ℤ) := by
  rw [titsForm_apply, Pi.one_apply, Pi.one_apply]
  ring

/-- Doubling the Tits form splits it into the two pieces `(2 - n) * (d₁ ^ 2 + d₂ ^ 2)` and
`n * (d₁ - d₂) ^ 2`, both nonnegative as soon as `n ≤ 2`. -/
private theorem two_mul_titsForm (d : Kronecker A → ℤ) :
    2 * titsForm (Kronecker A) d =
      (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2)
        + (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 := by
  rw [titsForm_apply]
  ring

/-- With at most two arrows the Tits form is positive semidefinite. -/
theorem titsForm_nonneg (h : Fintype.card A ≤ 2) (d : Kronecker A → ℤ) :
    0 ≤ titsForm (Kronecker A) d := by
  have hn : (Fintype.card A : ℤ) ≤ 2 := by exact_mod_cast h
  have h₁ : 0 ≤ (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have h₂ : 0 ≤ (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 :=
    mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
  have h₃ := two_mul_titsForm (A := A) d
  linarith

/-- The Tits form of the generalized Kronecker quiver is positive semidefinite exactly when there
are at most two arrows. Two arrows is the Kronecker quiver `• ⇉ •`, of affine type `Ã₁`, the
boundary case of Gabriel's theorem; three or more arrows makes the form indefinite. -/
theorem titsForm_nonneg_iff : (∀ d, 0 ≤ titsForm (Kronecker A) d) ↔ Fintype.card A ≤ 2 := by
  refine ⟨fun h => ?_, fun h => titsForm_nonneg h⟩
  have h1 := h 1
  rw [titsForm_one] at h1
  omega

/-- With at most one arrow the Tits form is positive definite: these are the quivers of type
`A₁ ⊔ A₁` (no arrow) and `A₂` (one arrow). -/
theorem titsForm_posDef (h : Fintype.card A ≤ 1) : (titsForm (Kronecker A)).PosDef := by
  intro d hd
  have hn : (Fintype.card A : ℤ) ≤ 1 := by exact_mod_cast h
  have hpos : 0 < d src ^ 2 + d tgt ^ 2 := by
    rcases eq_or_ne (d src) 0 with hs | hs
    · have ht : d tgt ≠ 0 := fun ht => hd (eq_zero_iff.mpr ⟨hs, ht⟩)
      have := sq_pos_of_ne_zero ht
      have := sq_nonneg (d src)
      linarith
    · have := sq_pos_of_ne_zero hs
      have := sq_nonneg (d tgt)
      linarith
  have h₁ : d src ^ 2 + d tgt ^ 2
      ≤ (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2) := by nlinarith
  have h₂ : 0 ≤ (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 :=
    mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
  have h₃ := two_mul_titsForm (A := A) d
  linarith

/-- The Tits form of the generalized Kronecker quiver is positive definite exactly when there is at
most one arrow: no arrow gives the disconnected Dynkin quiver `A₁ ⊔ A₁`, and one arrow gives `A₂`.
Every other generalized Kronecker quiver falls outside the Dynkin classification. -/
theorem titsForm_posDef_iff : (titsForm (Kronecker A)).PosDef ↔ Fintype.card A ≤ 1 := by
  refine ⟨fun h => ?_, titsForm_posDef⟩
  have h1 : (0 : ℤ) < titsForm (Kronecker A) 1 :=
    h 1 fun hc => one_ne_zero (congrFun hc src)
  rw [titsForm_one] at h1
  omega

/-! ### The Kronecker quiver itself -/

section Two

variable (h : Fintype.card A = 2)
include h

/-- The Tits form of the Kronecker quiver is the perfect square `(d₁ - d₂) ^ 2`. -/
theorem titsForm_eq_sq (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = (d src - d tgt) ^ 2 := by
  rw [titsForm_apply, h]
  push_cast
  ring

/-- The Tits form of the Kronecker quiver vanishes exactly on the diagonal. -/
theorem titsForm_eq_zero_iff (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 0 ↔ d src = d tgt := by
  rw [titsForm_eq_sq h, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-- The radical of the Tits form of the Kronecker quiver is the line spanned by the constant vector
`(1, 1)`: the null root of the affine root system `Ã₁`. -/
theorem titsForm_eq_zero_iff_exists_smul (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 0 ↔ ∃ c : ℤ, d = c • 1 := by
  rw [titsForm_eq_zero_iff h]
  refine ⟨fun hd => ⟨d src, funext fun v => ?_⟩, ?_⟩
  · cases v
    · simp
    · simp [hd]
  · rintro ⟨c, rfl⟩
    simp

/-- For the Kronecker quiver the integer vectors of Tits norm one -- the real roots of the affine
root system `Ã₁`, positive and negative alike -- are exactly those whose two coordinates differ by
one, that is `(m, m + 1)` and `(m + 1, m)`. -/
theorem titsForm_eq_one_iff (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 1 ↔ d src = d tgt + 1 ∨ d tgt = d src + 1 := by
  rw [titsForm_eq_sq h, sq_eq_one_iff]
  omega

/-- The Tits form of the Kronecker quiver is not positive definite: it is isotropic on the nonzero
vector `(1, 1)`. Together with `TauCeti.Quiver.Kronecker.titsForm_nonneg` this says it is positive
semidefinite but degenerate, which is what places the Kronecker quiver on the boundary of Gabriel's
dichotomy. -/
theorem not_titsForm_posDef : ¬ (titsForm (Kronecker A)).PosDef := by
  rw [titsForm_posDef_iff, h]
  omega

end Two

end Quiver.Kronecker

end TauCeti
