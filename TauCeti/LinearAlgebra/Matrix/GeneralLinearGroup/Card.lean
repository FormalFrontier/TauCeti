/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Non-public: `Matrix.card_GL_field` is what the two factorizations below are read off, in the
-- proofs only.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The order of `GL₂` over a finite field

Mathlib's `Matrix.card_GL_field` gives `|GL n 𝔽_q| = ∏ i, (qⁿ - qⁱ)`, which in size two reads
`(q² - 1)(q² - q)`. That form is a product of differences, and every index computation in `GL₂`
divides it by the order of a subgroup, so what is wanted is the factored form
`(q - 1)² · q · (q + 1)`, where the natural subtraction has already been carried out. It is
recorded here in the two associations the two maximal tori call for: the split torus has order
`(q - 1)²` and the non-split one `q² - 1`.

## Main results

* `TauCeti.natCard_GL_fin_two`: `|GL₂(𝔽_q)| = (q - 1)² · q(q + 1)`.
* `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: `|GL₂(𝔽_q)| = (q² - 1) · q(q - 1)`.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)".
-/

public section

namespace TauCeti

variable (F : Type*) [Field F] [Fintype F]

/-- **The order of `GL₂` over a finite field**, in the factored form `(q - 1)² · q(q + 1)`: the
first factor is the order of the split torus and the second its index. -/
theorem natCard_GL_fin_two :
    Nat.card (GL (Fin 2) F) =
      (Fintype.card F - 1) ^ 2 * (Fintype.card F * (Fintype.card F + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 :=
    ⟨Fintype.card F - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have h1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have h2 : (m + 1) ^ 2 - (m + 1) = m * (m + 1) := by
    have : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
    omega
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hm]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.add_sub_cancel, h1, h2]
  ring

/-- **The order of `GL₂` over a finite field**, in the factored form `(q² - 1) · q(q - 1)`: the
first factor is the order of the non-split torus and the second its index. -/
theorem natCard_GL_fin_two_eq_sq_sub_one_mul :
    Nat.card (GL (Fin 2) F) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F * (Fintype.card F - 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 :=
    ⟨Fintype.card F - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have h1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  rw [natCard_GL_fin_two, hm]
  simp only [Nat.add_sub_cancel, h1]
  ring

end TauCeti
