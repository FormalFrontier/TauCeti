/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Order properties of semistandard Young tableaux

Mathlib's `SemistandardYoungTableau` records that entries increase weakly along each row and
strictly down each column, each within a single row or column. This file combines the two into the
two-dimensional statement that consumers actually reach for, comparing entries that differ in both
coordinates at once: an entry is bounded by any entry weakly below and to the right of it.

The material is deliberately kept in its own module, upstream of the contents and Kostka-number
theory, so that a basic order fact about tableaux does not oblige a consumer to import that
theory.

## Main declarations

* `SemistandardYoungTableau.entry_le_of_le`: entries increase weakly to the right and downwards.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The entries of a semistandard Young tableau increase weakly to the right and downwards. -/
theorem entry_le_of_le (T : SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)

end SemistandardYoungTableau
