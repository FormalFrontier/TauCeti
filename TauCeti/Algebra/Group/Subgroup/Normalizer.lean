/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normality from elementwise commutation with a generating subgroup

A subgroup is normal as soon as its normalizer is everything, and the normalizer contains both the
subgroup itself and anything centralising it. So a subgroup `C` that is centralised elementwise by
a subgroup `P` with `C ⊔ P = ⊤` is normal. Mathlib has each ingredient
(`Subgroup.normalizer_eq_top_iff`, `Subgroup.le_normalizer`,
`Subgroup.centralizer_le_normalizer`) but not this combination.

## Main results

* `TauCeti.normal_of_commute_of_sup_eq_top`: a subgroup centralised elementwise by a subgroup that
  joins with it to the whole group is normal.
-/

public section

namespace TauCeti

open Subgroup

variable {G : Type*} [Group G]

/-- A subgroup centralised elementwise by a subgroup that joins with it to the whole group is
normal.

The commutation hypothesis is elementwise rather than `P ≤ centralizer C` because that is the form
a direct-product decomposition supplies; `C ⊔ P = ⊤` is weaker than `C` and `P` being complements,
which is what such a decomposition actually gives. -/
theorem normal_of_commute_of_sup_eq_top {C P : Subgroup G}
    (hcomm : ∀ c ∈ C, ∀ x ∈ P, Commute c x) (hsup : C ⊔ P = ⊤) : C.Normal := by
  -- `C` is normalised by itself and centralised by `P`, and the two generate `G`.
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
  exact sup_le le_normalizer fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun c hc => hcomm c hc x hx)

end TauCeti
