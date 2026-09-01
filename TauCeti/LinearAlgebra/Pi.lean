/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Disjointness of `Submodule.pi` supports

For `s : Set ι`, the submodule `Submodule.pi sᶜ (fun _ ↦ ⊥)` of `ι → M` consists of the families
vanishing outside `s` — the `Pi` analogue of `Finsupp.supported`. This file records that
complementary supports meet in `⊥`.

Mathlib has `Set.disjoint_pi`, but that is about `Set.pi` and characterises disjointness through
the fibres; it says nothing about the submodules cut out by a support condition.

## Main results

* `Submodule.disjoint_pi_compl_bot_of_disjoint`: disjoint index sets give disjoint submodules of
  families vanishing outside them.
-/

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]

/-- **Disjoint sets of indices give disjoint submodules of families vanishing outside them.**
A family vanishing outside `s` and outside `t` at once, for `s` and `t` disjoint, vanishes
everywhere. The submodules are `Submodule.pi` at the zero submodule.

Nothing here is topological or about any particular index type; the Huber two-sided series use it
at `ι = ℤ` with `s` and `t` the non-negative and negative degrees. -/
public theorem disjoint_pi_compl_bot_of_disjoint {ι : Type*} {s t : Set ι} (h : Disjoint s t) :
    Disjoint (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (Submodule.pi tᶜ fun _ ↦ (⊥ : Submodule A M)) :=
  Submodule.disjoint_def.mpr fun f hs ht ↦ funext fun i ↦ by
    by_cases hi : i ∈ s
    · exact ht i (Set.disjoint_left.mp h hi)
    · exact hs i hi

end Submodule
