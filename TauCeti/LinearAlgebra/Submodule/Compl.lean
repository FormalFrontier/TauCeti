/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Complementary submodules induced on a subspace

Mathlib's `Submodule.isCompl_comap_subtype_of_isCompl_of_le` restricts a complementary pair to a
subspace that contains one of the two. This file records the variant that applies when neither
member of the pair lies in the subspace: a disjoint pair cuts a subspace `U` into a complementary
pair as soon as the two intersections with `U` span `U` — for a general `U` a genuine hypothesis,
not a consequence of spanning the ambient module.

## Main results

* `TauCeti.Submodule.isCompl_comap_subtype`: a disjoint pair of submodules whose intersections with
  `U` span `U` restricts to a complementary pair of submodules of `U`.
* `TauCeti.Submodule.eq_of_isCompl_of_le_of_disjoint`: a complement of `A` contained in a submodule
  disjoint from `A` is equal to it.
-/

public section

namespace TauCeti

universe u v

namespace Submodule

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A disjoint pair of submodules whose intersections with a subspace `U` span `U` cuts `U` into a
complementary pair of submodules. -/
theorem isCompl_comap_subtype {U A B : Submodule R M} (hAB : Disjoint A B)
    (hU : U ≤ U ⊓ A ⊔ U ⊓ B) :
    IsCompl (A.comap U.subtype) (B.comap U.subtype) := by
  constructor
  · rw [disjoint_iff, ← Submodule.comap_inf, disjoint_iff.mp hAB, Submodule.comap_bot,
      Submodule.ker_subtype]
  · rw [codisjoint_iff]
    refine Submodule.map_injective_of_injective U.subtype_injective ?_
    rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      Submodule.map_subtype_top]
    exact le_antisymm (sup_le inf_le_left inf_le_left) hU

/-- A complement of `A` that is contained in a submodule disjoint from `A` exhausts it: two
submodules disjoint from `A`, one of them a complement of `A` and contained in the other, are
equal. -/
theorem eq_of_isCompl_of_le_of_disjoint {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {A B C : Submodule R M} (hB : IsCompl A B) (hBC : B ≤ C)
    (hAC : Disjoint A C) : B = C := by
  refine le_antisymm hBC fun c hc ↦ ?_
  have hmem : c ∈ A ⊔ B := by
    rw [hB.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  have haC : a ∈ C := by
    have hsub : a = a + b - b := by simp
    rw [hsub]
    exact Submodule.sub_mem _ hc (hBC hb)
  rw [Submodule.disjoint_def.1 hAC a ha haC, zero_add]
  exact hb

end Submodule

end TauCeti
