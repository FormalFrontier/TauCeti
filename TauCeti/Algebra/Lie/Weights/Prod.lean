/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Linear
public import TauCeti.Algebra.Lie.Prod

public section

/-!
# Weight spaces of a product of Lie modules

For two modules `M` and `N` over a nilpotent Lie algebra, the generalized `χ`-weight space of
`M × N` is the product of the generalized `χ`-weight spaces of the factors. Consequently a linear
form is a weight of the product exactly when it is a weight of at least one factor, and a product of
modules with linear weights again has linear weights.

## Main results

* `TauCeti.mem_genWeightSpace_prod_iff`: membership in a generalized weight space is componentwise.
* `TauCeti.genWeightSpace_prod_eq_bot_iff`: a generalized weight space is trivial exactly when both
  corresponding spaces in the factors are trivial.
* `TauCeti.instLinearWeightsProd`: products of modules with linear weights have linear weights.
* `TauCeti.finrank_genWeightSpace_prod`: over a field, generalized weight-space dimensions add.

The first consumer is `TauCeti.formalCharacter_prod`, the product-additivity result supporting the
"Formal characters" target in Layer 6 of the highest-weight representation-theory roadmap.
-/

namespace TauCeti

open LieModule Module

universe u v w w₁

section CommRing

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [CommRing R] [LieRing L]
  [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- **Membership in a generalized weight space of a product is componentwise.** A vector lies in
the generalized `χ`-weight space of a product exactly when each component lies in the corresponding
generalized `χ`-weight space of its factor. -/
@[simp]
theorem mem_genWeightSpace_prod_iff {χ : L → R} {p : M × N} :
    p ∈ genWeightSpace (M × N) χ ↔ p.1 ∈ genWeightSpace M χ ∧ p.2 ∈ genWeightSpace N χ := by
  refine ⟨fun hp ↦ ⟨map_genWeightSpace_le (LieModuleHom.fst R L M N)
      ((LieSubmodule.mem_map _).mpr ⟨p, hp, by simp⟩),
    map_genWeightSpace_le (LieModuleHom.snd R L M N)
      ((LieSubmodule.mem_map _).mpr ⟨p, hp, by simp⟩)⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  have hl : (p.1, (0 : N)) ∈ genWeightSpace (M × N) χ :=
    map_genWeightSpace_le (LieModuleHom.inl R L M N)
      ((LieSubmodule.mem_map _).mpr ⟨p.1, h₁, by simp⟩)
  have hr : ((0 : M), p.2) ∈ genWeightSpace (M × N) χ :=
    map_genWeightSpace_le (LieModuleHom.inr R L M N)
      ((LieSubmodule.mem_map _).mpr ⟨p.2, h₂, by simp⟩)
  simpa using add_mem hl hr

/-- **A linear form is a weight of a product exactly when it is a weight of one factor.** -/
@[simp]
theorem genWeightSpace_prod_eq_bot_iff {χ : L → R} :
    genWeightSpace (M × N) χ = ⊥ ↔ genWeightSpace M χ = ⊥ ∧ genWeightSpace N χ = ⊥ := by
  constructor
  · refine fun h ↦ ⟨eq_bot_iff.mpr fun m hm ↦ ?_, eq_bot_iff.mpr fun n hn ↦ ?_⟩
    · have hmem : ((m, 0) : M × N) ∈ genWeightSpace (M × N) χ :=
        mem_genWeightSpace_prod_iff.mpr ⟨hm, zero_mem _⟩
      rw [h, LieSubmodule.mem_bot] at hmem
      exact (LieSubmodule.mem_bot _).mpr (Prod.mk_eq_zero.mp hmem).1
    · have hmem : ((0, n) : M × N) ∈ genWeightSpace (M × N) χ :=
        mem_genWeightSpace_prod_iff.mpr ⟨zero_mem _, hn⟩
      rw [h, LieSubmodule.mem_bot] at hmem
      exact (LieSubmodule.mem_bot _).mpr (Prod.mk_eq_zero.mp hmem).2
  · rintro ⟨h₁, h₂⟩
    refine eq_bot_iff.mpr fun p hp ↦ ?_
    obtain ⟨hp₁, hp₂⟩ := mem_genWeightSpace_prod_iff.mp hp
    rw [h₁, LieSubmodule.mem_bot] at hp₁
    rw [h₂, LieSubmodule.mem_bot] at hp₂
    exact (LieSubmodule.mem_bot _).mpr (Prod.ext hp₁ hp₂)

/-- A weight of a product of Lie modules is a weight of one of the two factors. -/
private theorem genWeightSpace_ne_bot_or {χ : L → R} (h : genWeightSpace (M × N) χ ≠ ⊥) :
    genWeightSpace M χ ≠ ⊥ ∨ genWeightSpace N χ ≠ ⊥ :=
  not_and_or.mp ((not_congr genWeightSpace_prod_eq_bot_iff).mp h)

/-- **The weights of a product of Lie modules are linear** as soon as those of both factors are,
since a weight of the product is a weight of one of the factors. -/
instance instLinearWeightsProd [LinearWeights R L M] [LinearWeights R L N] :
    LinearWeights R L (M × N) where
  map_add χ hχ := by
    rcases genWeightSpace_ne_bot_or hχ with h | h
    exacts [LinearWeights.map_add χ h, LinearWeights.map_add χ h]
  map_smul χ hχ := by
    rcases genWeightSpace_ne_bot_or hχ with h | h
    exacts [LinearWeights.map_smul χ h, LinearWeights.map_smul χ h]
  map_lie χ hχ := by
    rcases genWeightSpace_ne_bot_or hχ with h | h
    exacts [LinearWeights.map_lie χ h, LinearWeights.map_lie χ h]

end CommRing

section Field

variable {K : Type u} {L : Type v} {M : Type w} {N : Type w₁} [Field K] [LieRing L]
  [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N] [FiniteDimensional K N]

/-- The generalized weight space of a product, as a linear equivalence with the product of the
generalized weight spaces. -/
private noncomputable def genWeightSpaceProdEquiv (χ : L → K) :
    genWeightSpace (M × N) χ ≃ₗ[K] genWeightSpace M χ × genWeightSpace N χ where
  toFun p := (⟨(p : M × N).1, (mem_genWeightSpace_prod_iff.mp p.2).1⟩,
    ⟨(p : M × N).2, (mem_genWeightSpace_prod_iff.mp p.2).2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun q := ⟨((q.1 : M), (q.2 : N)), mem_genWeightSpace_prod_iff.mpr ⟨q.1.2, q.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Generalized weight-space dimensions of a product add.** -/
@[simp]
theorem finrank_genWeightSpace_prod (χ : L → K) :
    finrank K (genWeightSpace (M × N) χ)
      = finrank K (genWeightSpace M χ) + finrank K (genWeightSpace N χ) := by
  rw [(genWeightSpaceProdEquiv χ).finrank_eq, Module.finrank_prod]

end Field

end TauCeti
