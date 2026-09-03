/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Projection

public section

/-!
# Exact sequences and generalized weight spaces

Let a nilpotent Lie algebra `L` act on finite-dimensional triangularizable modules. This file
proves that a surjective homomorphism of `L`-modules remains surjective after restriction to any
generalized weight space. Consequently a short exact sequence of modules restricts to a short
exact sequence on every generalized weight space, and the dimensions of corresponding weight
spaces are additive.

The nontrivial point is surjectivity. Given a vector of weight `χ` in the target, choose an
arbitrary preimage and decompose it into generalized weight components. Equivariance sends each
component into the corresponding target weight space. Projecting the resulting sum onto `χ`
therefore gives a preimage lying in the `χ`-weight space.

## Main definitions and results

* `TauCeti.genWeightSpaceMap`: the restriction of a Lie-module homomorphism to a
  generalized weight space.
* `TauCeti.genWeightSpaceMap_surjective`: surjectivity is preserved by this restriction for
  finite-dimensional triangularizable modules.
* `TauCeti.genWeightSpaceMap_exact`: an exact pair restricts to an exact pair when its first map
  is injective.
* `TauCeti.finrank_genWeightSpace_add_finrank_genWeightSpace_eq`: generalized weight-space
  dimensions are additive in a short exact sequence.

## Roadmap

This is the weight-space input for additivity of formal characters in Layer 6, "Formal
characters", of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.5.
-/

namespace TauCeti

open LieModule Module

universe u v w w₁ w₂

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [CommRing R] [LieRing L]
  [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The restriction of a Lie-module homomorphism to the generalized weight space at `χ`. -/
def genWeightSpaceMap (f : M →ₗ⁅R,L⁆ N) (χ : L → R) :
    genWeightSpace M χ →ₗ[R] genWeightSpace N χ :=
  ((f.comp (genWeightSpace M χ).incl).codRestrict (genWeightSpace N χ) (fun m ↦
      map_genWeightSpace_le f ⟨m, m.2, rfl⟩)).toLinearMap

/-- Restricting a Lie-module homomorphism to a generalized weight space does not change its
underlying values. -/
@[simp]
theorem coe_genWeightSpaceMap_apply (f : M →ₗ⁅R,L⁆ N) (χ : L → R)
    (m : genWeightSpace M χ) : ((genWeightSpaceMap f χ m : genWeightSpace N χ) : N) = f m :=
  (rfl)

/-- An injective Lie-module homomorphism is injective on every generalized weight space. -/
theorem genWeightSpaceMap_injective (f : M →ₗ⁅R,L⁆ N) (χ : L → R)
    (hf : Function.Injective f) : Function.Injective (genWeightSpaceMap f χ) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

/-! ### Surjective maps -/

section Surjective

variable {K : Type u} {L : Type v} {M : Type w} {N : Type w₁} [Field K] [LieRing L]
  [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [FiniteDimensional K M] [FiniteDimensional K N]
  [IsTriangularizable K L M] [IsTriangularizable K L N]

open scoped Classical in
private theorem genWeightSpaceProjection_map_genWeightSpaceProjection
    (f : M →ₗ⁅K,L⁆ N) (x : M) (μ : Weight K L M) (ν : Weight K L N) :
    genWeightSpaceProjection K L N ν (f (genWeightSpaceProjection K L M μ x)) =
      if (μ : L → K) = (ν : L → K) then f (genWeightSpaceProjection K L M μ x) else 0 := by
  classical
  by_cases hμν : (μ : L → K) = (ν : L → K)
  · simp only [hμν, ↓reduceIte]
    apply genWeightSpaceProjection_apply_of_mem
    rw [← hμν]
    exact map_genWeightSpace_le f ⟨_, genWeightSpaceProjection_apply_mem μ x, rfl⟩
  · simp only [hμν, ↓reduceIte]
    let z := f (genWeightSpaceProjection K L M μ x)
    by_cases hz : z = 0
    · simp [z, hz]
    have hzmem : z ∈ genWeightSpace N (μ : L → K) :=
      map_genWeightSpace_le f ⟨_, genWeightSpaceProjection_apply_mem μ x, rfl⟩
    have hμspace : genWeightSpace N (μ : L → K) ≠ ⊥ := by
      intro hbot
      have hzbot : z ∈ (⊥ : LieSubmodule K L N) := hbot ▸ hzmem
      exact hz (by simpa using hzbot)
    let μN : Weight K L N := ⟨(μ : L → K), hμspace⟩
    have hμNν : μN ≠ ν := fun h ↦ hμν
      (congrArg (fun ψ : Weight K L N ↦ (ψ : L → K)) h)
    simpa [z] using genWeightSpaceProjection_apply_of_mem_of_ne hμNν hzmem

open scoped Classical in
private noncomputable def genWeightSpacePreimage (f : M →ₗ⁅K,L⁆ N)
    (hf : Function.Surjective f) (χ : L → K) (y : genWeightSpace N χ) : M :=
  ∑ μ : Weight K L M, if (μ : L → K) = χ then
    genWeightSpaceProjection K L M μ (Classical.choose (hf y)) else 0

omit [FiniteDimensional K N] [IsTriangularizable K L N] in
private theorem genWeightSpacePreimage_mem (f : M →ₗ⁅K,L⁆ N) (hf : Function.Surjective f)
    (χ : L → K) (y : genWeightSpace N χ) :
    genWeightSpacePreimage f hf χ y ∈ genWeightSpace M χ := by
  classical
  apply Submodule.sum_mem
  intro μ _
  split
  · rename_i hμ
    have hle : genWeightSpace M (μ : L → K) ≤ genWeightSpace M χ := by
      simpa only [hμ] using (le_refl (genWeightSpace M χ))
    exact hle (genWeightSpaceProjection_apply_mem μ _)
  · exact LieSubmodule.zero_mem _

omit [FiniteDimensional K N] [IsTriangularizable K L N] in
private theorem map_genWeightSpacePreimage_eq_of_eq_bot (f : M →ₗ⁅K,L⁆ N)
    (hf : Function.Surjective f) (χ : L → K) (y : genWeightSpace N χ)
    (hχ : genWeightSpace N χ = ⊥) : f (genWeightSpacePreimage f hf χ y) = y := by
  classical
  have hy : (y : N) = 0 := by
    have : (y : N) ∈ (⊥ : LieSubmodule K L N) := hχ ▸ y.2
    simpa using this
  rw [hy]
  simp only [genWeightSpacePreimage, map_sum]
  apply Finset.sum_eq_zero
  intro μ _
  split
  · rename_i hμ
    have hmem : (f : M →ₗ[K] N)
        (genWeightSpaceProjection K L M μ (Classical.choose (hf y))) ∈
        genWeightSpace N χ := by
      have := map_genWeightSpace_le f
        ⟨_, genWeightSpaceProjection_apply_mem μ (Classical.choose (hf y)), rfl⟩
      simpa only [hμ] using this
    have hbot : (f : M →ₗ[K] N)
        (genWeightSpaceProjection K L M μ (Classical.choose (hf y))) ∈
        (⊥ : LieSubmodule K L N) := hχ ▸ hmem
    simpa using hbot
  · simp

private theorem map_genWeightSpacePreimage_eq_of_ne_bot (f : M →ₗ⁅K,L⁆ N)
    (hf : Function.Surjective f) (χ : L → K) (y : genWeightSpace N χ)
    (hχ : genWeightSpace N χ ≠ ⊥) : f (genWeightSpacePreimage f hf χ y) = y := by
  classical
  let ν : Weight K L N := ⟨χ, hχ⟩
  let x := Classical.choose (hf y)
  have hx : f x = y := Classical.choose_spec (hf y)
  have hdecomp : ∑ μ : Weight K L M,
      f (genWeightSpaceProjection K L M μ x) = y := by
    rw [← map_sum, sum_genWeightSpaceProjection_apply, hx]
  have hsum := congrArg (genWeightSpaceProjection K L N ν) hdecomp
  have hyν : (y : N) ∈ genWeightSpace N (ν : L → K) := by
    have hle : genWeightSpace N χ ≤ genWeightSpace N (ν : L → K) := by
      simpa only [Weight.coe_weight_mk, ν] using (le_refl (genWeightSpace N χ))
    exact hle y.2
  rw [map_sum, genWeightSpaceProjection_apply_of_mem hyν] at hsum
  simp_rw [genWeightSpaceProjection_map_genWeightSpaceProjection f x] at hsum
  have hsum' : (∑ μ : Weight K L M,
      if (μ : L → K) = χ then f (genWeightSpaceProjection K L M μ x) else 0) = y := by
    simpa only [Weight.coe_weight_mk, ν] using hsum
  rw [genWeightSpacePreimage, map_sum]
  -- Naming the chosen preimage above makes both occurrences use the same proof of surjectivity;
  -- the dependent `Classical.choose` term otherwise prevents the following sum from elaborating.
  change (∑ μ : Weight K L M,
    f (if (μ : L → K) = χ then genWeightSpaceProjection K L M μ x else 0)) = y
  calc
    _ = ∑ μ : Weight K L M,
        if (μ : L → K) = χ then f (genWeightSpaceProjection K L M μ x) else 0 := by
      apply Finset.sum_congr rfl
      intro μ _
      by_cases hμ : (μ : L → K) = χ <;> simp [hμ]
    _ = y := hsum'

private theorem map_genWeightSpacePreimage_eq (f : M →ₗ⁅K,L⁆ N)
    (hf : Function.Surjective f) (χ : L → K) (y : genWeightSpace N χ) :
    f (genWeightSpacePreimage f hf χ y) = y := by
  by_cases hχ : genWeightSpace N χ = ⊥
  · exact map_genWeightSpacePreimage_eq_of_eq_bot f hf χ y hχ
  · exact map_genWeightSpacePreimage_eq_of_ne_bot f hf χ y hχ

/-- A surjective homomorphism between finite-dimensional triangularizable Lie modules maps every
generalized weight space onto the corresponding generalized weight space. -/
theorem genWeightSpaceMap_surjective (f : M →ₗ⁅K,L⁆ N) (hf : Function.Surjective f)
    (χ : L → K) : Function.Surjective (genWeightSpaceMap f χ) := by
  intro y
  refine ⟨⟨genWeightSpacePreimage f hf χ y,
    genWeightSpacePreimage_mem f hf χ y⟩, Subtype.ext ?_⟩
  exact map_genWeightSpacePreimage_eq f hf χ y

end Surjective

/-! ### Short exact sequences -/

section Exact

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

/-- An exact pair of Lie-module homomorphisms restricts to an exact pair on each generalized
weight space when the first homomorphism is injective. -/
theorem genWeightSpaceMap_exact (f : M →ₗ⁅R,L⁆ N) (g : N →ₗ⁅R,L⁆ P)
    (h : Function.Exact f g) (hf : Function.Injective f) (χ : L → R) :
    Function.Exact (genWeightSpaceMap f χ) (genWeightSpaceMap g χ) := by
  intro y
  constructor
  · intro hy
    have hgy : g y = 0 := by
      have := congrArg Subtype.val hy
      simpa using this
    obtain ⟨x, hx⟩ := (h (y : N)).mp hgy
    have hxmem : x ∈ genWeightSpace M χ := by
      rw [← comap_genWeightSpace_eq_of_injective hf]
      rw [LieSubmodule.mem_comap, hx]
      exact y.2
    refine ⟨⟨x, hxmem⟩, Subtype.ext ?_⟩
    exact hx
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (h _).mpr ⟨x, rfl⟩

end Exact

section Finrank

variable {K : Type u} {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂}
  [Field K] [LieRing L] [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup P] [Module K P] [LieRingModule L P] [LieModule K L P]
  [FiniteDimensional K N] [FiniteDimensional K P]
  [IsTriangularizable K L N] [IsTriangularizable K L P]

/-- **Generalized weight-space dimensions are additive in a short exact sequence.** -/
theorem finrank_genWeightSpace_add_finrank_genWeightSpace_eq
    (f : M →ₗ⁅K,L⁆ N) (g : N →ₗ⁅K,L⁆ P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) (χ : L → K) :
    finrank K (genWeightSpace M χ) + finrank K (genWeightSpace P χ) =
      finrank K (genWeightSpace N χ) := by
  let fχ := genWeightSpaceMap f χ
  let gχ := genWeightSpaceMap g χ
  have hfχ : Function.Injective fχ := genWeightSpaceMap_injective f χ hf
  have hgχ : Function.Surjective gχ := genWeightSpaceMap_surjective g hg χ
  have hχ : Function.Exact fχ gχ := genWeightSpaceMap_exact f g h hf χ
  have hrange_f := LinearMap.finrank_range_of_inj hfχ
  have hrange_g : finrank K gχ.range = finrank K (genWeightSpace P χ) := by
    rw [LinearMap.range_eq_top.mpr hgχ, finrank_top]
  have hrank := gχ.finrank_range_add_finrank_ker
  rw [hχ.linearMap_ker_eq, hrange_f, hrange_g] at hrank
  omega

end Finrank

end TauCeti
