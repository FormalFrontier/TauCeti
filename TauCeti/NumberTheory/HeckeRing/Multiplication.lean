/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Support

/-!
# Hecke rings: the convolution product

The convolution product
`HeckeCosetModule Δ H₁ H₂ R × HeckeCosetModule Δ H₂ H₃ R → HeckeCosetModule Δ H₁ H₃ R`
of Hecke coset modules with coefficients in a semiring `R`, following [Shimura][shimura1971],
Chapter 3. On basis elements the product is `[D₁] * [D₂] = ∑_D m(D₁, D₂; D) [D]`, where the
structure constants `m` are Shimura's multiplicities cast into `R`. On the diagonal
`H₁ = H₂ = H₃` this is the multiplication of the Hecke ring.

Vendored from the in-review mathlib4 PR
[#41277](https://github.com/leanprover-community/mathlib4/pull/41277) (Chris Birkbeck), per the
ModularForms roadmap's dependency policy; migrate to Mathlib and delete this file when that
stack merges.

## Main definitions

* `HeckeCosetModule.structureConstants`: the formal sum `∑_D m(g₁, g₂; D) [D]` of the structure
  constants of a product of two double cosets.
* `HeckeCosetModule.mul`: the convolution product
  `HeckeCosetModule Δ H₁ H₂ R → HeckeCosetModule Δ H₂ H₃ R → HeckeCosetModule Δ H₁ H₃ R`.

## Main results

* `HeckeCosetModule.single_mul_single`: the product of two basis elements.
* `HeckeCosetModule.mul_single_single_of_mulMap_eq`: when the coset decomposition of `D₁ · D₂`
  multiplies into a single coset `D₃` with multiplicity at most one, `[D₁] · [D₂] = [D₃]` —
  stated for three subgroups and `mul`, so it covers the bimodule case, not only the ring.
* the `NonUnitalNonAssocSemiring (𝕋 Δ H R)` instance.
-/

public section

open DoubleCoset Finsupp
open scoped Pointwise

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

variable (R : Type*) [Semiring R]

open Classical in
/-- The structure constants of the Hecke product: `structureConstants H₁ H₂ H₃ R g₁ g₂` is the
formal sum `∑_D m(g₁, g₂; D) [D]` over mixed double cosets, with Shimura's multiplicities cast
into `R`. -/
noncomputable def structureConstants (H₁ H₂ H₃ : Subgroup G) [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] (g₁ g₂ : Δ) : HeckeCosetModule Δ H₁ H₃ R :=
  Finsupp.onFinset (Finset.univ.image (HeckeCoset.mulMap H₁ H₂ H₃ g₁ g₂))
    (fun D ↦ (multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (D.rep : G) : R))
    (fun D hD ↦ (HeckeCoset.mem_image_mulMap_iff g₁ g₂ D).mpr
      fun h0 ↦ hD (by rw [h0, Nat.cast_zero]))

@[simp] lemma structureConstants_apply [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (g₁ g₂ : Δ) (D : HeckeCoset Δ H₁ H₃) :
    structureConstants R H₁ H₂ H₃ g₁ g₂ D =
      (multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (D.rep : G) : R) := (rfl)

open Classical in
/-- The support of the structure constants is contained in the image of `mulMap`. -/
lemma support_structureConstants_subset [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] (g₁ g₂ : Δ) :
    (structureConstants R H₁ H₂ H₃ g₁ g₂).support ⊆
      Finset.univ.image (HeckeCoset.mulMap H₁ H₂ H₃ g₁ g₂) :=
  Finsupp.support_onFinset_subset

/-- The convolution product of Hecke coset modules, defined via the structure constants. The
diagonal case is the multiplication of the Hecke ring; see the `Mul (𝕋 Δ H R)` instance. -/
noncomputable def mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) :
    HeckeCosetModule Δ H₁ H₃ R :=
  f.sum fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep

lemma mul_eq_sum [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) : mul R f g =
      f.sum fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep :=
  (rfl)

/-- The multiplication of the Hecke ring: the diagonal case of the convolution product
`HeckeCosetModule.mul`. -/
noncomputable instance instMulHeckeRing {H : Subgroup G} [IsHeckeTriple Δ H H] :
    Mul (𝕋 Δ H R) where
  mul f g := mul R f g

lemma mul_def {H : Subgroup G} [IsHeckeTriple Δ H H] (f g : 𝕋 Δ H R) :
    f * g = mul R f g := (rfl)

/-- The convolution product of two basis elements. -/
lemma mul_single_single [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (D₁ : HeckeCoset Δ H₁ H₂) (D₂ : HeckeCoset Δ H₂ H₃) (a b : R) :
    mul R (single R D₁ a) (single R D₂ b) =
      a • b • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep := by
  rw [mul_eq_sum, sum_single_index, sum_single_index]
  · simp
  · rw [sum_single_index] <;> simp

/-- The product of two basis elements of the Hecke ring. -/
lemma single_mul_single {H : Subgroup G} [IsHeckeTriple Δ H H]
    (D₁ D₂ : HeckeCoset Δ H H) (a b : R) :
    single R D₁ a * single R D₂ b = a • b • structureConstants R H H H D₁.rep D₂.rep :=
  mul_single_single R D₁ D₂ a b

/-- **The single-basis-element product criterion.** If every pair in the coset decomposition of
`D₁ · D₂` multiplies into the single double coset `D₃`, and `D₃` occurs there with multiplicity
at most one, then the product of the two basis elements is the third basis element.

Stated at the natural level of the convolution: three subgroups and `mul R`, so it applies to
the whole `HeckeCosetModule` bimodule API and not only to the ring case `H₁ = H₂ = H₃`. This is
the structure-constant computation shared by every "a product of basis elements is again a
basis element" result; only the two hypotheses vary between them. -/
lemma mul_single_single_of_mulMap_eq [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (D₁ : HeckeCoset Δ H₁ H₂) (D₂ : HeckeCoset Δ H₂ H₃) (D₃ : HeckeCoset Δ H₁ H₃)
    (hmulMap : ∀ p, HeckeCoset.mulMap H₁ H₂ H₃ D₁.rep D₂.rep p = D₃)
    (hmul : multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (D₃.rep : G) ≤ 1) :
    mul R (single R D₁ 1) (single R D₂ 1) = single R D₃ 1 := by
  classical
  have hSC : structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep = single R D₃ 1 := by
    ext A
    rw [structureConstants_apply, single_apply]
    split_ifs with h
    · rw [← h]
      have hne : multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (D₃.rep : G) ≠ 0 := by
        rw [← HeckeCoset.mem_image_mulMap_iff]
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨(Classical.arbitrary _, Classical.arbitrary _), hmulMap _⟩
      have heq : multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (D₃.rep : G) = 1 := by omega
      rw [heq, Nat.cast_one]
    · have hzero : multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) ((A.rep : G)) = 0 := by
        by_contra h0
        refine h ?_
        have hmem := (HeckeCoset.mem_image_mulMap_iff _ _ A).mpr h0
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
        obtain ⟨p, hp⟩ := hmem
        rw [← hp, hmulMap p]
      rw [hzero, Nat.cast_zero]
  rw [mul_single_single, hSC, smul_single_one, smul_single_one]

/-- The convolution product distributes over addition on the right. -/
lemma mul_add [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g h : HeckeCosetModule Δ H₂ H₃ R) :
    mul R f (g + h) = mul R f g + mul R f h := by
  classical
  simp only [mul_eq_sum]
  exact (Finsupp.sum_congr fun D₁ _ ↦ Finsupp.sum_add_index (fun _ _ ↦ by simp)
    (fun _ _ b b' ↦ by rw [add_smul, smul_add])).trans Finsupp.sum_add

/-- The convolution product distributes over addition on the left. -/
lemma add_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f g : HeckeCosetModule Δ H₁ H₂ R) (h : HeckeCosetModule Δ H₂ H₃ R) :
    mul R (f + g) h = mul R f h + mul R g h := by
  classical
  simp only [mul_eq_sum]
  exact Finsupp.sum_add_index
    (fun _ _ ↦ by simp only [zero_smul]; exact Finsupp.sum_fun_zero (f := h))
    fun _ _ b b' ↦ (Finsupp.sum_congr fun D₂ _ ↦ by rw [add_smul]).trans Finsupp.sum_add

/-- The convolution product vanishes on the left zero. -/
lemma zero_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₂ H₃ R) : mul R (0 : HeckeCosetModule Δ H₁ H₂ R) f = 0 := by
  simp only [mul_eq_sum]
  exact Finsupp.sum_zero_index

/-- The convolution product vanishes on the right zero. -/
lemma mul_zero [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) : mul R f (0 : HeckeCosetModule Δ H₂ H₃ R) = 0 := by
  simp only [mul_eq_sum]
  exact (congrArg (Finsupp.sum f) (funext₂ fun _ _ ↦ Finsupp.sum_zero_index)).trans
    (Finsupp.sum_fun_zero f)

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance instNonUnitalNonAssocSemiringHeckeRing {H : Subgroup G}
    [IsHeckeTriple Δ H H] :
    NonUnitalNonAssocSemiring (𝕋 Δ H R) :=
  { (inferInstance : AddCommMonoid (𝕋 Δ H R)), (inferInstance : Mul (𝕋 Δ H R)) with
    left_distrib := fun f g h ↦ mul_add R f g h
    right_distrib := fun f g h ↦ add_mul R f g h
    zero_mul := fun f ↦ zero_mul R f
    mul_zero := fun f ↦ mul_zero R f }

end HeckeCosetModule
