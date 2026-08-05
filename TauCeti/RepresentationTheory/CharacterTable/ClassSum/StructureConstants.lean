/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis

/-!
# Structure constants of the class algebra

For conjugacy classes `Cᵢ`, `Cⱼ`, and `Cₖ` of a finite group, the structure constant
`structureConstant Cᵢ Cⱼ Cₖ` counts factorizations `x * y = g`, where `x ∈ Cᵢ`, `y ∈ Cⱼ`, and
`g` is any representative of `Cₖ`. Conjugating both factors proves that this count is independent
of the representative.

These natural numbers are the coefficients for multiplication in the class-sum basis of the center
of the group algebra. They are the integral input to the Dixon--Schneider character-table
algorithm. The class of `1` is a unit for them
(`TauCeti.structureConstant_mk_one_right`), since its class sum is the unit of the group algebra.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The type of factorizations of `g` with first factor in `Cᵢ` and second factor in `Cⱼ`. -/
private def StructureConstantFiber (Cᵢ Cⱼ : ConjClasses G) (g : G) :=
  {p : Cᵢ.carrier × Cⱼ.carrier // (p.1.1 : G) * p.2.1 = g}

private instance (Cᵢ Cⱼ : ConjClasses G) (g : G) :
    Fintype (StructureConstantFiber Cᵢ Cⱼ g) :=
  by
    unfold StructureConstantFiber
    infer_instance

private def structureConstantFiberEquiv (Cᵢ Cⱼ : ConjClasses G) {g h : G}
    (s : G) (hs : s * g * s⁻¹ = h) :
    StructureConstantFiber Cᵢ Cⱼ g ≃ StructureConstantFiber Cᵢ Cⱼ h where
  toFun p := ⟨
    (conjugateCarrierEquiv s Cᵢ p.1.1, conjugateCarrierEquiv s Cⱼ p.1.2),
    by simpa [conj_mul, p.2] using hs⟩
  invFun p := ⟨
    (conjugateCarrierEquiv s⁻¹ Cᵢ p.1.1, conjugateCarrierEquiv s⁻¹ Cⱼ p.1.2),
    by
      rw [conjugateCarrierEquiv_apply, conjugateCarrierEquiv_apply, conj_mul, p.2]
      rw [← hs]
      simp [mul_assoc]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [conjugateCarrierEquiv_apply, mul_assoc]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [conjugateCarrierEquiv_apply, mul_assoc]

/-- The number of factorizations `x * y = g`, for `x ∈ Cᵢ`, `y ∈ Cⱼ`, and any representative
`g` of `Cₖ`. This is independent of the representative by simultaneous conjugation. -/
def structureConstant (Cᵢ Cⱼ Cₖ : ConjClasses G) : ℕ :=
  Quotient.liftOn Cₖ
    (fun g => Fintype.card (StructureConstantFiber Cᵢ Cⱼ g))
    fun g h hgh => by
      obtain ⟨s, hs⟩ := isConj_iff.mp hgh
      exact Fintype.card_congr (structureConstantFiberEquiv Cᵢ Cⱼ s hs)

/-- The structure constant at the conjugacy class of `g` counts the corresponding
factorizations of `g`. -/
@[simp] theorem structureConstant_mk (Cᵢ Cⱼ : ConjClasses G) (g : G) :
    structureConstant Cᵢ Cⱼ (ConjClasses.mk g) =
      ((Finset.univ ×ˢ Finset.univ).filter
        fun p : Cᵢ.carrier × Cⱼ.carrier => (p.1.1 : G) * p.2.1 = g).card := by
  calc
    structureConstant Cᵢ Cⱼ (ConjClasses.mk g) =
        Fintype.card {p : Cᵢ.carrier × Cⱼ.carrier //
          (p.1.1 : G) * p.2.1 = g} := rfl
    _ = _ := Fintype.card_ofFinset _ (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)

/-- Multiplication of class sums is governed by the structure constants. -/
theorem classSum_mul (k : Type*) [Semiring k] (Cᵢ Cⱼ : ConjClasses G) :
    classSum k Cᵢ * classSum k Cⱼ =
      ∑ Cₖ : ConjClasses G, (structureConstant Cᵢ Cⱼ Cₖ : k) • classSum k Cₖ := by
  ext g
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [classSum_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, smul_eq_mul, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single, mul_one, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · rw [if_pos rfl, mul_one, structureConstant_mk]
    simpa only [Finset.sum_product] using
      (Finset.sum_boole (R := k)
        (fun p : Cᵢ.carrier × Cⱼ.carrier => (p.1.1 : G) * p.2.1 = g)
        (Finset.univ ×ˢ Finset.univ))
  · intro Cₖ _ hCₖ
    rw [if_neg hCₖ.symm, mul_zero]
  · simp

/-- **The coordinate identity**: multiplication of class sums inside the centre of the group
algebra expands in the class-sum basis with the structure constants as coefficients. This is
`TauCeti.classSum_mul` read in the centre, where the class sums are a basis. -/
theorem classSumCenter_mul (k : Type*) [CommSemiring k] (Cᵢ Cⱼ : ConjClasses G) :
    classSumCenter (k := k) Cᵢ * classSumCenter Cⱼ =
      ∑ Cₖ : ConjClasses G, (structureConstant Cᵢ Cⱼ Cₖ : k) • classSumCenter Cₖ := by
  refine Subtype.ext ?_
  push_cast [classSumCenter_coe]
  exact classSum_mul k Cᵢ Cⱼ

/-- The coefficient of `g` in a product of two class sums is the structure constant at the
conjugacy class of `g`. This is the pointwise form of `TauCeti.classSum_mul`. -/
theorem coeff_classSum_mul (k : Type*) [Semiring k] (Cᵢ Cⱼ : ConjClasses G) (g : G) :
    (classSum k Cᵢ * classSum k Cⱼ).coeff g = (structureConstant Cᵢ Cⱼ (ConjClasses.mk g) : k) := by
  rw [classSum_mul]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, classSum_coeff]
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · rw [if_pos rfl, mul_one]
  · intro Cₖ _ hCₖ
    rw [if_neg hCₖ.symm, mul_zero]
  · simp

/-- **The structure constants are symmetric in their two class arguments**, because the two class
sums commute in the group algebra. -/
theorem structureConstant_comm (Cᵢ Cⱼ Cₖ : ConjClasses G) :
    structureConstant Cᵢ Cⱼ Cₖ = structureConstant Cⱼ Cᵢ Cₖ := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep Cₖ
  have hcomm : classSum ℤ Cᵢ * classSum ℤ Cⱼ = classSum ℤ Cⱼ * classSum ℤ Cᵢ :=
    Subalgebra.mem_center_iff.mp (classSum_mem_center ℤ Cⱼ) _
  have h := congrArg (fun a : MonoidAlgebra ℤ G => a.coeff g) hcomm
  simp only [coeff_classSum_mul] at h
  exact_mod_cast h

/-- **The class of `1` is a unit for the structure constants**: because `K_{Cᵢ} · K_{[1]} = K_{Cᵢ}`,
the constant `aᵢ,[1],ₖ` is `1` when `Cₖ = Cᵢ` and `0` otherwise. -/
@[simp]
theorem structureConstant_mk_one_right (Cᵢ Cₖ : ConjClasses G) :
    structureConstant Cᵢ (ConjClasses.mk (1 : G)) Cₖ = if Cₖ = Cᵢ then 1 else 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep Cₖ
  have h := coeff_classSum_mul ℕ Cᵢ (ConjClasses.mk (1 : G)) g
  rw [classSum_mk_one, mul_one, classSum_coeff] at h
  simpa using h.symm

/-- The symmetric companion of `TauCeti.structureConstant_mk_one_right`. -/
@[simp]
theorem structureConstant_mk_one_left (Cⱼ Cₖ : ConjClasses G) :
    structureConstant (ConjClasses.mk (1 : G)) Cⱼ Cₖ = if Cₖ = Cⱼ then 1 else 0 := by
  rw [structureConstant_comm, structureConstant_mk_one_right]

end TauCeti
