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
algorithm.
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
theorem structureConstant_mk (Cᵢ Cⱼ : ConjClasses G) (g : G) :
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
theorem classSum_mul (k : Type*) [CommRing k] (Cᵢ Cⱼ : ConjClasses G) :
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

end TauCeti
