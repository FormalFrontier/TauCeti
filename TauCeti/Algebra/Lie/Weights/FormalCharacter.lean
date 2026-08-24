/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import TauCeti.Algebra.Lie.Weights.Integrality
public import TauCeti.Algebra.Lie.Weights.Prod
public import TauCeti.Algebra.Lie.Weights.WeylInvariance
public import TauCeti.LinearAlgebra.Dimension.DirectSum

public section

/-!
# The formal character of a finite-dimensional Lie module

Let `L` be a nilpotent Lie algebra over a field `K` acting on a finite-dimensional module `M` with
linear weights. The **formal character** of `M` is the multiplicity function `χ ↦ dim Mχ`, recorded
as an element of the integral group algebra `ℤ[Module.Dual K L]` of the dual of `L`: it is the
generating function of the weight-space dimensions, and the object in which the Weyl character
formula is an identity.

The multiplicities are Mathlib's *generalized* weight spaces `LieModule.genWeightSpace`. Over an
algebraically closed field of characteristic zero, for the Cartan subalgebra of a Killing-semisimple
Lie algebra, these are honest simultaneous eigenspaces (`TauCeti.genWeightSpace_eq_weightSpace`), so
the coefficients really are the honest weight multiplicities; that identification is recorded
below rather than built into the definition, which needs no semisimplicity.

## The group algebra as the carrier

The carrier is `AddMonoidAlgebra ℤ (Module.Dual K L)`, the group algebra of the *whole* dual rather
than of the weight lattice. Nothing is lost: for a module over a Killing-semisimple Lie algebra
every coefficient of the character sits at an integral weight
(`TauCeti.isIntegralWeight_of_formalCharacter_coeff_ne_zero`), so the character lands in the
lattice part of the larger algebra. The convolution product of that algebra is what makes
multiplicativity on tensor products expressible.

## Main definitions

* `TauCeti.formalCharacter`: the formal character `χ ↦ dim Mχ` of a finite-dimensional module.

## Main results

* `TauCeti.formalCharacter_coeff`: its coefficients are the weight-space dimensions.
* `TauCeti.formalCharacter_congr`: isomorphic modules have the same formal character.
* `TauCeti.sum_formalCharacter_coeff_eq_finrank`: when `M` is triangularizable, the coefficients
  sum to `dim M`, and
  `TauCeti.formalCharacter_eq_zero_iff` reads off that the character vanishes only for the zero
  module.
* `TauCeti.formalCharacter_prod`: **additivity.** The character of a product of modules is the sum
  of their characters. Its weight-theoretic input is
  `TauCeti.mem_genWeightSpace_prod_iff`, that a vector lies in a generalized weight space of a
  product exactly when both components lie in the corresponding generalized weight spaces, with
  `TauCeti.genWeightSpace_prod_eq_bot_iff` and
  `TauCeti.instLinearWeightsProd` the consequences a product of modules needs to have a character
  at all.
* `TauCeti.formalCharacter_coeff_eq_finrank_weightSpace`: over an algebraically closed field of
  characteristic zero, for a Cartan subalgebra of a Killing-semisimple Lie algebra, the coefficients
  are the *honest* weight multiplicities.
* `TauCeti.isIntegralWeight_of_formalCharacter_coeff_ne_zero`: the character is supported on
  integral weights.
* `TauCeti.formalCharacter_coeff_weylGroup_smul`: **Weyl invariance** of the character.

## Implementation notes

The support of the coefficient function is finite because it is contained in the image of the
finite type `LieModule.Weight K L M` under `LieModule.Weight.toLinear`, so the coefficients are
assembled with `Finsupp.ofSupportFinite`.

Additivity is stated for the binary product `M × N` of `TauCeti/Algebra/Lie/Prod.lean` rather than
for a short exact sequence: splitting an extension is Weyl's complete reducibility theorem, which
is not available at this point of the development and whose usual proof consumes the weight theory.

## References

This is the "formal characters" item of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose target signature
`formalCharacter` is pinned in the accompanying `Suggested.lean`. Its stated prerequisite is the
Layer 2 diagonalizability theorem, which supplies the honest multiplicities, together with the
Layer 2 Weyl invariance proved directly from `sl₂`; both are consumed here.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.5.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §7.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w₁

/-! ### The formal character -/

section Defs

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [LinearWeights K L M] [FiniteDimensional K M]

omit [LinearWeights K L M] in
/-- A generalized weight space is trivial exactly when its dimension is zero. -/
private theorem genWeightSpace_eq_bot_iff_finrank_eq_zero (χ : L → K) :
    genWeightSpace M χ = ⊥ ↔ finrank K (genWeightSpace M χ) = 0 := by
  rw [← LieSubmodule.toSubmodule_eq_bot, ← Submodule.finrank_eq_zero, finrank_toSubmodule]

omit [FiniteDimensional K M] in
/-- A nonzero generalized weight space determines a bundled weight whose underlying linear form is
the given one. -/
theorem exists_weight_coe_eq {χ : Dual K L} (h : genWeightSpace M (χ : L → K) ≠ ⊥) :
    ∃ w : Weight K L M, (w : Dual K L) = χ :=
  ⟨⟨(χ : L → K), h⟩, by ext x; simp⟩

omit [FiniteDimensional K M] in
/-- Coercion of bundled linear weights to the dual is injective. -/
private theorem weight_coe_injective :
    Function.Injective fun w : Weight K L M ↦ (w : Dual K L) := fun w w' h ↦ by
  ext x
  exact LinearMap.congr_fun h x

/-- The dimensions of the generalized weight spaces of a finite-dimensional module vanish off the
image of the finite type of its weights, hence for all but finitely many linear forms. -/
private theorem finite_support_finrank_genWeightSpace :
    (Function.support
      fun χ : Dual K L ↦ (finrank K (genWeightSpace M (χ : L → K)) : ℤ)).Finite := by
  refine Set.Finite.subset (Set.finite_range fun w : Weight K L M ↦ (w : Dual K L)) fun χ hχ ↦ ?_
  rw [Function.mem_support] at hχ
  have hne : genWeightSpace M (χ : L → K) ≠ ⊥ := by
    intro h
    apply hχ
    exact_mod_cast (genWeightSpace_eq_bot_iff_finrank_eq_zero K L M χ).mp h
  exact exists_weight_coe_eq K L M hne

/-- **The formal character** of a finite-dimensional Lie module: the element of the integral group
algebra of `Module.Dual K L` whose coefficient at `χ` is the dimension of the `χ`-weight space of
`M`. -/
noncomputable def formalCharacter : AddMonoidAlgebra ℤ (Dual K L) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_finrank_genWeightSpace K L M))

variable {K L M}

/-- The coefficient of the formal character at a linear form is the dimension of the corresponding
weight space. -/
@[simp]
theorem formalCharacter_coeff (χ : Dual K L) :
    (formalCharacter K L M).coeff χ = (finrank K (genWeightSpace M (χ : L → K)) : ℤ) := by
  rw [formalCharacter, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe]

/-- The coefficients of a formal character are dimensions, hence nonnegative. -/
theorem formalCharacter_coeff_nonneg (χ : Dual K L) : 0 ≤ (formalCharacter K L M).coeff χ := by
  simp

/-- A coefficient of the formal character vanishes exactly at a linear form that is not a weight. -/
theorem formalCharacter_coeff_eq_zero_iff {χ : Dual K L} :
    (formalCharacter K L M).coeff χ = 0 ↔ genWeightSpace M (χ : L → K) = ⊥ := by
  rw [formalCharacter_coeff, Int.natCast_eq_zero,
    genWeightSpace_eq_bot_iff_finrank_eq_zero]

/-- **The formal character as a sum of basis elements.** Each bundled weight contributes its
generalized weight-space dimension at the corresponding element of the dual. -/
theorem formalCharacter_eq_sum_single :
    formalCharacter K L M =
      ∑ w : Weight K L M,
        AddMonoidAlgebra.single (w : Dual K L) (finrank K (genWeightSpace M w) : ℤ) := by
  classical
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ ↦ ?_)
  rw [formalCharacter_coeff]
  by_cases hχ : genWeightSpace M (χ : L → K) = ⊥
  · have hnone : ∀ w : Weight K L M, (w : Dual K L) ≠ χ := fun w hw ↦ by
      apply w.genWeightSpace_ne_bot
      have hfun : (w : L → K) = (χ : L → K) :=
        congrArg (fun f : Dual K L ↦ (f : L → K)) hw
      simpa only [hfun] using hχ
    rw [(genWeightSpace_eq_bot_iff_finrank_eq_zero K L M _).mp hχ]
    simp [hnone]
  · obtain ⟨w, rfl⟩ := exists_weight_coe_eq K L M hχ
    have hinj := weight_coe_injective K L M
    have hcoeff :
        (∑ c : Weight K L M,
          AddMonoidAlgebra.single (c : Dual K L)
            (finrank K (genWeightSpace M c) : ℤ)).coeff (w : Dual K L) =
          ∑ c : Weight K L M,
            (AddMonoidAlgebra.single (c : Dual K L)
              (finrank K (genWeightSpace M c) : ℤ)).coeff (w : Dual K L) := by
      simp
    rw [hcoeff, Finset.sum_eq_single w]
    · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
      exact_mod_cast congrArg (fun ψ : L → K ↦ finrank K (genWeightSpace M ψ)) Weight.coe_coe
    · intro c _ hcw
      rw [AddMonoidAlgebra.coeff_single]
      simp only [Finsupp.single_apply]
      split
      · rename_i h
        exact (hcw (hinj h)).elim
      · rfl
    · simp

/-- **The formal character is an isomorphism invariant.** An equivalence of Lie modules carries the
`χ`-weight space of one onto the `χ`-weight space of the other. -/
theorem formalCharacter_congr {N : Type w₁} [AddCommGroup N] [Module K N] [LieRingModule L N]
    [LieModule K L N] [LinearWeights K L N] [FiniteDimensional K N] (e : M ≃ₗ⁅K,L⁆ N) :
    formalCharacter K L M = formalCharacter K L N := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ ↦ ?_)
  rw [formalCharacter_coeff, formalCharacter_coeff]
  have hinj : Function.Injective ⇑(e : M →ₗ⁅K,L⁆ N) := fun _ _ h ↦ e.injective h
  have hfr := (LieSubmodule.equivMapOfInjective (f := (e : M →ₗ⁅K,L⁆ N))
    (genWeightSpace M (χ : L → K)) hinj).toLinearEquiv.finrank_eq
  rw [map_genWeightSpace_eq e] at hfr
  exact_mod_cast hfr

end Defs

/-! ### The total dimension -/

section Total

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [LinearWeights K L M] [FiniteDimensional K M] [IsTriangularizable K L M]

/-- **The coefficients of the formal character sum to the dimension of the module.** The weight
spaces are the summands of an internal direct sum decomposition
(`TauCeti.isInternal_genWeightSpace`), and the character has one coefficient for each weight. -/
theorem sum_formalCharacter_coeff_eq_finrank :
    ((formalCharacter K L M).coeff.sum fun _ n ↦ n) = (finrank K M : ℤ) := by
  classical
  have hinj := weight_coe_injective K L M
  have hsub : (formalCharacter K L M).coeff.support ⊆
      Finset.univ.image fun w : Weight K L M ↦ (w : Dual K L) := fun χ hχ ↦ by
    rw [Finsupp.mem_support_iff] at hχ
    have hne := (not_congr formalCharacter_coeff_eq_zero_iff).mp hχ
    obtain ⟨w, rfl⟩ := exists_weight_coe_eq K L M hne
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  rw [Finsupp.sum_of_support_subset _ hsub _ fun _ _ ↦ rfl,
    Finset.sum_image fun a _ b _ h ↦ hinj h,
    finrank_eq_sum_finrank_of_isInternal (isInternal_genWeightSpace K L M)]
  push_cast
  exact Finset.sum_congr rfl fun _ _ ↦ rfl

/-- **The formal character vanishes only for the zero module.** -/
@[simp]
theorem formalCharacter_eq_zero_iff : formalCharacter K L M = 0 ↔ finrank K M = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := sum_formalCharacter_coeff_eq_finrank K L M
    rw [h] at this
    simpa using this.symm
  · refine AddMonoidAlgebra.ext (Finsupp.ext fun χ ↦ ?_)
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [formalCharacter_coeff_eq_zero_iff, genWeightSpace_eq_bot_iff_finrank_eq_zero]
    exact Nat.le_zero.mp (by
      simpa [h] using Submodule.finrank_le (genWeightSpace M (χ : L → K)).toSubmodule)

end Total

/-! ### Additivity -/

section Prod

variable (K : Type u) (L : Type v) (M : Type w) (N : Type w₁) [Field K] [LieRing L]
  [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [LinearWeights K L M]
  [FiniteDimensional K M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N] [LinearWeights K L N]
  [FiniteDimensional K N]

variable {K L M N}

/-- **Additivity of the formal character.** The character of a product of two finite-dimensional
modules is the sum of their characters. -/
@[simp]
theorem formalCharacter_prod :
    formalCharacter K L (M × N) = formalCharacter K L M + formalCharacter K L N := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ ↦ ?_)
  simp

end Prod

/-! ### The Cartan subalgebra of a Killing-semisimple Lie algebra over an algebraically closed field
of characteristic zero -/

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- **The coefficients of the formal character are the honest weight multiplicities.** Over a
Cartan subalgebra of a Killing-semisimple Lie algebra the generalized weight spaces are
simultaneous eigenspaces, by `TauCeti.genWeightSpace_eq_weightSpace`. -/
theorem formalCharacter_coeff_eq_finrank_weightSpace (χ : Dual K H) :
    (formalCharacter K H M).coeff χ = (finrank K (weightSpace M (χ : H → K)) : ℤ) := by
  rw [formalCharacter_coeff, genWeightSpace_eq_weightSpace]

omit [IsAlgClosed K] in
/-- **The formal character is supported on integral weights.** A linear form carrying a nonzero
coefficient is a weight of `M`, and the weights of a finite-dimensional module are integral
(`TauCeti.isIntegralWeight_of_weight`). -/
theorem isIntegralWeight_of_formalCharacter_coeff_ne_zero [IsTriangularizable K H L] {χ : Dual K H}
    (hχ : (formalCharacter K H M).coeff χ ≠ 0) : IsIntegralWeight χ := by
  have hne := (not_congr formalCharacter_coeff_eq_zero_iff).mp hχ
  obtain ⟨w, rfl⟩ := exists_weight_coe_eq K H M hne
  exact isIntegralWeight_of_weight w

/-- **Weyl invariance of the formal character.** The multiplicity of a weight is unchanged by the
action of the Weyl group of the root system of `H`; this is
`TauCeti.finrank_weightSpace_weylGroup_smul`, proved directly from the rank-one theory and not from
Weyl's complete reducibility theorem. -/
theorem formalCharacter_coeff_weylGroup_smul (w : (IsKilling.rootSystem H).weylGroup)
    (χ : Dual K H) :
    (formalCharacter K H M).coeff (w • χ) = (formalCharacter K H M).coeff χ := by
  rw [formalCharacter_coeff_eq_finrank_weightSpace, formalCharacter_coeff_eq_finrank_weightSpace,
    finrank_weightSpace_weylGroup_smul]

end Killing

end TauCeti
