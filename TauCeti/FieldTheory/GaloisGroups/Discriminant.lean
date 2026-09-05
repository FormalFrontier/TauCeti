/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The square root of the discriminant, and the test for the alternating group

Let `f` be a monic separable polynomial over a field `F`, and let `E` be an extension in which
`f` splits. Numbering the roots of `f` in `E` by an equivalence `e : Fin f.natDegree ≃ f.rootSet E`
turns the product of the root differences

`δ = ∏_{i < j} (rᵢ - rⱼ)`

into an element of `E`. Its square is the image of `Polynomial.discr f`, so `δ` is a square root
of the discriminant; it is only *a* square root, because a different numbering changes `δ` by the
sign of the permutation relating the two numberings.

That sign is the whole point. In a finite-dimensional Galois splitting extension, a field
automorphism of `E` over `F` permutes the roots, hence multiplies `δ` by the sign of the
permutation it induces. When `ringChar F ≠ 2`, consequently `δ` lies in `F` exactly when the
Galois image consists of even permutations, and — since `δ² = discr f` — that happens exactly
when `discr f` is a square in `F`. This is the **discriminant test** for containment in the
alternating group.

The characteristic hypothesis `ringChar F ≠ 2` is not decoration. In characteristic `2` one has
`-1 = 1`, so the sign never moves `δ`, the discriminant of a separable monic polynomial is
*always* a square, and the test decides nothing; this is recorded as
`Polynomial.Monic.isSquare_discr_of_char_two`.

## Main definitions

* `TauCeti.discrSqrt`: the product of the differences of the roots of `f` in `E`, taken over the
  pairs `i < j` of a numbering of the root set.

## Main results

* `Polynomial.Monic.discrSqrt_sq`: `discrSqrt e ^ 2` is the image of `Polynomial.discr f` in `E`.
* `TauCeti.discrSqrt_trans`: renumbering the roots by `π` multiplies `discrSqrt` by `sign π`.
* `AlgEquiv.map_discrSqrt`: an automorphism of `E` over `F` multiplies `discrSqrt e` by the sign of
  the permutation of the roots that it induces.
* `Polynomial.Monic.isSquare_discr_iff_mem_range`: `discr f` is a square in `F` exactly when
  `discrSqrt e` comes from `F`.
* `Polynomial.Monic.isSquare_discr_iff_range_le_alternatingGroup`: **the discriminant test**,
  valid away from characteristic `2`.
* `Polynomial.Monic.isSquare_discr_of_char_two`: in characteristic `2` the discriminant of a monic
  separable polynomial is always a square, so the test is vacuous there.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial

namespace TauCeti

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {f : F[X]}

/-! ## The discriminant test -/

section Galois

variable [Fact ((f.map (algebraMap F E)).Splits)]

open scoped Classical in
/-- **The transformation law for the square root of the discriminant.** An automorphism `ϕ` of a
splitting extension `E` over `F` multiplies the product of the root differences by the sign of the
permutation that `ϕ` induces on the roots of `f`. -/
theorem _root_.AlgEquiv.map_discrSqrt (ϕ : E ≃ₐ[F] E) (e : Fin f.natDegree ≃ f.rootSet E) :
    ϕ (discrSqrt e) =
      Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)) • discrSqrt e := by
  -- Transport the induced permutation of the root set to a permutation of `Fin f.natDegree`
  -- along the numbering; the sign is unchanged, and `TauCeti.discrSqrt_trans` applies.
  obtain ⟨ρ, hcongr⟩ : ∃ ρ : Equiv.Perm (Fin f.natDegree),
      e.permCongr ρ = Gal.galActionHom f E (Gal.restrict f E ϕ) :=
    ⟨e.permCongr.symm _, Equiv.apply_symm_apply _ _⟩
  have key : ∀ i, ϕ ((e i : E)) = ((e (ρ i) : E)) := fun i ↦ by
    have h : Gal.galActionHom f E (Gal.restrict f E ϕ) (e i) = e (ρ i) := by
      rw [← hcongr]; simp
    rw [← Gal.restrict_smul ϕ (e i)]
    exact congrArg Subtype.val h
  have himage : ϕ (discrSqrt e)
      = ∏ i, ∏ j ∈ Finset.Ioi i, ((e (ρ i) : E) - (e (ρ j) : E)) := by
    simp only [discrSqrt_def, map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact Finset.prod_congr rfl fun j _ ↦ by rw [map_sub, key, key]
  have hrenumber : discrSqrt (ρ.trans e)
      = ∏ i, ∏ j ∈ Finset.Ioi i, ((e (ρ i) : E) - (e (ρ j) : E)) := by
    simp only [discrSqrt_def, Equiv.trans_apply]
  rw [himage, ← hrenumber, discrSqrt_trans, ← Equiv.Perm.sign_permCongr e ρ, hcongr]

open scoped Classical in
/-- Away from characteristic `2`, the product of the root differences comes from the base field
exactly when the Galois image consists of even permutations of the roots. -/
theorem _root_.Polynomial.Monic.discrSqrt_mem_range_iff [FiniteDimensional F E] [IsGalois F E]
    (hf : f.Monic) (hsep : f.Separable) (hchar : ringChar F ≠ 2)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e ∈ Set.range (algebraMap F E) ↔
      (Gal.galActionHom f E).range ≤ alternatingGroup (f.rootSet E) := by
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr (Ring.two_ne_zero hchar)
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · rintro hfix g ⟨σ, rfl⟩
    obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective f E σ
    rw [Equiv.Perm.mem_alternatingGroup]
    have hϕ := hfix ϕ
    rw [AlgEquiv.map_discrSqrt] at hϕ
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)))
      with h1 | h1
    · exact h1
    -- An odd permutation would negate a nonzero element and fix it, forcing `2 = 0` in `E`.
    rw [h1] at hϕ
    refine absurd ?_ (hf.discrSqrt_ne_zero hsep e)
    have hdouble : (2 : E) * discrSqrt e = 0 := by
      simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul] at hϕ
      linear_combination -hϕ
    exact (mul_eq_zero.mp hdouble).resolve_left h2
  · intro hle ϕ
    rw [AlgEquiv.map_discrSqrt, Equiv.Perm.mem_alternatingGroup.mp (hle ⟨_, rfl⟩), one_smul]

open scoped Classical in
/-- **The discriminant test.** For a monic separable polynomial over a field of characteristic
other than `2`, the discriminant is a square in the base field exactly when the Galois group acts
on the roots by even permutations.

The characteristic hypothesis cannot be dropped: see
`Polynomial.Monic.isSquare_discr_of_char_two`. -/
theorem _root_.Polynomial.Monic.isSquare_discr_iff_range_le_alternatingGroup
    [FiniteDimensional F E] [IsGalois F E] (hf : f.Monic) (hsep : f.Separable)
    (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ (Gal.galActionHom f E).range ≤ alternatingGroup (f.rootSet E) := by
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  exact (hf.isSquare_discr_iff_mem_range hsep e).trans (hf.discrSqrt_mem_range_iff hsep hchar e)

/-- In characteristic `2` the discriminant of a monic separable polynomial is always a square,
whatever its Galois group: the sign of a permutation acts trivially because `-1 = 1`, so the
product of the root differences is fixed by the whole Galois group and therefore lies in the base
field.

This is why the discriminant test carries the hypothesis `ringChar F ≠ 2`. The invariant that
replaces the discriminant in characteristic `2` is Berlekamp's. -/
theorem _root_.Polynomial.Monic.isSquare_discr_of_char_two (hf : f.Monic) (hsep : f.Separable)
    (hchar : ringChar F = 2) : IsSquare f.discr := by
  classical
  let E := f.SplittingField
  let _ : IsGalois F E := IsGalois.of_separable_splitting_field hsep
  let _ : Fact ((f.map (algebraMap F E)).Splits) := ⟨IsSplittingField.splits E f⟩
  have hF : (2 : F) = 0 := by
    exact_mod_cast (ringChar.spec F 2).mpr (by rw [hchar])
  have h2 : (2 : E) = 0 := by rw [← map_ofNat (algebraMap F E) 2, hF, map_zero]
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  rw [hf.isSquare_discr_iff_mem_range hsep e, IsGalois.mem_range_algebraMap_iff_fixed]
  intro ϕ
  rw [AlgEquiv.map_discrSqrt]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)))
    with h1 | h1 <;> rw [h1]
  · rw [one_smul]
  · simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
    linear_combination -h2 * discrSqrt e

end Galois

end TauCeti
