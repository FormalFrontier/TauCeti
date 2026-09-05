/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.Perm.Fin
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

That sign is the whole point. A field automorphism of `E` over `F` permutes the roots, hence
multiplies `δ` by the sign of the permutation it induces. Consequently `δ` lies in `F` exactly
when the Galois image consists of even permutations, and — since `δ² = discr f` — that happens
exactly when `discr f` is a square in `F`. This is the **discriminant test** for containment in
the alternating group.

The characteristic hypothesis `ringChar F ≠ 2` is not decoration. In characteristic `2` one has
`-1 = 1`, so the sign never moves `δ`, the discriminant of a separable monic polynomial is
*always* a square, and the test decides nothing; this is recorded as
`TauCeti.isSquare_discr_of_ringChar_eq_two`.

## Main definitions

* `TauCeti.discrSqrt`: the product of the differences of the roots of `f` in `E`, taken over the
  pairs `i < j` of a numbering of the root set.

## Main results

* `TauCeti.discrSqrt_sq`: `discrSqrt e ^ 2` is the image of `Polynomial.discr f` in `E`.
* `TauCeti.discrSqrt_trans`: renumbering the roots by `π` multiplies `discrSqrt` by `sign π`.
* `TauCeti.map_discrSqrt`: an automorphism of `E` over `F` multiplies `discrSqrt e` by the sign of
  the permutation of the roots that it induces.
* `TauCeti.isSquare_discr_iff_mem_range`: `discr f` is a square in `F` exactly when `discrSqrt e`
  comes from `F`.
* `TauCeti.isSquare_discr_iff_range_le_alternatingGroup`: **the discriminant test**, valid away
  from characteristic `2`.
* `TauCeti.isSquare_discr_of_ringChar_eq_two`: in characteristic `2` the discriminant of a monic
  separable polynomial is always a square, so the test is vacuous there.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial

namespace TauCeti

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {f : F[X]}

/-! ## Numbering the roots -/

-- Membership in the root set is membership in the root multiset of the mapped polynomial.
private theorem mem_roots_map_iff {a : E} :
    a ∈ (f.map (algebraMap F E)).roots ↔ a ∈ f.rootSet E :=
  Polynomial.mem_aroots'.trans Polynomial.mem_rootSet'.symm

/-- A numbering of the root set of a separable polynomial enumerates the whole root multiset:
separability makes the roots simple, so the multiset is the image of the numbering. This is the
hypothesis that the root-product formula for the discriminant takes. -/
theorem roots_map_eq_map_numbering (hsep : f.Separable) (e : Fin f.natDegree ≃ f.rootSet E) :
    (f.map (algebraMap F E)).roots = Multiset.map (fun i ↦ ((e i : E))) Finset.univ.val := by
  refine (Multiset.Nodup.ext (nodup_roots hsep.map) ?_).mpr ?_
  · exact Finset.univ.nodup.map fun i j h ↦ e.injective (Subtype.ext h)
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    exact ⟨fun ha ↦ ⟨e.symm ⟨a, mem_roots_map_iff.mp ha⟩, by simp⟩,
      fun ⟨i, hi⟩ ↦ hi ▸ mem_roots_map_iff.mpr (e i).2⟩

/-! ## The square root of the discriminant -/

/-- The product `∏_{i < j} (rᵢ - rⱼ)` of the differences of the roots of `f` in `E`, taken along a
numbering `e` of the root set.

For monic separable `f` this is a square root of the discriminant, by `TauCeti.discrSqrt_sq`. It
is only *a* square root: `TauCeti.discrSqrt_trans` shows that changing the numbering by an odd
permutation changes the sign. The root set carries no order, so the numbering is an explicit
argument and is never fixed globally. -/
def discrSqrt (e : Fin f.natDegree ≃ f.rootSet E) : E :=
  ∏ i, ∏ j ∈ Finset.Ioi i, ((e i : E) - (e j : E))

/-- The defining equation of `TauCeti.discrSqrt`. -/
theorem discrSqrt_def (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e = ∏ i, ∏ j ∈ Finset.Ioi i, ((e i : E) - (e j : E)) := (rfl)

/-- The defining property: the square of the product of the root differences is the discriminant.
-/
theorem discrSqrt_sq (hf : f.Monic) (hsep : f.Separable) (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e ^ 2 = algebraMap F E f.discr := by
  rw [hf.discr_eq_prod_roots_sub_sq (roots_map_eq_map_numbering hsep e), discrSqrt_def,
    ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ (Finset.prod_pow _ _ _).symm

/-- A separable monic polynomial has nonzero discriminant, so the product of its root differences
is nonzero. -/
theorem discrSqrt_ne_zero (hf : f.Monic) (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) : discrSqrt e ≠ 0 := by
  intro h
  have h0 : algebraMap F E f.discr = 0 := by rw [← discrSqrt_sq hf hsep e, h, zero_pow two_ne_zero]
  exact (hf.discr_ne_zero_iff.mpr hsep)
    ((map_eq_zero_iff _ (algebraMap F E).injective).mp h0)

/-- Renumbering the roots by a permutation `π` multiplies the product of the root differences by
the sign of `π`. This is the alternating behaviour that makes the discriminant test work. -/
theorem discrSqrt_trans (e : Fin f.natDegree ≃ f.rootSet E) (π : Equiv.Perm (Fin f.natDegree)) :
    discrSqrt (π.trans e) = Equiv.Perm.sign π • discrSqrt e := by
  have h := π.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j ↦ ((e i : E) - (e j : E))) fun i j ↦ (neg_sub _ _).symm
  simp only [discrSqrt_def, Equiv.trans_apply, h, Units.smul_def, zsmul_eq_mul]

/-- The discriminant is a square in the base field exactly when the product of the root
differences already comes from the base field. No Galois hypothesis is involved: this is the
elementary half of the discriminant test, and it is the reading of `TauCeti.discrSqrt_sq` in both
directions. -/
theorem isSquare_discr_iff_mem_range (hf : f.Monic) (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    IsSquare f.discr ↔ discrSqrt e ∈ Set.range (algebraMap F E) := by
  constructor
  · rintro ⟨c, hc⟩
    have hsq : discrSqrt e * discrSqrt e = algebraMap F E c * algebraMap F E c := by
      rw [← map_mul, ← hc, ← sq, discrSqrt_sq hf hsep]
    rcases mul_self_eq_mul_self_iff.mp hsq with h | h
    · exact ⟨c, h.symm⟩
    · exact ⟨-c, by rw [map_neg, ← h]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, (algebraMap F E).injective ?_⟩
    rw [map_mul, hc, ← sq, discrSqrt_sq hf hsep]

/-! ## The discriminant test -/

section Galois

variable [DecidableEq E] [Fact ((f.map (algebraMap F E)).Splits)]

/-- **The transformation law for the square root of the discriminant.** An automorphism `ϕ` of a
splitting extension `E` over `F` multiplies the product of the root differences by the sign of the
permutation that `ϕ` induces on the roots of `f`. -/
theorem map_discrSqrt (ϕ : E ≃ₐ[F] E) (e : Fin f.natDegree ≃ f.rootSet E) :
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
    rw [discrSqrt_def, map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [map_sub, key, key]
  have hrenumber : discrSqrt (ρ.trans e)
      = ∏ i, ∏ j ∈ Finset.Ioi i, ((e (ρ i) : E) - (e (ρ j) : E)) := by
    rw [discrSqrt_def]
    simp only [Equiv.trans_apply]
  rw [himage, ← hrenumber, discrSqrt_trans, ← Equiv.Perm.sign_permCongr e ρ, hcongr]

/-- Away from characteristic `2`, the product of the root differences comes from the base field
exactly when the Galois image consists of even permutations of the roots. -/
theorem discrSqrt_mem_range_iff [FiniteDimensional F E] [IsGalois F E] (hf : f.Monic)
    (hsep : f.Separable) (hchar : ringChar F ≠ 2) (e : Fin f.natDegree ≃ f.rootSet E) :
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
    rw [map_discrSqrt] at hϕ
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)))
      with h1 | h1
    · exact h1
    -- An odd permutation would negate a nonzero element and fix it, forcing `2 = 0` in `E`.
    rw [h1] at hϕ
    refine absurd ?_ (discrSqrt_ne_zero hf hsep e)
    have hdouble : (2 : E) * discrSqrt e = 0 := by
      simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul] at hϕ
      linear_combination -hϕ
    exact (mul_eq_zero.mp hdouble).resolve_left h2
  · intro hle ϕ
    rw [map_discrSqrt, Equiv.Perm.mem_alternatingGroup.mp (hle ⟨_, rfl⟩), one_smul]

/-- **The discriminant test.** For a monic separable polynomial over a field of characteristic
other than `2`, the discriminant is a square in the base field exactly when the Galois group acts
on the roots by even permutations.

The characteristic hypothesis cannot be dropped: see
`TauCeti.isSquare_discr_of_ringChar_eq_two`. -/
theorem isSquare_discr_iff_range_le_alternatingGroup [FiniteDimensional F E] [IsGalois F E]
    (hf : f.Monic) (hsep : f.Separable) (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ (Gal.galActionHom f E).range ≤ alternatingGroup (f.rootSet E) := by
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  exact (isSquare_discr_iff_mem_range hf hsep e).trans (discrSqrt_mem_range_iff hf hsep hchar e)

/-- The discriminant test, read on the elements of the Galois group: away from characteristic `2`
the discriminant is a square exactly when every element of the Galois group acts on the roots by
an even permutation. -/
theorem isSquare_discr_iff_forall_sign_eq_one [FiniteDimensional F E] [IsGalois F E]
    (hf : f.Monic) (hsep : f.Separable) (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ ∀ σ : f.Gal, Equiv.Perm.sign (Gal.galActionHom f E σ) = 1 := by
  rw [isSquare_discr_iff_range_le_alternatingGroup (E := E) hf hsep hchar]
  refine ⟨fun h σ ↦ Equiv.Perm.mem_alternatingGroup.mp (h ⟨σ, rfl⟩), fun h g hg ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := hg
  exact Equiv.Perm.mem_alternatingGroup.mpr (h σ)

omit [DecidableEq E] in
/-- In characteristic `2` the discriminant of a monic separable polynomial is always a square,
whatever its Galois group: the sign of a permutation acts trivially because `-1 = 1`, so the
product of the root differences is fixed by the whole Galois group and therefore lies in the base
field.

This is why the discriminant test carries the hypothesis `ringChar F ≠ 2`. The invariant that
replaces the discriminant in characteristic `2` is Berlekamp's. -/
theorem isSquare_discr_of_ringChar_eq_two [FiniteDimensional F E] [IsGalois F E] (hf : f.Monic)
    (hsep : f.Separable) (hchar : ringChar F = 2) : IsSquare f.discr := by
  classical
  have hF : (2 : F) = 0 := by
    exact_mod_cast (ringChar.spec F 2).mpr (by rw [hchar])
  have h2 : (2 : E) = 0 := by rw [← map_ofNat (algebraMap F E) 2, hF, map_zero]
  obtain ⟨e⟩ : Nonempty (Fin f.natDegree ≃ f.rootSet E) :=
    ⟨(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hsep Fact.out)).symm⟩
  rw [isSquare_discr_iff_mem_range hf hsep e, IsGalois.mem_range_algebraMap_iff_fixed]
  intro ϕ
  rw [map_discrSqrt]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom f E (Gal.restrict f E ϕ)))
    with h1 | h1 <;> rw [h1]
  · rw [one_smul]
  · simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
    linear_combination -h2 * discrSqrt e

end Galois

end TauCeti
