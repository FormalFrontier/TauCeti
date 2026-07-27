/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.CharP.Basic

/-!
# A multiquadratic field is Galois

For square roots `root i` of radicands `d i ∈ K`, the multiquadratic field `M = K(rootᵢ : i)` is
the splitting field of `∏ᵢ (X² - dᵢ)`, hence normal; when `2 ≠ 0` in `K` each generator is
separable, so `M / K` is Galois. Along the way we record the basic structure shared by the later
group-theoretic analysis: every `K`-automorphism sends each generator to another element with the
same square, so it is an involution and the automorphism group is abelian.

The explicit identification of the group with `(ℤ/2)ⁿ` is a separate, later step
(`TauCeti.NumberTheory.Multiquadratic.Galois.Group`).

## Main results

* `TauCeti.Multiquadratic.isSplittingField`: `M` is the splitting field of `∏ᵢ (X² - dᵢ)`.
* `TauCeti.Multiquadratic.isGalois`: `M / K` is Galois (when `2 ≠ 0` in `K`).
* `TauCeti.Multiquadratic.aut_mul_self_eq_one`: every `σ : M ≃ₐ[K] M` satisfies `σ * σ = 1`.
* `TauCeti.Multiquadratic.aut_commute`: the automorphism group is commutative.

## Provenance

Generalised from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where these
facts were established for one concrete CM field.
-/

public section

open Polynomial IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

section SplittingField

variable [Finite ι]

/-- The defining polynomial of the multiquadratic field: `∏ᵢ (X² - dᵢ)`. -/
noncomputable def definingPolynomial (d : ι → K) : K[X] :=
  letI := Fintype.ofFinite ι
  ∏ i, (X ^ 2 - C (d i))

/-- The defining polynomial is the product of the quadratic factors `X² - dᵢ`. -/
@[simp] theorem definingPolynomial_def :
    definingPolynomial d = (letI := Fintype.ofFinite ι; ∏ i, (X ^ 2 - C (d i))) := by
  rw [definingPolynomial]

omit [Finite ι] in
/-- Each quadratic factor splits in `M`, with roots `± rootᵢ`. -/
private theorem splits_X_sq_sub_C (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    ((X ^ 2 - C (d i)).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  have hmem : root i ∈ adjoin K (Set.range root) := subset_adjoin _ _ ⟨i, rfl⟩
  have hy2 : (⟨root i, hmem⟩ : adjoin K (Set.range root)) ^ 2
      = algebraMap K (adjoin K (Set.range root)) (d i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
    exact hroot i
  have hfac : (X ^ 2 - C (d i)).map (algebraMap K (adjoin K (Set.range root)))
      = (X - C ⟨root i, hmem⟩) * (X - C (-⟨root i, hmem⟩)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hy2, map_pow, map_neg]; ring
  rw [hfac]
  exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)

/-- The `i`-th generator, as an element of the multiquadratic field `M`. -/
@[expose] noncomputable def gen (root : ι → L) (i : ι) : adjoin K (Set.range root) :=
  ⟨root i, subset_adjoin _ _ ⟨i, rfl⟩⟩

omit [Finite ι] in
/-- Coercing the `i`-th generator of `K(rootᵢ : i)` back to `L` gives `root i`. -/
@[simp] theorem coe_gen (i : ι) : (gen (K := K) root i : L) = root i := rfl

omit [Finite ι] in
/-- The generators generate `M` as its own top field. -/
theorem adjoin_gen_eq_top :
    IntermediateField.adjoin K (Set.range (gen (K := K) root)) = ⊤ := by
  refine IntermediateField.map_injective (adjoin K (Set.range root)).val ?_
  have hmaptop : (⊤ : IntermediateField K (adjoin K (Set.range root))).map
      (adjoin K (Set.range root)).val = adjoin K (Set.range root) := by
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [IntermediateField.adjoin_map, hmaptop]
  congr 1
  rw [← Set.range_comp]
  rfl

omit [Finite ι] in
/-- The generator squares to its radicand (in `M`). -/
@[simp] theorem gen_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    gen (K := K) root i ^ 2 = algebraMap K (adjoin K (Set.range root)) (d i) := by
  apply Subtype.ext
  rw [IntermediateField.coe_pow, coe_gen, IntermediateField.coe_algebraMap_apply]
  exact hroot i

omit [Finite ι] in
/-- Every automorphism sends a generator to itself or to its negation. -/
theorem aut_gen_eq_self_or_eq_neg (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = gen root i ∨ σ (gen root i) = -gen root i := by
  have h1 : (σ (gen root i)) ^ 2 = (gen root i) ^ 2 := by
    rw [← map_pow, gen_sq hroot, AlgEquiv.commutes, ← gen_sq hroot]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h1

omit [Finite ι] in
/-- A generator is not equal to its own negation when the radicand is nonzero, since `2 ≠ 0` in
`L` (via `Ring.eq_self_iff_eq_zero_of_char_ne_two`). -/
theorem gen_ne_neg [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (i : ι) (hd : d i ≠ 0) :
    gen (K := K) root i ≠ -gen root i := by
  intro h
  have hcoe : root i = -root i := by simpa using congrArg Subtype.val h
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr two_ne_zero
  have hr0 : root i ≠ 0 := fun hx0 =>
    hd ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mp
      (by rw [← hroot i, hx0]; ring))
  have hchar : ringChar L ≠ 2 := fun hc =>
    h2L (by exact_mod_cast (ringChar.spec L 2).2 (by simp [hc]))
  exact hr0 ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp hcoe.symm)

/-- `∏ᵢ (X² - dᵢ)` is nonzero. -/
private theorem definingPolynomial_ne_zero : definingPolynomial d ≠ 0 := by
  rw [definingPolynomial, Finset.prod_ne_zero_iff]
  exact fun i _ => Polynomial.X_pow_sub_C_ne_zero (by norm_num) (d i)

/-- The defining polynomial splits over `M`. -/
private theorem splits_definingPolynomial (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    ((definingPolynomial d).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  rw [definingPolynomial, Polynomial.map_prod]
  exact Polynomial.Splits.prod fun i _ => splits_X_sq_sub_C hroot i

omit [Finite ι] in
/-- Each generator is algebraic over `K` (it satisfies `X² - dᵢ`). -/
private theorem isAlgebraic_gen (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    IsAlgebraic K (gen (K := K) root i) :=
  ⟨X ^ 2 - C (d i), X_pow_sub_C_ne_zero (by norm_num) _, by
    rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self]⟩

/-- `M = K(rootᵢ : i)` is the splitting field of `∏ᵢ (X² - dᵢ)` over `K`. -/
theorem isSplittingField (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    (definingPolynomial d).IsSplittingField K (adjoin K (Set.range root)) where
  splits' := splits_definingPolynomial hroot
  adjoin_rootSet' := by
    letI := Fintype.ofFinite ι
    have hsub : Set.range (gen (K := K) root) ⊆
        (definingPolynomial d).rootSet (adjoin K (Set.range root)) := by
      rintro _ ⟨i, rfl⟩
      rw [Polynomial.mem_rootSet]
      refine ⟨definingPolynomial_ne_zero, ?_⟩
      rw [definingPolynomial, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self])
    have halg : ∀ x ∈ Set.range (gen (K := K) root), IsAlgebraic K x := by
      rintro _ ⟨i, rfl⟩; exact isAlgebraic_gen hroot i
    refine le_antisymm le_top ?_
    rw [← Algebra.adjoin_eq_top_of_intermediateField halg (adjoin_gen_eq_top (root := root))]
    exact Algebra.adjoin_mono hsub

/-- A multiquadratic field over a field in which `2 ≠ 0` is Galois: it is the splitting field of
`∏ᵢ (X² - dᵢ)` (hence normal), and each generator satisfies a separable quadratic. -/
theorem isGalois [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    IsGalois K (adjoin K (Set.range root)) := by
  haveI := isSplittingField hroot
  haveI : Normal K (adjoin K (Set.range root)) := Normal.of_isSplittingField (definingPolynomial d)
  haveI : Algebra.IsSeparable K (adjoin K (Set.range root)) := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨i, rfl⟩
    -- `root i` is a root of `X² - dᵢ`; this is separable when `dᵢ ≠ 0` (as `2 ≠ 0`), and when
    -- `dᵢ = 0` the generator is `0`, a root of the separable polynomial `X`.
    have haeval : aeval (root i) (X ^ 2 - C (d i)) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, hroot i, sub_self]
    by_cases hd : d i = 0
    · have hr0 : root i = 0 := by
        have hz : root i ^ 2 = 0 := by rw [hroot i, hd, map_zero]
        exact pow_eq_zero_iff (by norm_num) |>.mp hz
      exact separable_X.of_dvd (minpoly.dvd K (root i) (by rw [aeval_X, hr0]))
    · exact (separable_X_pow_sub_C (d i) (by exact_mod_cast two_ne_zero) hd).of_dvd
        (minpoly.dvd K (root i) haeval)
  constructor

end SplittingField

/-- Every `K`-automorphism of the multiquadratic field `K(rootᵢ : i)` is an involution: fixing
`K` forces the image of each generator to have the same square as the generator, so applying the
automorphism twice fixes the generators. -/
@[simp]
theorem aut_mul_self_eq_one (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : IntermediateField.adjoin K (Set.range root) ≃ₐ[K]
      IntermediateField.adjoin K (Set.range root)) :
    σ * σ = 1 := by
  refine AlgEquiv.coe_toAlgHom_injective ?_
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := K)
    (S := IntermediateField.adjoin K (Set.range root)) (s := Set.range root) rfl ?_
  rintro x ⟨i, rfl⟩
  -- The extensionality goal `↑(σ * σ) ⟨root i, _⟩ = ⟨root i, _⟩` is definitionally the generator
  -- equation below: `gen root i := ⟨root i, _⟩`, and `↑(σ * σ) ·` reduces to `σ (σ ·)`. We convert
  -- to that readable form so the `aut_gen_eq_self_or_eq_neg` case split can fire on `gen root i`.
  change σ (σ (gen root i)) = gen root i
  rcases aut_gen_eq_self_or_eq_neg hroot σ i with h | h <;> simp [h, map_neg]

/-- The automorphism group of a multiquadratic field is commutative: every element has order
dividing two, so any two commute. -/
theorem aut_commute (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (a b : IntermediateField.adjoin K (Set.range root) ≃ₐ[K]
      IntermediateField.adjoin K (Set.range root)) :
    Commute a b :=
  Commute.of_orderOf_dvd_two
    (fun σ => orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact aut_mul_self_eq_one hroot σ)) a b

end TauCeti.Multiquadratic
