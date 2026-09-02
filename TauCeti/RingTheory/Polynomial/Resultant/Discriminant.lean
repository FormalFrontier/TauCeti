/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The discriminant of a polynomial as a product over pairs of roots

Mathlib defines `Polynomial.discr f` as the determinant of `f.sylvesterDeriv`, corrected by the
sign `(-1) ^ (n * (n - 1) / 2)` with `n = f.natDegree`. The division-free relation is that the
resultant of `f` and `f.derivative` equals this sign times `f.leadingCoeff * f.discr`
(`Polynomial.resultant_deriv`). What that definition does not say is what the discriminant
measures. This file proves the classical root-product formula

`(∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2`

for a family of roots `r : Fin n → R` over an arbitrary commutative ring, together with the
consequences that read the formula: base change, and the criterion for a monic polynomial to be
separable.

## Main results

* `Polynomial.discr_prod_X_sub_C`, `Polynomial.discr_prod_X_sub_C_eq_sq`: the root-product
  formula, in its squared-product form and in the form `discr = δ ^ 2` for the Vandermonde-like
  product `δ = ∏_{i < j} (rᵢ - rⱼ)`. The second is the shape the discriminant test for
  containment in the alternating group is stated with, since a Galois automorphism permutes the
  roots and multiplies `δ` by the sign of that permutation.
* `Polynomial.Monic.discr_eq_prod_roots_sub_sq`: the same formula for a monic polynomial that
  splits after base change, written against a numbering of its root multiset.
* `Polynomial.Monic.prod_roots_eval_derivative`: the product of the derivative over the root
  multiset, which is the discriminant up to the same sign. This is the shape in which the
  discriminant of a minimal polynomial is a norm.
* `Polynomial.Monic.discr_mul`: the product formula for discriminants, with the square of the
  resultant as its cross term.
* `Polynomial.discr_map_of_natDegree_eq`, `Polynomial.Monic.discr_map`: base change whenever the
  degree is preserved, with monicity as a convenient sufficient condition.
* `Polynomial.Monic.isUnit_discr_iff`, `Polynomial.Monic.discr_ne_zero_iff`,
  `Polynomial.Monic.discr_ne_zero_iff_separable_map`: a monic polynomial is separable exactly
  when its discriminant is a unit; over a field that reads `discr f ≠ 0`, and over a domain the
  correct statement passes to the fraction field.
* `Cubic.discr_toPoly`: the two discriminants of a cubic with nonzero leading coefficient agree,
  so that `Cubic.discr` and `Polynomial.discr` may be used interchangeably in degree three.
* `Algebra.discr_powerBasis_eq_minpoly_discr`: the algebra discriminant of a power basis agrees
  with the polynomial discriminant of the minimal polynomial of its generator.

## Implementation notes

The root-product formula is a universal polynomial identity, and it is proved as one. The work
happens over an integral domain, where `Polynomial.resultant_eq_prod_eval` evaluates the
resultant of `f` and `f.derivative` as a product over the roots of `f`; the general case is then
the image of the identity over `MvPolynomial (Fin n) ℤ`, which is a domain, under the ring
morphism sending the `i`-th variable to `r i`. Base change along that morphism is legitimate
precisely because `∏ i, (X - C (X i))` is monic.

The separability criterion is *not* a universal identity, and the failure is recorded here:
`Polynomial.not_separable_X_pow_two_sub_one` shows that `X ^ 2 - 1` over `ℤ` has nonzero
discriminant `4` and is not `Polynomial.Separable`. Over a domain the criterion must therefore
be read in the fraction field, and that is the form every use over `ℤ` takes.

The sign bookkeeping — folding the off-diagonal product over ordered pairs into a product over
unordered pairs, and evaluating `∑ i, #(Ioi i)` as `n * (n - 1) / 2` — follows the corresponding
step of `Algebra.discr_powerBasis_eq_prod''` in `Mathlib/RingTheory/Discriminant.lean`, and
reuses the same lemma `Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag`. No Mathlib code is
vendored.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §3.3.2 and §6.3.
* S. Lang, *Algebra*, third edition, Chapter IV, §8.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a monic polynomial, the resultant of `f` and `f.derivative`, taken at the degree bounds
`f.natDegree` and `f.natDegree - 1` that the Sylvester matrix of the discriminant uses, is the
discriminant up to the sign `(-1) ^ (n * (n - 1) / 2)`.

This is `Polynomial.resultant_deriv` with the leading coefficient removed, extended to the
constant polynomial `1`, which that lemma excludes. -/
theorem _root_.Polynomial.Monic.resultant_derivative {f : R[X]} (hf : f.Monic) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with h | h
  · obtain rfl := eq_one_of_monic_natDegree_zero hf h
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  · rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp h), hf.leadingCoeff, mul_one]

/-- For monic `f`, `f.resultant g` does not depend on which valid upper bound is supplied for the
degree of `g`. -/
private theorem Polynomial.Monic.resultant_of_le {f g : R[X]} (hf : f.Monic) {n : ℕ}
    (hn : g.natDegree ≤ n) : f.resultant g f.natDegree n = f.resultant g := by
  have hn' : n = g.natDegree + (n - g.natDegree) :=
    (Nat.add_sub_cancel' hn).symm
  conv_lhs => rw [hn']
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree, hf.leadingCoeff, one_pow, one_mul]

private theorem Polynomial.sylvesterDeriv_map_reindex {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    Matrix.reindex (finCongr (by rw [hdeg])) (finCongr (by rw [hdeg]))
      (f.map φ).sylvesterDeriv = φ.mapMatrix f.sylvesterDeriv := by
  classical
  let e : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree) ≃
      Fin (f.natDegree - 1 + f.natDegree) := finCongr (by rw [hdeg])
  change Matrix.reindex e e (f.map φ).sylvesterDeriv = φ.mapMatrix f.sylvesterDeriv
  ext i j
  simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, sylvesterDeriv, hdeg]
  by_cases hzero : f.natDegree = 0
  · simp [hzero]
  · simp only [hzero, ↓reduceDIte]
    by_cases hi : (i : ℕ) = 2 * f.natDegree - 2
    · by_cases hj₁ : (j : ℕ) = f.natDegree - 2
      · simp [Matrix.updateRow_apply, Fin.ext_iff, hi, hj₁]
      · by_cases hj₂ : (j : ℕ) = 2 * f.natDegree - 2
        · simp [Matrix.updateRow_apply, Fin.ext_iff, hi, hj₂]
          split_ifs <;> simp
        · simp [Matrix.updateRow_apply, Fin.ext_iff, hi, hj₁, hj₂]
    · simp only [Matrix.updateRow_apply, Fin.ext_iff, hi, ite_false]
      induction j using Fin.addCases with
      | left j =>
          let j' : Fin ((f.map φ).natDegree - 1) :=
            Fin.cast (congrArg (· - 1) hdeg.symm) j
          have hj : e.symm (Fin.castAdd f.natDegree j) =
              Fin.castAdd (f.map φ).natDegree j' := by
            apply Fin.ext
            rfl
          rw [hj]
          simp [j', hdeg, hi, sylvester, derivative_map]
          split_ifs <;> simp
      | right j =>
          let j' : Fin (f.map φ).natDegree := Fin.cast hdeg.symm j
          have hj : e.symm (Fin.natAdd (f.natDegree - 1) j) =
              Fin.natAdd ((f.map φ).natDegree - 1) j' := by
            apply Fin.ext
            simp [e, j', hdeg]
          rw [hj]
          simp [j', hdeg, hi, sylvester, derivative_map]
          split_ifs <;> simp

/-- Base change of the discriminant along a ring morphism that preserves the degree. -/
theorem _root_.Polynomial.discr_map_of_natDegree_eq {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  classical
  simp only [discr, hdeg, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [RingHom.map_det]
  let e : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree) ≃
      Fin (f.natDegree - 1 + f.natDegree) := finCongr (by rw [hdeg])
  rw [← Matrix.det_reindex_self e]
  congr 1
  exact Polynomial.sylvesterDeriv_map_reindex φ hdeg

/-- Base change of the discriminant along a ring morphism, for a monic polynomial. Monicity
ensures that the degree is preserved. -/
@[simp]
theorem _root_.Polynomial.Monic.discr_map {f : R[X]} (hf : f.Monic) (φ : R →+* S) :
    (f.map φ).discr = φ f.discr := by
  nontriviality S
  exact Polynomial.discr_map_of_natDegree_eq φ (hf.natDegree_map φ)

private theorem triangle_add (m n : ℕ) :
    (m + n) * (m + n - 1) / 2 =
      m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, Nat.triangle_succ, Nat.triangle_succ, ih]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The discriminant of a product of monic polynomials is the product of their discriminants and
the square of their resultant. -/
theorem _root_.Polynomial.Monic.discr_mul {f g : R[X]} (hf : f.Monic) (hg : g.Monic) :
    (f * g).discr = f.discr * g.discr * (f.resultant g) ^ 2 := by
  by_cases hf0 : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hf0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  by_cases hg0 : g.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hg hg0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  let d := f.natDegree + g.natDegree - 1
  have hdeg : (f * g).natDegree = f.natDegree + g.natDegree := hf.natDegree_mul hg
  have hderiv : (f * g).derivative.natDegree ≤ d := by
    dsimp only [d]
    rw [← hdeg]
    exact natDegree_derivative_le _
  have hpf : g.derivative.natDegree + f.natDegree ≤ d := by
    have := natDegree_derivative_le g
    dsimp only [d]
    omega
  have hpg : f.derivative.natDegree + g.natDegree ≤ d := by
    have := natDegree_derivative_le f
    dsimp only [d]
    omega
  have hpf' : f.natDegree + g.derivative.natDegree ≤ d := by omega
  have hmul_f : (f.derivative * g).natDegree ≤ d := natDegree_mul_le.trans hpg
  have hmul_g : (f * g.derivative).natDegree ≤ d := natDegree_mul_le.trans hpf'
  have hresf : f.resultant (f * g).derivative f.natDegree d =
      f.resultant f.derivative * f.resultant g := by
    rw [derivative_mul, resultant_add_mul_right _ _ _ _ _ hpf le_rfl,
      Polynomial.Monic.resultant_of_le hf hmul_f,
      ← Polynomial.Monic.resultant_of_le hf natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  have hresg : g.resultant (f * g).derivative g.natDegree d =
      g.resultant f * g.resultant g.derivative := by
    rw [derivative_mul, mul_comm f.derivative g, add_comm,
      resultant_add_mul_right _ _ _ _ _ hpg le_rfl,
      Polynomial.Monic.resultant_of_le hg hmul_g,
      ← Polynomial.Monic.resultant_of_le hg natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  have hmul := resultant_mul_left f g (f * g).derivative d hderiv
  rw [hresf, hresg] at hmul
  have hfd : f.resultant f.derivative =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
    rw [← Polynomial.Monic.resultant_of_le hf (natDegree_derivative_le f),
      hf.resultant_derivative]
  have hgd : g.resultant g.derivative =
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.discr := by
    rw [← Polynomial.Monic.resultant_of_le hg (natDegree_derivative_le g),
      hg.resultant_derivative]
  have hcomm : g.resultant f = (-1) ^ (g.natDegree * f.natDegree) * f.resultant g :=
    resultant_comm g f g.natDegree f.natDegree
  have hdisc := (hf.mul hg).resultant_derivative
  rw [hdeg] at hdisc
  dsimp only [d] at hmul
  rw [hmul, hfd, hgd, hcomm,
    triangle_add, pow_add, pow_add] at hdisc
  ring_nf at hdisc
  have hu : IsUnit (((-1 : R) ^ (f.natDegree * g.natDegree)) *
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)) :=
    ((isUnit_one.neg.pow _).mul (isUnit_one.neg.pow _)).mul (isUnit_one.neg.pow _)
  apply hu.mul_right_injective
  ring_nf
  convert hdisc.symm using 1
  all_goals ring

/-! ### The root-product formula -/

/-- For a monic polynomial that splits, the product of the derivative over the root multiset is
the discriminant, up to the sign `(-1) ^ (n * (n - 1) / 2)`. Over a number field this is the
statement that the discriminant of a minimal polynomial is, up to that sign, the norm of the
derivative at the generator. -/
theorem _root_.Polynomial.Monic.prod_roots_eval_derivative [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) : (f.roots.map fun a ↦ eval a f.derivative).prod =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  have key := resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
    (natDegree_derivative_le f) hs
  rwa [hf.resultant_derivative, hf.leadingCoeff, one_pow, one_mul, eq_comm] at key

/-- The root-product formula over an integral domain, where the resultant of `f` and its
derivative may be evaluated over the roots of `f`. -/
private theorem discr_prod_X_sub_C_of_isDomain [IsDomain R] {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  classical
  set f : R[X] := ∏ i, (X - C (r i)) with hfdef
  have hmon : f.Monic := monic_prod_X_sub_C r univ
  have hdeg : f.natDegree = n := by simp [hfdef]
  have hsplits : f.Splits := Splits.prod fun i _ ↦ Splits.X_sub_C (r i)
  have hroots : f.roots = univ.val.map r := by
    -- Expose the composition needed by `Multiset.map_map`.
    have hcomp : (fun i ↦ (X - C (r i) : R[X])) = (fun a ↦ X - C a) ∘ r := rfl
    rw [hfdef, Finset.prod_eq_multiset_prod,
      hcomp, ← Multiset.map_map, roots_multiset_prod_X_sub_C]
  -- The derivative of `f` at the root `r i` is the product of the other root differences.
  have hderiv : ∀ i, eval (r i) f.derivative = ∏ j ∈ univ.erase i, (r i - r j) := by
    intro i
    rw [hfdef, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hk
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk.symm, mem_univ i⟩)
        (by simp), zero_mul]
    · simp
  -- Evaluate the derivative of `f` over the roots of `f`.
  have key := hmon.prod_roots_eval_derivative hsplits
  rw [hroots, Multiset.map_map, ← Finset.prod_eq_multiset_prod, eq_comm] at key
  simp only [Function.comp_apply, hderiv, ← Finset.compl_singleton] at key
  -- Fold the off-diagonal product into a product over unordered pairs.
  rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag fun a b ↦ r b - r a] at key
  have hsign : ∀ i : Fin n, ∀ j ∈ Ioi i, (r i - r j) * (r j - r i) = -1 * (r i - r j) ^ 2 :=
    fun i j _ ↦ by ring
  rw [Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl (hsign i), hdeg] at key
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum] at key
  have hcard : ∑ i : Fin n, #(Ioi i) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi, Fin.sum_univ_eq_sum_range fun i ↦ n - 1 - i]
    rw [Finset.sum_range_reflect (fun i ↦ i) n, Finset.sum_range_id]
  rw [hcard] at key
  exact ((isUnit_one.neg.pow (n * (n - 1) / 2)).mul_right_injective key)

/-- **The root-product formula for the discriminant.** The discriminant of a product of linear
factors is the square of the Vandermonde-like product of the differences of the roots. This is a
universal polynomial identity, so it holds over any commutative ring, with the roots repeated
according to multiplicity. -/
theorem _root_.Polynomial.discr_prod_X_sub_C {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  set φ : MvPolynomial (Fin n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) r with hφ
  have hmon : (∏ i, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))).Monic :=
    monic_prod_X_sub_C _ _
  have hmap : (∏ i, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))).map φ =
      ∏ i, (X - C (r i)) := by
    simp [Polynomial.map_prod, hφ]
  have key := hmon.discr_map φ
  rw [hmap] at key
  rw [key, discr_prod_X_sub_C_of_isDomain]
  simp only [map_prod, map_pow, map_sub, hφ, MvPolynomial.eval₂Hom_X']

/-- The root-product formula, in the form `discr f = δ ^ 2` for the product `δ` of the differences
of the roots taken over pairs `i < j`. This is the form the discriminant test for containment in
the alternating group reads: a permutation of the roots multiplies `δ` by its sign. -/
theorem _root_.Polynomial.discr_prod_X_sub_C_eq_sq {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = (∏ i, ∏ j ∈ Ioi i, (r i - r j)) ^ 2 := by
  rw [Polynomial.discr_prod_X_sub_C, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_pow _ 2 _

/-- The root-product formula for a monic polynomial that splits after base change, written against
a numbering `r` of the root multiset over the extension ring. -/
theorem _root_.Polynomial.Monic.discr_eq_prod_roots_sub_sq {L : Type*} [CommRing L] [IsDomain L]
    [Algebra R L] {f : R[X]} (hf : f.Monic) (hs : (f.map (algebraMap R L)).Splits) {n : ℕ}
    {r : Fin n → L} (hr : (f.map (algebraMap R L)).roots = univ.val.map r) :
    algebraMap R L f.discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  have hfeq : f.map (algebraMap R L) = ∏ i, (X - C (r i)) := by
    rw [hs.eq_prod_roots_of_monic (hf.map _), hr, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [← hf.discr_map, hfeq, Polynomial.discr_prod_X_sub_C]

/-- For a separable field extension with a power basis, the algebra discriminant of the power
basis is the polynomial discriminant of the minimal polynomial of its generator. -/
theorem _root_.Algebra.discr_powerBasis_eq_minpoly_discr {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] (pb : PowerBasis K L) [Algebra.IsSeparable K L] :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  classical
  let E := AlgebraicClosure L
  let := fun a b : E ↦ Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  let r : Fin pb.dim → E := fun i ↦ e i pb.gen
  have hs : ((minpoly K pb.gen).map (algebraMap K E)).Splits := IsAlgClosed.splits _
  have hrmem : ∀ i, r i ∈ (minpoly K pb.gen).aroots E := by
    intro i
    rw [mem_roots, IsRoot.def, eval_map_algebraMap, aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  have hrnodup : (univ.val.map r).Nodup := by
    rw [Multiset.nodup_map_iff_of_injective]
    · exact univ.nodup
    · intro i j hij
      exact e.injective (pb.algHom_ext hij)
  have hr : ((minpoly K pb.gen).map (algebraMap K E)).roots = univ.val.map r := by
    have hle : univ.val.map r ≤ ((minpoly K pb.gen).map (algebraMap K E)).roots :=
      (Multiset.le_iff_subset hrnodup).2 (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
        exact hrmem i)
    have hcardroots : ((minpoly K pb.gen).map (algebraMap K E)).roots.card = pb.dim := by
      rw [← hs.natDegree_eq_card_roots,
        (minpoly.monic pb.isIntegral_gen).natDegree_map (algebraMap K E),
        pb.natDegree_minpoly]
    exact (Multiset.eq_of_le_of_card_le hle (by simp [hcardroots])).symm
  apply (algebraMap K E).injective
  rw [Algebra.discr_powerBasis_eq_prod K E pb e,
    (minpoly.monic pb.isIntegral_gen).discr_eq_prod_roots_sub_sq hs hr]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [r]
  ring

/-! ### Separability -/

/-- A monic polynomial is separable exactly when its discriminant is a unit. Both sides read the
resultant of `f` with `f.derivative`: separability is coprimality of that pair, and
`Polynomial.isUnit_resultant_iff_isCoprime` turns coprimality into a unit resultant. -/
@[simp]
theorem _root_.Polynomial.Monic.isUnit_discr_iff {f : R[X]} (hf : f.Monic) :
    IsUnit f.discr ↔ f.Separable := by
  rw [separable_def, ← isUnit_resultant_iff_isCoprime hf,
    ← Polynomial.Monic.resultant_of_le hf (natDegree_derivative_le f),
    hf.resultant_derivative,
    IsUnit.mul_iff]
  simp [isUnit_one.neg.pow]

/-- Over a field, a monic polynomial is separable exactly when its discriminant is nonzero.

⚠ The field hypothesis is not decoration: `Polynomial.not_separable_X_pow_two_sub_one` records a
monic polynomial over `ℤ` with nonzero discriminant that is not separable. -/
@[simp]
theorem _root_.Polynomial.Monic.discr_ne_zero_iff {K : Type*} [Field K] {f : K[X]}
    (hf : f.Monic) : f.discr ≠ 0 ↔ f.Separable := by
  rw [← hf.isUnit_discr_iff, isUnit_iff_ne_zero]

/-- Over a domain, the discriminant of a monic polynomial is nonzero exactly when the polynomial
becomes separable over the fraction field. This is the form every use over `ℤ` takes. -/
@[simp]
theorem _root_.Polynomial.Monic.discr_ne_zero_iff_separable_map (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic) :
    f.discr ≠ 0 ↔ (f.map (algebraMap R K)).Separable := by
  rw [← (hf.map (algebraMap R K)).discr_ne_zero_iff, hf.discr_map,
    map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)]

/-! ### The failure of the separability criterion over a ring -/

/-- The discriminant of `X ^ 2 - 1` over `ℤ` is `4`. -/
theorem _root_.Polynomial.discr_X_pow_two_sub_one : (X ^ 2 - 1 : ℤ[X]).discr = 4 := by
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [coeff_one]

/-- `X ^ 2 - 1` is not separable over `ℤ`, although its discriminant `4` is nonzero: a coprimality
witness for `X ^ 2 - 1` and `2 * X`, evaluated at `1`, would give `2 ∣ 1`. This is why
`Polynomial.Monic.discr_ne_zero_iff` is stated over a field, and why the version over a domain
passes to the fraction field. -/
theorem _root_.Polynomial.not_separable_X_pow_two_sub_one : ¬ (X ^ 2 - 1 : ℤ[X]).Separable := by
  rw [separable_def']
  rintro ⟨a, b, hab⟩
  have := congrArg (eval 1) hab
  simp at this
  omega

/-! ### Comparison with the discriminant of a cubic -/

/-- For a cubic with nonzero leading coefficient, the discriminant in the sense of `Cubic.discr`
is the discriminant of the associated degree-three polynomial. The two conventions agree on the
nose, with no normalization to monic and no sign. -/
@[simp]
theorem _root_.Cubic.discr_toPoly {P : Cubic R} (ha : P.a ≠ 0) : P.toPoly.discr = P.discr := by
  rw [discr_of_degree_eq_three (P.degree_of_a_ne_zero ha), P.coeff_eq_a, P.coeff_eq_b,
    P.coeff_eq_c, P.coeff_eq_d, Cubic.discr]

end TauCeti
