/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Basic

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
* `Polynomial.Monic.discr_eq_prod_roots_sub_sq`: the same formula for a monic polynomial,
  written against a numbering `r : Fin f.natDegree → L` of its root multiset over an extension.
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
* `Cubic.toPoly_discr`: the two discriminants of a cubic with nonzero leading coefficient agree,
  so that `Cubic.discr` and `Polynomial.discr` may be used interchangeably in degree three.
* `Algebra.discr_powerBasis_eq_minpoly_discr`: the algebra discriminant of a power basis agrees
  with the polynomial discriminant of the minimal polynomial of its generator.
## Implementation notes

The root-product formula is a universal polynomial identity, so it is stated over an arbitrary
commutative ring and proved by base change from `MvPolynomial (Fin n) ℤ`, which is a domain and
over which the roots are the variables themselves.

The separability criterion is *not* a universal identity, and the failure is recorded here:
`Polynomial.not_separable_X_pow_two_sub_one` shows that `X ^ 2 - 1` over `ℤ` has nonzero
discriminant `4` and is not `Polynomial.Separable`. Over a domain the criterion is therefore
formulated after passage to a fraction field.

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

This is the monic case of `Polynomial.resultant_deriv`: the leading coefficient of that lemma is
`1`, and its positive-degree hypothesis is unnecessary, the constant polynomial `1` being
covered. -/
theorem _root_.Polynomial.Monic.resultant_deriv {f : R[X]} (hf : f.Monic) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with h | h
  · obtain rfl := eq_one_of_monic_natDegree_zero hf h
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  · rw [_root_.Polynomial.resultant_deriv (natDegree_pos_iff_degree_pos.mp h), hf.leadingCoeff,
      mul_one]

private noncomputable def Polynomial.sylvesterDerivIndexEquiv {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree) ≃
      Fin (f.natDegree - 1 + f.natDegree) :=
  finCongr (by rw [hdeg])

@[simp]
private theorem Polynomial.sylvesterDerivIndexEquiv_symm_val {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree)
    (i : Fin (f.natDegree - 1 + f.natDegree)) :
    ((sylvesterDerivIndexEquiv φ hdeg).symm i : ℕ) = i := rfl

private theorem Polynomial.sylvesterDerivIndexEquiv_symm_castAdd {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) (j : Fin (f.natDegree - 1)) :
    (sylvesterDerivIndexEquiv φ hdeg).symm (Fin.castAdd f.natDegree j) =
      Fin.castAdd (f.map φ).natDegree (Fin.cast (congrArg (· - 1) hdeg.symm) j) := by
  apply Fin.ext
  rfl

private theorem Polynomial.sylvesterDerivIndexEquiv_symm_natAdd {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) (j : Fin f.natDegree) :
    (sylvesterDerivIndexEquiv φ hdeg).symm (Fin.natAdd (f.natDegree - 1) j) =
      Fin.natAdd ((f.map φ).natDegree - 1) (Fin.cast hdeg.symm j) := by
  apply Fin.ext
  simp [sylvesterDerivIndexEquiv, hdeg]

/-- Mapping coefficients preserves `sylvesterDeriv` after transporting its degree-dependent
indices. The definition must be unfolded here because Mathlib supplies `sylvester_map_map`, but
no corresponding map lemma for the modified bottom row of `sylvesterDeriv`. -/
private theorem Polynomial.sylvesterDeriv_map_reindex {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    Matrix.reindex (sylvesterDerivIndexEquiv φ hdeg) (sylvesterDerivIndexEquiv φ hdeg)
      (f.map φ).sylvesterDeriv = φ.mapMatrix f.sylvesterDeriv := by
  classical
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
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
          rw [sylvesterDerivIndexEquiv_symm_castAdd φ hdeg j]
          simp [sylvesterDerivIndexEquiv, hdeg, hi, sylvester, derivative_map]
          split_ifs <;> simp
      | right j =>
          rw [sylvesterDerivIndexEquiv_symm_natAdd φ hdeg j]
          simp [sylvesterDerivIndexEquiv, hdeg, hi, sylvester, derivative_map]
          split_ifs <;> simp

/-- Base change of the discriminant along a ring morphism that preserves the degree. -/
theorem _root_.Polynomial.discr_map_of_natDegree_eq {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  classical
  simp only [discr, hdeg, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [RingHom.map_det]
  let e := Polynomial.sylvesterDerivIndexEquiv φ hdeg
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

/-- The discriminant of a product of monic polynomials is the product of their discriminants and
the square of their resultant. -/
theorem _root_.Polynomial.Monic.discr_mul {f g : R[X]} (hf : f.Monic) (hg : g.Monic) :
    (f * g).discr = f.discr * g.discr * (f.resultant g) ^ 2 := by
  -- A monic factor of degree zero is `1`, and both sides are then the discriminant of the other
  -- factor; the argument below needs both degrees positive.
  by_cases hf0 : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hf0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  by_cases hg0 : g.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hg hg0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  -- All resultants against `(f * g).derivative` are taken at the single degree bound `d`, which
  -- is the degree bound `Polynomial.discr` uses for `f * g`; the next block records that every
  -- polynomial the argument feeds to a resultant stays inside that bound.
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
  -- Step 1: expand `(f * g)' = f' * g + f * g'`. Against `f` the second summand is a multiple of
  -- `f`, so it drops out of the resultant, leaving `res(f, f') * res(f, g)`; against `g` the
  -- first summand drops out symmetrically.
  have hresf : f.resultant (f * g).derivative f.natDegree d =
      f.resultant f.derivative * f.resultant g := by
    rw [derivative_mul, resultant_add_mul_right _ _ _ _ _ hpf le_rfl,
      hf.resultant_of_le hmul_f,
      ← hf.resultant_of_le natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  have hresg : g.resultant (f * g).derivative g.natDegree d =
      g.resultant f * g.resultant g.derivative := by
    rw [derivative_mul, mul_comm f.derivative g, add_comm,
      resultant_add_mul_right _ _ _ _ _ hpg le_rfl,
      hg.resultant_of_le hmul_g,
      ← hg.resultant_of_le natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  -- Step 2: multiplicativity of the resultant in its left argument turns
  -- `res(f * g, (f * g)')` into the product of the two resultants just computed.
  have hmul := resultant_mul_left f g (f * g).derivative d hderiv
  rw [hresf, hresg] at hmul
  -- Step 3: read each resultant of a polynomial against its own derivative as a discriminant,
  -- and swap the arguments of the crossed resultant `res(g, f)`.
  have hfd : f.resultant f.derivative =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
    rw [← hf.resultant_of_le (natDegree_derivative_le f),
      hf.resultant_deriv]
  have hgd : g.resultant g.derivative =
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.discr := by
    rw [← hg.resultant_of_le (natDegree_derivative_le g),
      hg.resultant_deriv]
  have hcomm : g.resultant f = (-1) ^ (g.natDegree * f.natDegree) * f.resultant g :=
    resultant_comm g f g.natDegree f.natDegree
  -- Step 4: the same reading on the left-hand side produces the sign
  -- `(-1) ^ ((m + n) * (m + n - 1) / 2)`. The triangular number of a sum splits as the two
  -- triangular numbers plus the cross term `m * n` — Vandermonde's identity `Nat.add_choose_eq`
  -- at `k = 2` — so that sign is the two signs collected in Step 3 together with `(-1) ^ (m * n)`
  -- from `hcomm`. All of them cancel, being units.
  have htriangle : ∀ m n : ℕ,
      (m + n) * (m + n - 1) / 2 = m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
    intro m n
    have h := Nat.add_choose_eq m n 2
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.choose_two_right] at h
    omega
  have hdisc := (hf.mul hg).resultant_deriv
  rw [hdeg] at hdisc
  dsimp only [d] at hmul
  rw [hmul, hfd, hgd, hcomm,
    htriangle, pow_add, pow_add] at hdisc
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
the discriminant, up to the sign `(-1) ^ (n * (n - 1) / 2)`. After base change and identification
of the roots with conjugates, this yields the corresponding norm formula. -/
theorem _root_.Polynomial.Monic.prod_roots_eval_derivative [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) : (f.roots.map fun a ↦ eval a f.derivative).prod =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  have key := resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
    (natDegree_derivative_le f) hs
  rwa [hf.resultant_deriv, hf.leadingCoeff, one_pow, one_mul, eq_comm] at key

/-- The root-product formula over an integral domain, where the resultant of `f` and its
derivative may be evaluated over the roots of `f`. -/
private theorem discr_prod_X_sub_C_of_isDomain [IsDomain R] {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  classical
  set f : R[X] := ∏ i, (X - C (r i)) with hfdef
  have hmon : f.Monic := monic_prod_X_sub_C r univ
  have hdeg : f.natDegree = n := by simp [hfdef]
  have hsplits : f.Splits := Splits.prod fun i _ ↦ Splits.X_sub_C (r i)
  -- Rewrite `f` as a product over the multiset of roots, the shape Mathlib's root lemmas take.
  have hfms : f = (Multiset.map (fun a ↦ X - C a) (univ.val.map r)).prod := by
    rw [hfdef, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hroots : f.roots = univ.val.map r := by
    rw [hfms, roots_multiset_prod_X_sub_C]
  -- The derivative of `f` at the root `r i` is the product of the other root differences; this
  -- is `Polynomial.eval_multiset_prod_X_sub_C_derivative`, after erasing the index `i` rather
  -- than one occurrence of the value `r i`.
  have hderiv : ∀ i, eval (r i) f.derivative = ∏ j ∈ univ.erase i, (r i - r j) := by
    intro i
    have hmem : r i ∈ univ.val.map r :=
      Multiset.mem_map_of_mem r (Finset.mem_val.mpr (mem_univ i))
    have herase : (univ.val.map r).erase (r i) = (univ.erase i).val.map r := by
      rw [Finset.erase_val]
      conv_lhs => rw [← Multiset.cons_erase (Finset.mem_val.mpr (mem_univ i))]
      rw [Multiset.map_cons, Multiset.erase_cons_head]
    rw [hfms, eval_multiset_prod_X_sub_C_derivative hmem, herase, Finset.prod_eq_multiset_prod,
      Multiset.map_map]
    rfl
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
a numbering `r : Fin n → L` of the root multiset with arbitrary cardinality `n`. The complete
numbering, by `Fin f.natDegree`, is `Polynomial.Monic.discr_eq_prod_roots_sub_sq`. -/
private theorem _root_.Polynomial.Monic.discr_eq_prod_roots_sub_sq_of_splits {L : Type*}
    [CommRing L] [IsDomain L] [Algebra R L] {f : R[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap R L)).Splits) {n : ℕ} {r : Fin n → L}
    (hr : (f.map (algebraMap R L)).roots = univ.val.map r) :
    algebraMap R L f.discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  have hfeq : f.map (algebraMap R L) = ∏ i, (X - C (r i)) := by
    rw [hs.eq_prod_roots_of_monic (hf.map _), hr, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [← hf.discr_map, hfeq, Polynomial.discr_prod_X_sub_C]

/-- **The root-product formula for a monic polynomial.** Number the roots of a monic `f` over an
extension `L`, with multiplicity, as `r : Fin f.natDegree → L`. Then the discriminant of `f` is
the square of the Vandermonde-like product of the differences of the roots. Numbering the whole
root multiset by `Fin f.natDegree` already says that `f` splits over `L`, so no splitting
hypothesis appears. -/
theorem _root_.Polynomial.Monic.discr_eq_prod_roots_sub_sq {L : Type*} [CommRing L] [IsDomain L]
    [Algebra R L] {f : R[X]} (hf : f.Monic) {r : Fin f.natDegree → L}
    (hr : (f.map (algebraMap R L)).roots = univ.val.map r) :
    algebraMap R L f.discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  have hcard : (f.map (algebraMap R L)).roots.card = (f.map (algebraMap R L)).natDegree := by
    rw [hr, hf.natDegree_map]
    simp
  exact hf.discr_eq_prod_roots_sub_sq_of_splits (splits_iff_card_roots.mpr hcard) hr

/-! ### Separability -/

/-- A monic polynomial is separable exactly when its discriminant is a unit. This is the
ring-level form of the criterion; over a field it reads `f.discr ≠ 0`. -/
@[simp]
theorem _root_.Polynomial.Monic.isUnit_discr_iff {f : R[X]} (hf : f.Monic) :
    IsUnit f.discr ↔ f.Separable := by
  -- Separability is coprimality of `f` with `f.derivative`, which
  -- `Polynomial.isUnit_resultant_iff_isCoprime` reads as a unit resultant; the discriminant
  -- differs from that resultant by the unit sign.
  rw [separable_def, ← isUnit_resultant_iff_isCoprime hf,
    ← hf.resultant_of_le (natDegree_derivative_le f),
    hf.resultant_deriv,
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
becomes separable over the fraction field: over a domain the separability criterion is the one
formulated after passage to a fraction field. -/
@[simp]
theorem _root_.Polynomial.Monic.discr_ne_zero_iff_separable_map (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic) :
    f.discr ≠ 0 ↔ (f.map (algebraMap R K)).Separable := by
  rw [← (hf.map (algebraMap R K)).discr_ne_zero_iff, hf.discr_map,
    map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)]

/-! ### The discriminant of a power basis -/

/-- For a finite field extension with a power basis, the algebra discriminant of the power basis
is the polynomial discriminant of the minimal polynomial of its generator. Separability is not
needed: without it both sides vanish, the left because the trace form is identically zero and the
right because the minimal polynomial is inseparable. -/
theorem _root_.Algebra.discr_powerBasis_eq_minpoly_discr {K L : Type*} [Field K] [Field L]
    [Algebra K L] (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  let _ := pb.finite
  classical
  let E := AlgebraicClosure L
  let := fun a b : E ↦ Classical.propDecidable (Eq a b)
  have hs : ((minpoly K pb.gen).map (algebraMap K E)).Splits := IsAlgClosed.splits _
  -- A power basis is separable over `K` exactly when the whole extension is, since the number of
  -- embeddings of `L` into an algebraic closure is then the degree of the minimal polynomial.
  have hsep_of : IsSeparable K pb.gen → Algebra.IsSeparable K L := fun h ↦ by
    rw [← Field.finSepDegree_eq_finrank_iff,
      Field.finSepDegree_eq_of_isAlgClosed (F := K) (E := L) (K := E),
      AlgHom.natCard_of_powerBasis pb h hs, PowerBasis.finrank pb]
  by_cases hsepL : Algebra.IsSeparable K L
  case neg =>
    -- The inseparable case: the trace form vanishes identically, and so does the discriminant of
    -- the minimal polynomial, which is monic and not separable.
    have hzero : Algebra.traceMatrix K pb.basis = 0 := by
      ext i j
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        Algebra.trace_eq_zero_of_not_isSeparable hsepL]
    have hminpoly : ¬ (minpoly K pb.gen).Separable := fun h ↦ hsepL (hsep_of h)
    have : Nonempty (Fin pb.dim) := ⟨⟨0, pb.dim_pos⟩⟩
    rw [Algebra.discr_def, hzero, Matrix.det_zero,
      eq_comm, ← not_ne_iff, (minpoly.monic pb.isIntegral_gen).discr_ne_zero_iff]
    exact hminpoly
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  let r : Fin pb.dim → E := fun i ↦ e i pb.gen
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
    (minpoly.monic pb.isIntegral_gen).discr_eq_prod_roots_sub_sq_of_splits hs hr]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [r]
  ring

/-! ### The failure of the separability criterion over a ring -/

/-- The discriminant of `X ^ 2 - 1` over `ℤ` is `4`. -/
theorem _root_.Polynomial.discr_X_pow_two_sub_one : (X ^ 2 - 1 : ℤ[X]).discr = 4 := by
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [coeff_one]

/-- `X ^ 2 - 1` is not separable over `ℤ`, although its discriminant `4` is nonzero. This is why
`Polynomial.Monic.discr_ne_zero_iff` is stated over a field, and why the version over a domain
passes to the fraction field. -/
theorem _root_.Polynomial.not_separable_X_pow_two_sub_one : ¬ (X ^ 2 - 1 : ℤ[X]).Separable := by
  -- A coprimality witness for `X ^ 2 - 1` and `2 * X`, evaluated at `1`, would give `2 ∣ 1`.
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
theorem _root_.Cubic.toPoly_discr {P : Cubic R} (ha : P.a ≠ 0) : P.toPoly.discr = P.discr := by
  rw [discr_of_degree_eq_three (P.degree_of_a_ne_zero ha), P.coeff_eq_a, P.coeff_eq_b,
    P.coeff_eq_c, P.coeff_eq_d, Cubic.discr]

end TauCeti
