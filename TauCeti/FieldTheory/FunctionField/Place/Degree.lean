/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.IntermediateField.AdjoinInv

/-!
# The degree of a place of an algebraic function field is finite

The residue field `F_P` of a place `P` of `F / k` is an extension of the constants `k`, and its
degree `deg P = [F_P : k]` is the weight a place carries in a divisor. This file proves that
the degree is finite and bounded, which is Stichtenoth,
*Algebraic Function Fields and Codes*, Proposition 1.1.15: for every `x : F` whose order at `P`
is nonzero,

```
1 ≤ deg P ≤ [F : k(x)].
```

The bound is what guards the junk value of `Module.finrank` in the definition
`TauCeti.Place.degree`, so from here on the degree of a place of an algebraic function field is
a genuine positive natural number.

## Main results

* `TauCeti.Place.linearIndependent_adjoin_of_linearIndependent_residue`: the heart of the
  matter. If `x` has positive order at `P`, then elements of `𝒪_P` whose residues are linearly
  independent over `k` are themselves linearly independent over `k(x)`.
* `TauCeti.Place.finite_residueField`: the residue field of a place of an algebraic function
  field is a finite extension of the constants.
* `TauCeti.Place.degree_le_finrank_over_adjoin`: `deg P ≤ [F : k(x)]` for every `x` with
  `ord_P x ≠ 0`.
  The lower bound `1 ≤ deg P` is `TauCeti.Place.one_le_degree_of_isFunctionField`.
* `TauCeti.Place.degree_eq_one_iff_algebraMap_surjective` and
  `TauCeti.Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one`: the rational places are
  those whose residue field is exhausted by the constants, equivalently those at which every
  integral function agrees with a constant to first order.
* `TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isIntegral`: a place with algebraic residue
  field over an algebraically closed field of constants is rational (Stichtenoth, Remark 1.1.17).

## Implementation notes

The linear-independence step is Stichtenoth's argument, run over the polynomial ring rather
than over `k(x)`: the family is shown to be linearly independent over the `k`-subalgebra
`k[x] = Algebra.adjoin k {x}`, and `LinearIndependent.iff_fractionRing` then upgrades this to
`k(x) = k⟮x⟯`, which is the fraction field of `k[x]` by Mathlib's
`IntermediateField.algebraAdjoinAdjoin` instances. Clearing the common power of `x` from a
relation is done with `Polynomial.rootMultiplicity 0`, so no denominators ever appear.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.1.15 and Remark 1.1.17.
-/

public section

noncomputable section

open IntermediateField Polynomial

open scoped IntermediateField.algebraAdjoinAdjoin

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace Place

variable {P : Place k F}

/-! ### Residues of polynomial expressions in an element of the maximal ideal -/

/-- If `t` lies in the maximal ideal of `𝒪_P`, then the value of a polynomial `p` at `t` reduces
to the constant term of `p`. -/
private theorem residue_aeval_of_residue_eq_zero {t : P.integers}
    (ht : IsLocalRing.residue P.integers t = 0) (p : k[X]) :
    IsLocalRing.residue P.integers (aeval t p) =
      algebraMap k P.ResidueField (p.coeff 0) := by
  rw [aeval_def, Polynomial.hom_eval₂, ht, eval₂_at_zero]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

private theorem exists_common_X_pow_factor {ι : Type*} (s : Finset ι) (p : ι → k[X])
    (hne : ∃ i ∈ s, p i ≠ 0) :
    ∃ m, ∃ q : ι → k[X], (∀ i ∈ s, p i = X ^ m * q i) ∧
      ∃ j ∈ s, (q j).coeff 0 ≠ 0 := by
  classical
  have hfilter : (s.filter fun i ↦ p i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hpi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
  obtain ⟨j, hj, hjmin⟩ :=
    (s.filter fun i ↦ p i ≠ 0).exists_min_image (fun i ↦ rootMultiplicity 0 (p i)) hfilter
  obtain ⟨hjs, hjne⟩ := Finset.mem_filter.mp hj
  let m := rootMultiplicity (0 : k) (p j)
  let q : ι → k[X] := fun i ↦ p i /ₘ (X : k[X]) ^ m
  have hdvd : ∀ i ∈ s, (X : k[X]) ^ m ∣ p i := by
    intro i hi
    rcases eq_or_ne (p i) 0 with h | h
    · simp [h]
    · refine dvd_trans (pow_dvd_pow _ (hjmin i (Finset.mem_filter.mpr ⟨hi, h⟩))) ?_
      simpa [m] using pow_rootMultiplicity_dvd (p i) 0
  have hfactor : ∀ i ∈ s, p i = (X : k[X]) ^ m * q i := by
    intro i hi
    conv_lhs => rw [← modByMonic_add_div (p i) ((X : k[X]) ^ m)]
    rw [(modByMonic_eq_zero_iff_dvd (monic_X.pow m)).mpr (hdvd i hi), zero_add]
  refine ⟨m, q, hfactor, j, hjs, ?_⟩
  simpa [q, m, coeff_zero_eq_eval_zero] using
    (eval_divByMonic_pow_rootMultiplicity_ne_zero (p := p j) 0 hjne)

/-! ### Linear independence over `k(x)` of a lift of a `k`-independent family of residues -/

/-- **The key step of Stichtenoth, Proposition 1.1.15.** Let `x` be an element of positive order
at a place `P`, so that `x` reduces to `0` in the residue field. If elements `z i` of the
valuation ring `𝒪_P` have residues that are linearly independent over the constants `k`, then
the `z i` are themselves linearly independent over `k(x)`. -/
theorem linearIndependent_adjoin_of_linearIndependent_residue {x : F} (hx : 0 < P.ord x)
    {ι : Type*} {z : ι → P.integers}
    (hz : LinearIndependent k fun i ↦ IsLocalRing.residue P.integers (z i)) :
    LinearIndependent k⟮x⟯ fun i ↦ (z i : F) := by
  classical
  have hx0 : x ≠ 0 := fun h ↦ by simp [h] at hx
  have hxmem : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr hx.le
  have ht : IsLocalRing.residue P.integers ⟨x, hxmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, P.mem_maximalIdeal_iff_ord_pos hx0]
    exact hx
  have hxtr : Transcendental k x := P.transcendental_of_ord_ne_zero hx.ne'
  have hinj : Function.Injective (aeval x : k[X] →ₐ[k] F) := transcendental_iff_injective.mp hxtr
  -- The coercion `𝒪_P → F` as a `k`-algebra map, used to move relations between `F` and `𝒪_P`.
  have hcoe : ∀ (p : k[X]), ((aeval (⟨x, hxmem⟩ : P.integers) p : P.integers) : F) =
      aeval x p := fun p ↦ by
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k P.integers F)
      (⟨x, hxmem⟩ : P.integers) p
    simpa using this.symm
  rw [← LinearIndependent.iff_fractionRing (Algebra.adjoin k {x}) k⟮x⟯]
  rw [linearIndependent_iff']
  intro s g hsum i₀ hi₀
  by_contra hg0
  -- Write the coefficients as polynomials in `x`.
  have hrange : ∀ y : F, y ∈ Algebra.adjoin k ({x} : Set F) → ∃ p : k[X], aeval x p = y := by
    intro y hy
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hy
  choose p hp using fun i ↦ hrange (g i : F) (g i).2
  have hpzero : ∀ i, p i = 0 ↔ g i = 0 := by
    intro i
    rw [← hinj.eq_iff, map_zero, hp i]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg _ h⟩
  obtain ⟨m, q, hfactor, j, hjs, hqj⟩ := exists_common_X_pow_factor s p
    ⟨i₀, hi₀, fun h ↦ hg0 ((hpzero i₀).mp h)⟩
  -- The relation, with the common factor `x ^ m` removed, lives in `𝒪_P`.
  have hsumF : ∑ i ∈ s, aeval x (q i) * (z i : F) = 0 := by
    have hx0' : (x : F) ^ m ≠ 0 := pow_ne_zero _ hx0
    refine mul_left_cancel₀ hx0' ?_
    rw [Finset.mul_sum, mul_zero]
    rw [← hsum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Algebra.smul_def]
    have : (algebraMap (Algebra.adjoin k ({x} : Set F)) F) (g i) = aeval x (p i) := (hp i).symm
    rw [this, hfactor i hi]
    simp [mul_assoc]
  have hsumO : ∑ i ∈ s, aeval (⟨x, hxmem⟩ : P.integers) (q i) * z i = 0 := by
    apply Subtype.ext
    push_cast
    simpa [hcoe] using hsumF
  -- Reducing modulo the maximal ideal turns it into a `k`-relation between the residues.
  have hres : ∑ i ∈ s, (q i).coeff 0 • IsLocalRing.residue P.integers (z i) = 0 := by
    have := congrArg (IsLocalRing.residue P.integers) hsumO
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, residue_aeval_of_residue_eq_zero ht, Algebra.smul_def]
  have := linearIndependent_iff'.mp hz s (fun i ↦ (q i).coeff 0) hres j hjs
  exact hqj this

/-! ### Finiteness and the bound on the degree -/

private theorem rank_residueField_le_finrank_over_adjoin_of_ord_pos (P : Place k F) {x : F}
    (hx : 0 < P.ord x)
    [FiniteDimensional k⟮x⟯ F] :
    Module.rank k P.ResidueField ≤ (Module.finrank k⟮x⟯ F : Cardinal) := by
  refine rank_le fun s hs ↦ ?_
  choose z hz using fun i : s ↦ IsLocalRing.residue_surjective (i : P.ResidueField)
  have hz' : LinearIndependent k fun i : s ↦ IsLocalRing.residue P.integers (z i) := by
    simpa only [hz] using hs
  have := (linearIndependent_adjoin_of_linearIndependent_residue hx
    hz').fintype_card_le_finrank
  simpa using this

variable (P) in
/-- The rank of the residue field over the constants is bounded by `[F : k(x)]` for every `x`
whose order at `P` is nonzero, provided `F` is finite over `k(x)` (Stichtenoth, Proposition
1.1.15). -/
theorem rank_residueField_le_finrank_over_adjoin {x : F} (hx : P.ord x ≠ 0)
    [FiniteDimensional k⟮x⟯ F] :
    Module.rank k P.ResidueField ≤ (Module.finrank k⟮x⟯ F : Cardinal) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hinv : 0 < P.ord x⁻¹ := by rw [P.ord_inv]; omega
    have : FiniteDimensional k⟮x⁻¹⟯ F := by
      rw [IntermediateField.adjoin_simple_inv (K := k) x]
      infer_instance
    rw [← IntermediateField.adjoin_simple_inv (K := k) x]
    exact rank_residueField_le_finrank_over_adjoin_of_ord_pos P hinv
  · exact rank_residueField_le_finrank_over_adjoin_of_ord_pos P hpos

variable (P) in
/-- The residue field of a place of an algebraic function field is a finite extension of the
constants (Stichtenoth, Proposition 1.1.15). This is what makes `TauCeti.Place.degree` a
genuine invariant rather than a junk value. -/
theorem finite_residueField (hF : IsFunctionField k F) : Module.Finite k P.ResidueField := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have hpos : 0 < P.ord t := by omega
  have : FiniteDimensional k⟮t⟯ F :=
    hF.finiteDimensional_adjoin (P.transcendental_of_ord_ne_zero hpos.ne')
  exact Module.rank_lt_aleph0_iff.mp
    ((rank_residueField_le_finrank_over_adjoin P hpos.ne').trans_lt
      Cardinal.natCast_lt_aleph0)

variable (P) in
/-- **Stichtenoth, Proposition 1.1.15**: the degree of a place is bounded by `[F : k(x)]` for
every `x` whose order at `P` is nonzero. -/
theorem degree_le_finrank_over_adjoin (hF : IsFunctionField k F) {x : F} (hx : P.ord x ≠ 0) :
    P.degree ≤ Module.finrank k⟮x⟯ F := by
  have : FiniteDimensional k⟮x⟯ F :=
    hF.finiteDimensional_adjoin (P.transcendental_of_ord_ne_zero hx)
  rw [P.degree_eq_finrank]
  exact Module.finrank_le_of_rank_le (rank_residueField_le_finrank_over_adjoin P hx)

variable (P) in
/-- **Stichtenoth, Proposition 1.1.15**: the degree of a place of an algebraic function field
is positive. -/
theorem one_le_degree_of_isFunctionField (hF : IsFunctionField k F) : 1 ≤ P.degree := by
  let _ := P.finite_residueField hF
  exact P.one_le_degree

/-! ### Rational places -/

variable (P) in
/-- A place has degree one exactly when every residue is the residue of a constant: the
**rational** places (Stichtenoth, Definition 1.1.14). -/
theorem degree_eq_one_iff_algebraMap_surjective :
    P.degree = 1 ↔ Function.Surjective (algebraMap k P.ResidueField) := by
  rw [degree_eq_finrank, Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact ⟨And.right, fun h ↦ ⟨FaithfulSMul.algebraMap_injective k _, h⟩⟩

variable (P) in
/-- A place is rational exactly when every function integral at `P` agrees with a constant to
first order: this is the sense in which the value `f(P)` of a function at a rational place is
an element of `k`. The multiplicative form avoids the junk value `ord_P 0 = 0`, which occurs
here whenever `f` is itself a constant. -/
theorem degree_eq_one_iff_forall_exists_valuation_sub_lt_one :
    P.degree = 1 ↔
      ∀ f ∈ P.integers, ∃ c : k, P.valuation (f - algebraMap k F c) < 1 := by
  have hsub : ∀ (a : P.integers) (c : k),
      ((a - algebraMap k P.integers c : P.integers) : F) = (a : F) - algebraMap k F c :=
    fun a c ↦ by
      change (algebraMap P.integers F) (a - algebraMap k P.integers c) = _
      rw [map_sub, IsScalarTower.algebraMap_apply k P.integers F]
      -- The structure map from the valuation subring to `F` is its subtype coercion.
      rfl
  have key : ∀ (a : P.integers) (c : k),
      P.valuation ((a : F) - algebraMap k F c) < 1 ↔
        IsLocalRing.residue P.integers a = algebraMap k P.ResidueField c := by
    intro a c
    rw [← hsub a c, ← P.mem_maximalIdeal_iff_valuation_lt_one, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, sub_eq_zero]
    rw [IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [degree_eq_one_iff_algebraMap_surjective]
  constructor
  · intro h f hf
    obtain ⟨c, hc⟩ := h (IsLocalRing.residue P.integers ⟨f, hf⟩)
    exact ⟨c, (key ⟨f, hf⟩ c).mpr hc.symm⟩
  · intro h y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hc⟩ := h (a : F) a.2
    exact ⟨c, ((key a c).mp hc).symm⟩

variable (P) in
/-- If the residue field of a place is algebraic over an algebraically closed field of constants,
then the place is rational (Stichtenoth, Remark 1.1.17). -/
theorem degree_eq_one_of_isAlgClosed_of_isIntegral [IsAlgClosed k]
    [Algebra.IsIntegral k P.ResidueField] : P.degree = 1 := by
  exact (degree_eq_one_iff_algebraMap_surjective P).mpr
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

end Place

end TauCeti
