/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Degree
public import TauCeti.RingTheory.Valuation.Polynomial

/-!
# The zeros of a function of an algebraic function field are few

A nonzero element `x` of a function field `F / k` has, at every place `P`, an order `ord_P x`,
and the places where that order is nonzero are the zeros and the poles of `x`. This file proves
that a function has only finitely many of each, and quantifies the statement: the zeros of `x`,
counted with multiplicity `ord_P x` and weighted by the residue degree `deg P`, number at most
`[F : k(x)]`. This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed. (GTM 254),
Proposition 1.3.3 and Corollary 1.3.4.

The finiteness statement is what makes the divisor theory possible at all: without it the
principal divisor `div x = ∑_P ord_P x · P` of a function is not a finitely supported formal sum
and does not lie in `Place k F →₀ ℤ`.

## Main results

* `TauCeti.Place.sum_ord_mul_degree_le_finrank`: **Stichtenoth, Proposition 1.3.3**. For any
  finite set `S` of places at which `x` has positive order,
  `∑ P ∈ S, ord_P x · deg P ≤ [F : k(x)]`.
* `TauCeti.Place.card_le_finrank_of_forall_ord_pos`: in particular `x` has at most `[F : k(x)]`
  zeros.
* `TauCeti.Place.finite_setOf_ord_pos_of_finiteDimensional`: finiteness of the zeros when
  `F / k(x)` is finite-dimensional.
* `TauCeti.Place.finite_setOf_ord_pos`, `TauCeti.Place.finite_setOf_ord_neg` and
  `TauCeti.Place.finite_setOf_ord_ne_zero`: **Stichtenoth, Corollary 1.3.4**. Every element of
  an algebraic function field has finitely many zeros and finitely many poles. Each of the
  three is a statement about the totalized order function `ord_P`, and so is stated for every
  `x : F`: for `x ≠ 0` it is Corollary 1.3.4 as Stichtenoth states it, while at `x = 0` the
  junk value `ord_P 0 = 0` makes all three sets empty and the statement degenerate.

## Implementation notes

Proposition 1.3.3 is proved exactly as in Stichtenoth, by exhibiting `∑ P ∈ S, ord_P x · deg P`
elements of `F` that are linearly independent over `k(x)`. For each place `P` of `S` choose

* a uniformizer `t_P` (`TauCeti.Place.exists_ord_eq_one_and_forall_mem_ord_eq_zero`) which is a
  unit at every other place of `S`, and
* lifts `u_{P,j}` of a `k`-basis of the residue field `F_P`
  (`TauCeti.Place.exists_residue_eq_and_forall_mem_ord_eq`) whose order at every other place
  `Q` of `S` is at least `ord_Q x`;

the family is then `u_{P,j} · t_P ^ a` for `0 ≤ a < ord_P x`. Both choices are weak
approximation, and both are what make the places of `S` interact: a relation among the family
is grouped by place, and the group belonging to one place `P₀` is seen to have order exactly
`a₀ < ord_{P₀} x` at `P₀`, where `a₀` is the least exponent surviving the clearing of a common
factor `x`, while every other group has order at least `ord_{P₀} x` there. The two are
incompatible, so no relation exists.

As in `TauCeti.FieldTheory.FunctionField.Place.Degree`, the relation is taken over the
polynomial subalgebra `k[x] = Algebra.adjoin k {x}` and upgraded by
`LinearIndependent.iff_fractionRing`; the common power of `x` is cleared by
`TauCeti.Polynomial.exists_common_X_pow_factor`. Orders are compared in the multiplicative form
`P.valuation`, which is free of the junk value `ord_P 0 = 0`, so no term of a sum has to be
proved nonzero.

## Provenance

The mathematics is Stichtenoth's and the Lean development is independent. The separate
`vaca22/riemann-roch-function-fields` project (Guanghao Li, Apache-2.0) carries a complete
function-field Riemann–Roch development by the same Stichtenoth route; no code is copied or
adapted from it here. In particular, this file uses Tau Ceti's normalized-`ℤᵐ⁰`-valuation
`TauCeti.Place` API.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.3.3 and Corollary 1.3.4.
-/

public section

noncomputable section

open IntermediateField Polynomial

open scoped IntermediateField.algebraAdjoinAdjoin WithZero

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace Place

variable {P : Place k F}

/-! ### The order of a two-parameter polynomial combination at a single place

The two lemmas of this section are the local computations of Stichtenoth's Proposition 1.3.3:
the value of `P` on `∑ a, ∑ j, p_{a,j}(x) · u_j · t ^ a` when `P` is the place the family
belongs to, and when it is one of the others. -/

/-- A crude bound: if `x` and `t` are integral at `P` and every `u j` has value at most `γ`,
then so does any polynomial combination `∑ a, ∑ j, p_{a,j}(x) · u_j · t ^ a`. -/
private theorem valuation_sum_le {x t : F} (hx : x ∈ P.integers) (ht : P.valuation t ≤ 1)
    {E N : ℕ} {u : Fin N → F} {γ : ℤᵐ⁰} (hu : ∀ j, P.valuation (u j) ≤ γ)
    (q : Fin E → Fin N → k[X]) :
    P.valuation (∑ a : Fin E, ∑ j : Fin N, aeval x (q a j) * (u j * t ^ (a : ℕ))) ≤ γ := by
  refine P.valuation.map_sum_le fun a _ ↦ P.valuation.map_sum_le fun j _ ↦ ?_
  have h1 : P.valuation (aeval x (q a j)) ≤ 1 :=
    P.valuation.aeval_le_one (fun c ↦ P.mem_integers_iff.mp (P.algebraMap_mem_integers c))
      (P.mem_integers_iff.mp hx) (q a j)
  calc P.valuation (aeval x (q a j) * (u j * t ^ (a : ℕ)))
      = P.valuation (aeval x (q a j)) * (P.valuation (u j) * P.valuation t ^ (a : ℕ)) := by
        rw [map_mul, map_mul, map_pow]
    _ ≤ 1 * (γ * 1) := mul_le_mul' h1 (mul_le_mul' (hu j) (pow_le_one' ht _))
    _ = γ := by rw [mul_one, one_mul]

/-- **The local computation of Stichtenoth, Proposition 1.3.3.** Let `x` have positive order at
`P`, let `t` be a prime element at `P`, and let `u_1, …, u_N` be elements of `𝒪_P` whose
residues are linearly independent over `k`. Given coefficients `q a j ∈ k[X]`, let `A` be the
least exponent `a` at which some `q a j` has a nonzero constant term, and assume
`A < ord_P x`. Then the polynomial combination `∑ a, ∑ j, q_{a,j}(x) · u_j · t ^ a` has order
exactly `A` at `P`.

The point is that the exponents below `A` contribute a factor `x`, hence order at least
`ord_P x > A`, the exponents above `A` contribute order at least `a > A` through `t ^ a`, and
the exponent `A` itself contributes exactly `A` because the residues are independent. -/
private theorem valuation_sum_eq_exp_neg {x t : F} (hx : 0 < P.ord x) (ht : P.ord t = 1)
    {E N : ℕ} {u : Fin N → F} (humem : ∀ j, u j ∈ P.integers)
    (hu : LinearIndependent k fun j ↦ IsLocalRing.residue P.integers ⟨u j, humem j⟩)
    (q : Fin E → Fin N → k[X]) {A : Fin E} (hA : ∃ j, (q A j).coeff 0 ≠ 0)
    (hmin : ∀ a : Fin E, (a : ℕ) < (A : ℕ) → ∀ j, (q a j).coeff 0 = 0)
    (hAlt : ((A : ℕ) : ℤ) < P.ord x) :
    P.valuation (∑ a : Fin E, ∑ j : Fin N, aeval x (q a j) * (u j * t ^ (a : ℕ)))
      = WithZero.exp (-((A : ℕ) : ℤ)) := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hxmem : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr hx.le
  have hvx : P.valuation x = WithZero.exp (-P.ord x) := P.valuation_eq_exp_neg_ord hx0
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hvt : ∀ a : ℕ, P.valuation (t ^ a) = WithZero.exp (-(a : ℤ)) := fun a ↦ by
    rw [P.valuation_eq_exp_neg_ord (pow_ne_zero a ht0), P.ord_pow, ht, mul_one]
  have hone : ∀ c : k, P.valuation (algebraMap k F c) ≤ 1 := fun c ↦
    P.mem_integers_iff.mp (P.algebraMap_mem_integers c)
  -- The coefficient block at an exponent `a`, read inside `𝒪_P`.
  set Y : Fin E → P.integers :=
    fun a ↦ ∑ j, aeval (⟨x, hxmem⟩ : P.integers) (q a j) * ⟨u j, humem j⟩ with hY
  have hcoe : ∀ p : k[X], ((aeval (⟨x, hxmem⟩ : P.integers) p : P.integers) : F) = aeval x p := by
    intro p
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k P.integers F)
      (⟨x, hxmem⟩ : P.integers) p
    simpa using this.symm
  have hYcoe : ∀ a : Fin E, (Y a : F) = ∑ j : Fin N, aeval x (q a j) * u j := by
    intro a
    rw [hY]
    push_cast
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoe]
  -- Regrouping: the `a`-th slice of the family is the block `Y a` times `t ^ a`.
  have hslice : ∀ a : Fin E, ∑ j : Fin N, aeval x (q a j) * (u j * t ^ (a : ℕ))
      = (Y a : F) * t ^ (a : ℕ) := by
    intro a
    rw [hYcoe a, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  -- At the exponent `A` the block is a unit, because the residues are independent.
  have hres0 : IsLocalRing.residue P.integers (⟨x, hxmem⟩ : P.integers) = 0 :=
    (P.residue_eq_zero_iff_ord_pos hx0).mpr hx
  have hresY : IsLocalRing.residue P.integers (Y A)
      = ∑ j, (q A j).coeff 0 • IsLocalRing.residue P.integers ⟨u j, humem j⟩ := by
    rw [hY, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_mul, residue_aeval_of_residue_eq_zero hres0, Algebra.smul_def]
  have hresYne : IsLocalRing.residue P.integers (Y A) ≠ 0 := by
    rw [hresY]
    intro h
    obtain ⟨j, hj⟩ := hA
    exact hj (Fintype.linearIndependent_iff.mp hu _ h j)
  have hYne : (Y A : F) ≠ 0 := fun h ↦ hresYne (by
    have hYzero : Y A = 0 := Subtype.ext h
    rw [hYzero]
    exact map_zero _)
  have hvY : P.valuation (Y A : F) = 1 := by
    have h1 : 0 ≤ P.ord (Y A : F) := P.mem_integers_iff_ord_nonneg.mp (Y A).2
    have h2 : ¬ 0 < P.ord (Y A : F) := fun h ↦ hresYne ((P.residue_eq_zero_iff_ord_pos hYne).mpr h)
    have hordY : P.ord (Y A : F) = 0 := by omega
    rw [P.valuation_eq_exp_neg_ord hYne, hordY]
    simp
  -- Every other exponent contributes strictly less.
  have hsmall : ∀ a ∈ Finset.univ \ {A},
      P.valuation ((Y a : F) * t ^ (a : ℕ)) < P.valuation ((Y A : F) * t ^ (A : ℕ)) := by
    intro a ha
    have hane : (a : ℕ) ≠ (A : ℕ) := fun h ↦ by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
      exact ha.2 (Fin.ext h)
    rw [map_mul, map_mul, hvY, hvt, hvt, one_mul]
    rcases lt_or_gt_of_ne hane with hlt | hgt
    · -- Below `A` every coefficient is divisible by `X`, so the block is divisible by `x`.
      have hblock : P.valuation (Y a : F) ≤ WithZero.exp (-P.ord x) := by
        rw [hYcoe a]
        refine P.valuation.map_sum_le fun j _ ↦ ?_
        obtain ⟨q', hq'⟩ := Polynomial.X_dvd_iff.mpr (hmin a hlt j)
        rw [map_mul, hq', map_mul, aeval_X, map_mul, hvx]
        calc WithZero.exp (-P.ord x) * P.valuation (aeval x q') * P.valuation (u j)
            ≤ WithZero.exp (-P.ord x) * 1 * 1 :=
              mul_le_mul' (mul_le_mul' le_rfl (P.valuation.aeval_le_one hone
                (P.mem_integers_iff.mp hxmem) q')) (P.mem_integers_iff.mp (humem j))
          _ = WithZero.exp (-P.ord x) := by rw [mul_one, mul_one]
      calc P.valuation (Y a : F) * WithZero.exp (-((a : ℕ) : ℤ))
          ≤ WithZero.exp (-P.ord x) * WithZero.exp (-((a : ℕ) : ℤ)) :=
            mul_le_mul' hblock le_rfl
        _ = WithZero.exp (-P.ord x + -((a : ℕ) : ℤ)) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp (-P.ord x) := WithZero.exp_le_exp.mpr (by omega)
        _ < WithZero.exp (-((A : ℕ) : ℤ)) := WithZero.exp_lt_exp.mpr (by omega)
    · -- Above `A` the factor `t ^ a` alone already forces a strictly larger order.
      calc P.valuation (Y a : F) * WithZero.exp (-((a : ℕ) : ℤ))
          ≤ 1 * WithZero.exp (-((a : ℕ) : ℤ)) :=
            mul_le_mul' (P.mem_integers_iff.mp (Y a).2) le_rfl
        _ = WithZero.exp (-((a : ℕ) : ℤ)) := one_mul _
        _ < WithZero.exp (-((A : ℕ) : ℤ)) := WithZero.exp_lt_exp.mpr (by omega)
  rw [Finset.sum_congr rfl fun a _ ↦ hslice a,
    P.valuation.map_sum_eq_of_lt (Finset.mem_univ A) hsmall, map_mul, hvY, hvt, one_mul]

/-! ### Proposition 1.3.3 -/

/-- **The products `u P j * t P ^ a` are linearly independent over `k⟮x⟯`.** Given
uniformizers `t P` at each place of `S` that are units at the other places of `S`, and lifts
`u P j` of a `k`-basis of each residue field that are as small as `x` at the other places, the
products `u P j * t P ^ a` for `a < ord_P x` form a `k⟮x⟯`-linearly independent family. This is
the content of Stichtenoth, Proposition 1.3.3; counting the family is all that remains. -/
private theorem linearIndependent_mul_pow_of_linearIndependent_residue {x : F}
    {S : Finset (Place k F)} (hS : ∀ P ∈ S, 0 < P.ord x)
    {t : {P : Place k F // P ∈ S} → F}
    (ht1 : ∀ P : {P : Place k F // P ∈ S}, (P : Place k F).ord (t P) = 1)
    (ht0 : ∀ (P : {P : Place k F // P ∈ S}) (Q : Place k F), Q ∈ S → Q ≠ (P : Place k F) →
      Q.ord (t P) = 0)
    {u : ∀ P : {P : Place k F // P ∈ S},
      Fin (Module.finrank k (P : Place k F).ResidueField) → F}
    (humem : ∀ (P : {P : Place k F // P ∈ S}) j, u P j ∈ (P : Place k F).integers)
    (huord : ∀ (P : {P : Place k F // P ∈ S}) j (Q : Place k F), Q ∈ S → Q ≠ (P : Place k F) →
      Q.ord (u P j) = Q.ord x)
    (hlib : ∀ P : {P : Place k F // P ∈ S}, LinearIndependent k
      fun j ↦ IsLocalRing.residue (P : Place k F).integers ⟨u P j, humem P j⟩) :
    LinearIndependent k⟮x⟯
      (fun i : Σ P : {P : Place k F // P ∈ S}, Fin ((P : Place k F).ord x).toNat ×
          Fin (Module.finrank k (P : Place k F).ResidueField) ↦
        u i.1 i.2.2 * t i.1 ^ (i.2.1 : ℕ)) := by
  classical
  -- Clear a common power of `x` from the coefficients, then localise at the place `P₀` carrying
  -- the surviving lowest-degree coefficient: there the valuation of its own block is `exp (-A)`
  -- exactly, while every other block is at most `exp (-ord_{P₀} x)`, and `A < ord_{P₀} x` makes
  -- that a contradiction.
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₁, hP₁⟩
  · have : IsEmpty (Σ P : {P : Place k F // P ∈ (∅ : Finset (Place k F))},
        Fin ((P : Place k F).ord x).toNat ×
          Fin (Module.finrank k (P : Place k F).ResidueField)) :=
      ⟨fun i ↦ Finset.notMem_empty _ i.1.2⟩
    exact linearIndependent_empty_type
  have hx0 : x ≠ 0 := by rintro rfl; simpa using hS P₁ hP₁
  -- Linear independence of the residue vectors already forces each lift to be nonzero.
  have hune : ∀ (P : {P : Place k F // P ∈ S}) j, u P j ≠ 0 := by
    intro P j h
    have hu0 : (⟨u P j, humem P j⟩ : (P : Place k F).integers) = 0 := Subtype.ext h
    exact (hlib P).ne_zero j (by rw [hu0, map_zero])
  rw [← LinearIndependent.iff_fractionRing (Algebra.adjoin k {x}) k⟮x⟯,
    Fintype.linearIndependent_iff]
  intro g hsum i₁
  by_contra hg0
  -- Write the coefficients as polynomials in `x` and clear the common power of `x`.
  have hrange : ∀ y : F, y ∈ Algebra.adjoin k ({x} : Set F) → ∃ p : k[X], aeval x p = y := by
    intro y hy
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hy
  choose p hp using fun i ↦ hrange ((g i : Algebra.adjoin k ({x} : Set F)) : F) (g i).2
  have hpne : p i₁ ≠ 0 := by
    intro h
    exact hg0 (Subtype.ext (by simpa [h] using (hp i₁).symm))
  obtain ⟨m, q, hfactor, i₂, -, hq₂⟩ :=
    TauCeti.Polynomial.exists_common_X_pow_factor Finset.univ p ⟨i₁, Finset.mem_univ _, hpne⟩
  have hsumF : ∑ i, aeval x (q i) * (u i.1 i.2.2 * t i.1 ^ (i.2.1 : ℕ)) = 0 := by
    refine mul_left_cancel₀ (pow_ne_zero m hx0) ?_
    rw [Finset.mul_sum, mul_zero, ← hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Subalgebra.algebraMap_apply, ← hp i,
      hfactor i (Finset.mem_univ i), map_mul, map_pow, aeval_X]
    ring
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma] at hsumF
  simp only [Fintype.sum_prod_type] at hsumF
  -- Split the relation into the block at `P₀ := i₂.1` and the remaining blocks.
  set P₀ := i₂.1
  have hmem₂ : i₂.2.1 ∈ Finset.univ.filter
      (fun a : Fin ((P₀ : Place k F).ord x).toNat ↦ ∃ j, (q ⟨P₀, a, j⟩).coeff 0 ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i₂.2.2, hq₂⟩
  set A := (Finset.univ.filter
    (fun a : Fin ((P₀ : Place k F).ord x).toNat ↦ ∃ j, (q ⟨P₀, a, j⟩).coeff 0 ≠ 0)).min'
      ⟨i₂.2.1, hmem₂⟩ with hAdef
  have hAex : ∃ j, (q ⟨P₀, A, j⟩).coeff 0 ≠ 0 := by
    have := Finset.min'_mem _ (⟨i₂.2.1, hmem₂⟩ :
      (Finset.univ.filter (fun a : Fin ((P₀ : Place k F).ord x).toNat ↦
        ∃ j, (q ⟨P₀, a, j⟩).coeff 0 ≠ 0)).Nonempty)
    simpa [← hAdef] using this
  have hAmin : ∀ a : Fin ((P₀ : Place k F).ord x).toNat, (a : ℕ) < (A : ℕ) →
      ∀ j, (q ⟨P₀, a, j⟩).coeff 0 = 0 := by
    intro a ha j
    by_contra h
    have hle : A ≤ a := Finset.min'_le _ a (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, h⟩)
    exact absurd (Fin.le_def.mp hle) (by omega)
  have hAlt : ((A : ℕ) : ℤ) < (P₀ : Place k F).ord x := by
    have h1 := A.isLt
    have h2 := hS (P₀ : Place k F) P₀.2
    omega
  have hkey : (P₀ : Place k F).valuation
      (∑ a : Fin ((P₀ : Place k F).ord x).toNat,
        ∑ j : Fin (Module.finrank k (P₀ : Place k F).ResidueField),
          aeval x (q ⟨P₀, a, j⟩) * (u P₀ j * t P₀ ^ (a : ℕ)))
      = WithZero.exp (-((A : ℕ) : ℤ)) :=
    valuation_sum_eq_exp_neg (hS (P₀ : Place k F) P₀.2) (ht1 P₀) (humem P₀) (hlib P₀) _
      hAex hAmin hAlt
  have hother : ∀ P : {P : Place k F // P ∈ S}, P ≠ P₀ →
      (P₀ : Place k F).valuation
        (∑ a : Fin ((P : Place k F).ord x).toNat,
          ∑ j : Fin (Module.finrank k (P : Place k F).ResidueField),
            aeval x (q ⟨P, a, j⟩) * (u P j * t P ^ (a : ℕ)))
        ≤ WithZero.exp (-(P₀ : Place k F).ord x) := by
    intro P hP
    have hne : (P₀ : Place k F) ≠ (P : Place k F) := fun h ↦ hP (Subtype.ext h.symm)
    refine valuation_sum_le ?_ ?_ ?_ _
    · exact (P₀ : Place k F).mem_integers_iff_ord_nonneg.mpr (hS _ P₀.2).le
    · exact (P₀ : Place k F).mem_integers_iff.mp
        ((P₀ : Place k F).mem_integers_iff_ord_nonneg.mpr
          (by rw [ht0 P (P₀ : Place k F) P₀.2 hne]))
    · intro j
      rw [(P₀ : Place k F).valuation_eq_exp_neg_ord (hune P j),
        huord P j (P₀ : Place k F) P₀.2 hne]
  have hsplit : (∑ a : Fin ((P₀ : Place k F).ord x).toNat,
      ∑ j : Fin (Module.finrank k (P₀ : Place k F).ResidueField),
        aeval x (q ⟨P₀, a, j⟩) * (u P₀ j * t P₀ ^ (a : ℕ)))
      = -∑ P ∈ Finset.univ.erase P₀, ∑ a : Fin ((P : Place k F).ord x).toNat,
          ∑ j : Fin (Module.finrank k (P : Place k F).ResidueField),
            aeval x (q ⟨P, a, j⟩) * (u P j * t P ^ (a : ℕ)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ P₀)]
    exact hsumF
  rw [hsplit, Valuation.map_neg] at hkey
  have hle : WithZero.exp (-((A : ℕ) : ℤ)) ≤ WithZero.exp (-(P₀ : Place k F).ord x) := by
    rw [← hkey]
    exact Valuation.map_sum_le _ fun P hP ↦ hother P (Finset.ne_of_mem_erase hP)
  have := WithZero.exp_le_exp.mp hle
  omega

/-- The natural-number form of Stichtenoth, Proposition 1.3.3, which is what the linear
independence of Stichtenoth's family says on the nose. -/
private theorem sum_toNat_mul_finrank_le {x : F} [FiniteDimensional k⟮x⟯ F]
    {S : Finset (Place k F)} (hS : ∀ P ∈ S, 0 < P.ord x) :
    ∑ P ∈ S, (P.ord x).toNat * Module.finrank k P.ResidueField ≤ Module.finrank k⟮x⟯ F := by
  -- A `k`-basis of each residue field, which is finite over `k` because `x` is a parameter.
  obtain ⟨b⟩ : Nonempty (∀ P : {P : Place k F // P ∈ S},
      Module.Basis (Fin (Module.finrank k (P : Place k F).ResidueField)) k
        (P : Place k F).ResidueField) :=
    ⟨fun P ↦
      let _ := (P : Place k F).finiteDimensional_residueField_of_ord_ne_zero
        (hS (P : Place k F) P.2).ne'
      Module.finBasis k _⟩
  -- Uniformizers, chosen to be units at the other places of `S`.
  choose t ht1 ht0 using fun P : {P : Place k F // P ∈ S} ↦
    (P : Place k F).exists_ord_eq_one_and_forall_mem_ord_eq_zero S
  -- Lifts of the residue bases, chosen to be as small as `x` at the other places of `S`.
  choose u humem hures huord using fun (P : {P : Place k F // P ∈ S})
      (j : Fin (Module.finrank k (P : Place k F).ResidueField)) ↦
    (P : Place k F).exists_residue_eq_and_forall_mem_ord_eq S (b P j) (fun Q ↦ Q.ord x)
  have hlib : ∀ P : {P : Place k F // P ∈ S}, LinearIndependent k
      fun j ↦ IsLocalRing.residue (P : Place k F).integers ⟨u P j, humem P j⟩ := fun P ↦ by
    simpa only [hures P] using (b P).linearIndependent
  -- Stichtenoth's family, indexed by a place of `S`, an exponent and a basis vector.
  have key := linearIndependent_mul_pow_of_linearIndependent_residue hS ht1 ht0 humem huord hlib
  have hcard := key.fintype_card_le_finrank
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  rwa [Finset.sum_coe_sort S
    (fun P ↦ (P.ord x).toNat * Module.finrank k P.ResidueField)] at hcard

/-- **Stichtenoth, Proposition 1.3.3**: the zeros of `x`, counted with multiplicity and weighted
by their residue degrees, number at most `[F : k(x)]`. The statement is for an arbitrary finite
set `S` of zeros of `x`; that there are only finitely many of them is the corollary
`TauCeti.Place.finite_setOf_ord_pos`. -/
theorem sum_ord_mul_degree_le_finrank {x : F} [FiniteDimensional k⟮x⟯ F]
    {S : Finset (Place k F)} (hS : ∀ P ∈ S, 0 < P.ord x) :
    ∑ P ∈ S, P.ord x * (P.degree : ℤ) ≤ (Module.finrank k⟮x⟯ F : ℤ) := by
  have key := sum_toNat_mul_finrank_le hS
  calc ∑ P ∈ S, P.ord x * (P.degree : ℤ)
      = ((∑ P ∈ S, (P.ord x).toNat * Module.finrank k P.ResidueField : ℕ) : ℤ) := by
        push_cast
        exact Finset.sum_congr rfl fun P hP ↦ by
          rw [Int.toNat_of_nonneg (hS P hP).le, P.degree_eq_finrank]
    _ ≤ (Module.finrank k⟮x⟯ F : ℤ) := by exact_mod_cast key

/-- A function of a function field has at most `[F : k(x)]` zeros: the degree-weighted count of
`TauCeti.Place.sum_ord_mul_degree_le_finrank`, read with every weight replaced by `1`. -/
theorem card_le_finrank_of_forall_ord_pos {x : F} [FiniteDimensional k⟮x⟯ F]
    {S : Finset (Place k F)} (hS : ∀ P ∈ S, 0 < P.ord x) :
    S.card ≤ Module.finrank k⟮x⟯ F := by
  have key := sum_ord_mul_degree_le_finrank hS
  have hlow : (S.card : ℤ) ≤ ∑ P ∈ S, P.ord x * (P.degree : ℤ) := by
    have hcard : (S.card : ℤ) = ∑ _P ∈ S, (1 : ℤ) := by simp
    rw [hcard]
    refine Finset.sum_le_sum fun P hP ↦ ?_
    let _ := P.finiteDimensional_residueField_of_ord_ne_zero (x := x) (hS P hP).ne'
    have h1 : 1 ≤ P.degree := P.one_le_degree
    have h2 : 1 ≤ P.ord x := hS P hP
    exact one_le_mul_of_one_le_of_one_le h2 (by exact_mod_cast h1)
  omega

/-! ### Corollary 1.3.4: the zeros and the poles are finite in number -/

/-- The places at which `x` has positive order are finite in number whenever `F / k(x)` is
finite-dimensional. For `x ≠ 0` these places are the zeros of `x`; at `x = 0` the set is empty,
by the junk value `ord_P 0 = 0`. -/
theorem finite_setOf_ord_pos_of_finiteDimensional {x : F} [FiniteDimensional k⟮x⟯ F] :
    {P : Place k F | 0 < P.ord x}.Finite := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (Module.finrank k⟮x⟯ F + 1)
  have := card_le_finrank_of_forall_ord_pos (S := T) fun P hP ↦ hTsub hP
  omega

/-- **Stichtenoth, Corollary 1.3.4**: an element of an algebraic function field has only
finitely many zeros. The set is the support of the totalized order function `ord_P` on the
positive side, so the statement holds for every `x : F`; it is Corollary 1.3.4 for `x ≠ 0`,
while at `x = 0` the junk value `ord_P 0 = 0` empties it, the zero function having in truth a
zero at every place. -/
theorem finite_setOf_ord_pos (hF : IsFunctionField k F) (x : F) :
    {P : Place k F | 0 < P.ord x}.Finite := by
  by_cases hx : IsAlgebraic k x
  · -- An element algebraic over the constants is a unit at every place.
    have hzeros : {P : Place k F | 0 < P.ord x} = ∅ := by
      ext P
      simp [P.ord_eq_zero_of_isAlgebraic hx]
    rw [hzeros]
    exact Set.finite_empty
  · let _ := hF.finiteDimensional_adjoin (y := x) hx
    exact finite_setOf_ord_pos_of_finiteDimensional (x := x)

/-- **Stichtenoth, Corollary 1.3.4**: an element of an algebraic function field has only
finitely many poles. A pole of `x` is a zero of `x⁻¹`. As for the zeros, the set is a side of
the support of the totalized `ord_P` and the statement is Corollary 1.3.4 for `x ≠ 0`; at
`x = 0`, where `ord_P 0 = 0`, it is empty, as the zero function indeed has no pole. -/
theorem finite_setOf_ord_neg (hF : IsFunctionField k F) (x : F) :
    {P : Place k F | P.ord x < 0}.Finite := by
  refine (finite_setOf_ord_pos hF x⁻¹).subset fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, P.ord_inv] at hP ⊢
  omega

/-- **Stichtenoth, Corollary 1.3.4**: the places at which an element of an algebraic function
field has nonzero order are finite in number. This is the finiteness that makes the principal
divisor `div x = ∑_P ord_P x · P` of a nonzero `x` a finitely supported formal sum; `0` has no
principal divisor, and the statement at `x = 0` is the degenerate one that the junk value
`ord_P 0 = 0` has empty support. -/
theorem finite_setOf_ord_ne_zero (hF : IsFunctionField k F) (x : F) :
    {P : Place k F | P.ord x ≠ 0}.Finite := by
  refine ((finite_setOf_ord_pos hF x).union (finite_setOf_ord_neg hF x)).subset fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq] at hP
  rcases lt_or_gt_of_ne hP with h | h
  · exact Or.inr h
  · exact Or.inl h

end Place

end TauCeti

end

end
