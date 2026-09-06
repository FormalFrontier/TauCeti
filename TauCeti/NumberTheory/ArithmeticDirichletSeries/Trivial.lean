/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The trivial ideal weight and Dedekind zeta coefficients

This file identifies the norm coefficients of the trivial ideal weight with the coefficients of
the Dedekind zeta function.  There is one necessary exception: Mathlib's coefficient counts all
integral ideals and therefore has value `1` at index zero, contributed by the zero ideal, whereas
an `ArithmeticFunction` has value zero there.  Since `LSeries` ignores its zero coefficient, the
two coefficient systems define the same series.

For the rational field the ring of integers is isomorphic to `ℤ`.  Mapping an ideal through this
isomorphism and using `Int.ideal_span_absNorm_eq_self` shows that there is exactly one ideal of
each positive norm.  Thus the trivial ideal weight over `ℚ` regroups to the constant coefficient
`1` at every positive index, as for the Riemann zeta function.

## Roadmap role

This is Layer **1.3**, the trivial specialization, of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  It completes Layer 1 without asserting the
exact abscissa of convergence; that is Layer 5, proved in
`TauCeti.abscissaOfAbsConv_normCoeff_one`.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The coefficient used in Mathlib's definition of the Dedekind zeta function: the number of
integral ideals of absolute norm `n`.

Unlike an `ArithmeticFunction`, this function has value `1` at zero, contributed by the zero
ideal. -/
noncomputable def dedekindZetaCoeff (n : ℕ) : ℕ :=
  Nat.card {I : _root_.Ideal (𝓞 K) // _root_.Ideal.absNorm I = n}

/-- The zero ideal is the unique integral ideal of absolute norm zero. -/
@[simp]
theorem dedekindZetaCoeff_zero : dedekindZetaCoeff K 0 = 1 := by
  simp [dedekindZetaCoeff, Ideal.absNorm_eq_zero_iff]

/-- The Dedekind zeta function is the `LSeries` of `dedekindZetaCoeff`. -/
theorem dedekindZeta_eq_LSeries_dedekindZetaCoeff (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := by
  simp [NumberField.dedekindZeta, dedekindZetaCoeff]

private def normFiberSubtypeEquiv {n : ℕ} (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.1, I.2⟩
  invFun I :=
    ⟨⟨I.1, by
      rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
      exact fun hzero ↦ hn (I.2.symm.trans hzero)⟩, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Away from zero, the cardinality of the finite nonzero-ideal norm fibre is the corresponding
Dedekind zeta coefficient. -/
theorem card_normFiber_eq_dedekindZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    (normFiber K n).card = dedekindZetaCoeff K n := by
  rw [← Nat.card_eq_finsetCard, dedekindZetaCoeff]
  exact Nat.card_congr <|
    (Equiv.subtypeEquivRight fun I ↦ mem_normFiber (K := K)).trans
      (normFiberSubtypeEquiv K hn)

/-- The trivial ideal arithmetic function regroups to the Dedekind zeta coefficients away from
zero.  At zero its norm coefficient is forced to vanish by the `ArithmeticFunction` carrier. -/
@[simp]
theorem normCoeff_one_apply (n : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, normCoeff_eq_sum_normFiber]
    simp [card_normFiber_eq_dedekindZetaCoeff K hn]

/-- The trivial unitary ideal weight has the Dedekind zeta coefficients away from zero. -/
theorem normCoeff_toIdealArithmeticFunction_one_apply (n : ℕ) :
    normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction n =
      if n = 0 then 0 else dedekindZetaCoeff K n := by
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_one]
  exact normCoeff_one_apply K n

/-- Regrouping the trivial ideal weight gives Mathlib's Dedekind zeta function. -/
theorem dedekindZeta_eq_LSeries_normCoeff_one (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (normCoeff K (1 : IdealArithmeticFunction K)) s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  apply LSeries_congr
  intro n hn
  rw [normCoeff_one_apply, ite_eq_right hn]

private theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Infinite R] [Infinite S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).symm

private theorem rat_normFiber_subsingleton (n : ℕ) :
    Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
  constructor
  intro I J
  apply Subtype.ext
  have hmap : I.1.map Rat.ringOfIntegersEquiv = J.1.map Rat.ringOfIntegersEquiv := by
    rw [← Int.ideal_span_absNorm_eq_self (I.1.map Rat.ringOfIntegersEquiv),
      ← Int.ideal_span_absNorm_eq_self (J.1.map Rat.ringOfIntegersEquiv),
      absNorm_map_ringEquiv Rat.ringOfIntegersEquiv I.1,
      absNorm_map_ringEquiv Rat.ringOfIntegersEquiv J.1, I.2, J.2]
  calc
    I.1 = Ideal.comap Rat.ringOfIntegersEquiv (I.1.map Rat.ringOfIntegersEquiv) :=
      (Ideal.comap_map_of_bijective _ Rat.ringOfIntegersEquiv.bijective).symm
    _ = Ideal.comap Rat.ringOfIntegersEquiv (J.1.map Rat.ringOfIntegersEquiv) :=
      congrArg (Ideal.comap Rat.ringOfIntegersEquiv) hmap
    _ = J.1 := Ideal.comap_map_of_bijective _ Rat.ringOfIntegersEquiv.bijective

private theorem rat_normFiber_nonempty (n : ℕ) :
    Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
  refine ⟨⟨(Ideal.span {(n : ℤ)}).map Rat.ringOfIntegersEquiv.symm, ?_⟩⟩
  rw [absNorm_map_ringEquiv, Ideal.absNorm_span_singleton]
  simp

/-- There is exactly one integral ideal of `ℚ` of each absolute norm. -/
@[simp]
theorem dedekindZetaCoeff_rat (n : ℕ) :
    dedekindZetaCoeff ℚ n = 1 := by
  let _ : Subsingleton {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} :=
    rat_normFiber_subsingleton n
  let _ : Nonempty {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := rat_normFiber_nonempty n
  exact Nat.card_unique

/-- Over `ℚ`, the trivial ideal weight has coefficient `1` at every positive integer. -/
theorem normCoeff_one_rat_apply {n : ℕ} (hn : 0 < n) :
    normCoeff ℚ (1 : IdealArithmeticFunction ℚ) n = 1 := by
  rw [normCoeff_one_apply, ite_eq_right hn.ne', dedekindZetaCoeff_rat]
  norm_num

/-- Over `ℚ`, the trivial unitary ideal weight has coefficient `1` at every positive integer. -/
theorem normCoeff_toIdealArithmeticFunction_one_rat_apply {n : ℕ} (hn : 0 < n) :
    normCoeff ℚ (1 : UnitaryIdealWeight ℚ).toIdealArithmeticFunction n = 1 := by
  rw [normCoeff_toIdealArithmeticFunction_one_apply, ite_eq_right hn.ne', dedekindZetaCoeff_rat]
  norm_num

end TauCeti
