/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic
public import TauCeti.FieldTheory.IntermediateField.Adjoin.Inv
public import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental
public import TauCeti.FieldTheory.FunctionField.AffineModel.Place
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Principal

/-!
# The product formula for algebraic function fields

This file proves that the principal divisor of every nonzero function has degree zero.  More
precisely, for a function `z` transcendental over `k`, both its zero divisor and its pole divisor
have degree `[F : k(z)]`.  This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Theorem 1.4.11.

Here `k` is not assumed to be the exact constant field of `F`, so a function outside `k` may still
be algebraic over `k`.  Accordingly the hypothesis throughout is transcendence over `k`, which is
strictly stronger than nonconstancy.

## Main results

* `TauCeti.Divisor.degree_zeros` and `TauCeti.Divisor.degree_poles` compute the two effective
  parts of the principal divisor of a function transcendental over `k`.
* `TauCeti.Divisor.degree_principal` is the product formula.
* `TauCeti.Divisor.degreeClass` descends degree to the divisor class group, and
  `TauCeti.Divisor.degree_eq_of_linearlyEquivalent` records invariance under linear equivalence.
* `TauCeti.riemannRochSpace_eq_bot_of_degree_neg` and
  `TauCeti.Divisor.dim_eq_zero_of_degree_neg` are the negative-degree consequence.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.4.11 and Corollary 1.4.12.
-/

public section

open IntermediateField

namespace TauCeti

open AlgebraicGeometry
open scoped IntermediateField.algebraAdjoinAdjoin

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The existing bound on the weighted number of zeros, expressed as the degree of the zero
divisor. -/
private theorem degree_zeros_le_finrank_adjoin (hF : IsFunctionField k F) {z : F} (hz : z ≠ 0)
    [FiniteDimensional k⟮z⟯ F] :
    Divisor.degree (Divisor.zeros hF (Units.mk0 z hz)) ≤ (Module.finrank k⟮z⟯ F : ℤ) := by
  have hsupport : ∀ P ∈ (Divisor.zeros hF (Units.mk0 z hz)).support, 0 < P.ord z :=
    fun P hP ↦ (Divisor.mem_support_zeros_iff hF).mp hP
  have hbound := Place.sum_ord_mul_degree_le_finrank hsupport
  calc
    Divisor.degree (Divisor.zeros hF (Units.mk0 z hz)) =
        ∑ P ∈ (Divisor.zeros hF (Units.mk0 z hz)).support,
          (Divisor.zeros hF (Units.mk0 z hz)) P * P.degree :=
      Divisor.degree_eq_sum_support _
    _ = ∑ P ∈ (Divisor.zeros hF (Units.mk0 z hz)).support,
          P.ord z * P.degree := Finset.sum_congr rfl fun P hP ↦ by
      -- Expose function application as `coeff` so the zeros coefficient theorem rewrites it.
      change (Divisor.zeros hF (Units.mk0 z hz)).coeff P * P.degree =
        P.ord z * P.degree
      rw [Divisor.coeff_zeros, Units.val_mk0]
      rw [max_eq_left (hsupport P hP).le]
    _ ≤ (Module.finrank k⟮z⟯ F : ℤ) := hbound

/-- **The growth estimate** behind Stichtenoth's proofs of Theorems 1.4.11 and 1.4.14, in divisor
form: if the functions `c i` are linearly independent over `k⟮x⟯` and all their poles are
dominated by one divisor `C`, then the `#ι * (l + 1)` products `c i * x ^ j` with `j ≤ l` are
linearly independent elements of `L(l (x)_∞ + C)`. -/
theorem Divisor.card_mul_succ_le_dim_nsmul_poles_add (hF : IsFunctionField k F) (x : Fˣ)
    (hx : Transcendental k (x : F)) {ι : Type*} [Fintype ι]
    (c : ι → Fˣ) (hc : LinearIndependent k⟮(x : F)⟯ fun i ↦ (c i : F)) {C : Divisor k F}
    (hC : ∀ i, Divisor.poles hF (c i) ≤ C) (l : ℕ) :
    Fintype.card ι * (l + 1) ≤ Divisor.dim (l • Divisor.poles hF x + C) := by
  classical
  have hmem : ∀ p : ι × Fin (l + 1),
      (c p.1 : F) * (x : F) ^ (p.2 : ℕ) ∈ riemannRochSpace (l • Divisor.poles hF x + C) := by
    rintro ⟨i, j⟩
    have hjle : (j : ℕ) ≤ l := Nat.lt_succ_iff.mp j.isLt
    have hpow : Divisor.principal hF (x ^ (j : ℕ)) =
        (j : ℕ) • Divisor.principal hF x := by
      rw [← zpow_natCast x (j : ℕ), Divisor.principal_zpow, natCast_zsmul]
    have hsplit : l • Divisor.poles hF x =
        (j : ℕ) • Divisor.poles hF x + (l - (j : ℕ)) • Divisor.poles hF x := by
      rw [← add_nsmul, Nat.add_sub_cancel' hjle]
    have hkey : Divisor.principal hF (c i * x ^ (j : ℕ)) +
          (l • Divisor.poles hF x + C) =
        Divisor.zeros hF (c i) + (C - Divisor.poles hF (c i)) +
          (j : ℕ) • Divisor.zeros hF x + (l - (j : ℕ)) • Divisor.poles hF x := by
      rw [Divisor.principal_mul, hpow, hsplit,
        ← Divisor.zeros_sub_poles hF (c i), ← Divisor.zeros_sub_poles hF x]
      module
    have hnonneg : (0 : Divisor k F) ≤
        Divisor.principal hF (c i * x ^ (j : ℕ)) + (l • Divisor.poles hF x + C) := by
      rw [hkey]
      refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
      · exact WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_zeros hF (c i))
      · exact sub_nonneg.mpr (hC i)
      · exact nsmul_nonneg
          (WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_zeros hF x)) _
      · exact nsmul_nonneg
          (WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF x)) _
    have hval : ((c i * x ^ (j : ℕ) : Fˣ) : F) = (c i : F) * (x : F) ^ (j : ℕ) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [← hval]
    exact (mem_riemannRochSpace_units_iff hF).mpr hnonneg
  have hfam := Transcendental.linearIndependent_mul_pow_fin hx hc (l + 1)
  have hv : LinearIndependent k fun p : ι × Fin (l + 1) ↦
      (⟨(c p.1 : F) * (x : F) ^ (p.2 : ℕ), hmem p⟩ :
        riemannRochSpace (l • Divisor.poles hF x + C)) := by
    refine LinearIndependent.of_comp (riemannRochSpace (l • Divisor.poles hF x + C)).subtype ?_
    simpa [Function.comp_def] using hfam
  have _ := finiteDimensional_riemannRochSpace hF (l • Divisor.poles hF x + C)
  have hcard := hv.fintype_card_le_finrank
  rw [Divisor.dim_def]
  simpa using hcard

/-- The pole divisor of a transcendental function has degree equal to the degree of the resulting
rational subfield.  This is the growth argument in Stichtenoth's proof of Theorem 1.4.11. -/
private theorem degree_poles_eq_finrank_adjoin (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) (hx0 : x ≠ 0) :
    Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) =
      (Module.finrank k⟮x⟯ F : ℤ) := by
  classical
  let _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  let b := Module.finBasis k⟮x⟯ F
  let c : Fin (Module.finrank k⟮x⟯ F) → Fˣ := fun i ↦ Units.mk0 (b i) (b.ne_zero i)
  have hcLI : LinearIndependent k⟮x⟯ fun i ↦ (c i : F) := by
    simpa only [c, Units.val_mk0] using b.linearIndependent
  let B : Divisor k F := Divisor.poles hF (Units.mk0 x hx0)
  let C : Divisor k F := ∑ i, Divisor.poles hF (c i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦
    WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF (c i))
  have hCi (i) : Divisor.poles hF (c i) ≤ C :=
    Finset.single_le_sum
      (fun j _ ↦ WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF (c j)))
      (Finset.mem_univ i)
  have hlower (n : ℕ) :
      Module.finrank k⟮x⟯ F * (n + 1) ≤
        Divisor.dim (n • B + C) := by
    simpa only [B, Fintype.card_fin] using
      Divisor.card_mul_succ_le_dim_nsmul_poles_add hF (Units.mk0 x hx0) hx c hcLI hCi n
  have hB : 0 ≤ B :=
    WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF _)
  have hBdeg : 0 ≤ Divisor.degree B := Divisor.degree_nonneg hB
  let d := (Divisor.degree B).toNat
  have hd : (d : ℤ) = Divisor.degree B := by
    exact Int.toNat_of_nonneg hBdeg
  have hCdeg : 0 ≤ Divisor.degree C := Divisor.degree_nonneg hC
  let e := (Divisor.degree C).toNat
  have he : (e : ℤ) = Divisor.degree C := Int.toNat_of_nonneg hCdeg
  let q := Module.finrank k (algebraicClosure k F)
  let n := e + q
  let E : Divisor k F := n • B + C
  have hE : 0 ≤ E := add_nonneg (nsmul_nonneg hB _) hC
  have hlow : Module.finrank k⟮x⟯ F * (n + 1) ≤ Divisor.dim E := by
    simpa only [E] using hlower n
  have hupp := Divisor.dim_le_degree_posPart_add_finrank hF E
  rw [WeilDivisor.posPart_eq_self_iff_isEffective.mpr
    (WeilDivisor.isEffective_iff_zero_le.mpr hE), Divisor.degree_add, map_nsmul] at hupp
  have hineq : ((Module.finrank k⟮x⟯ F * (n + 1) : ℕ) : ℤ) ≤
      (n : ℤ) * d + e + q := by
    calc
      ((Module.finrank k⟮x⟯ F * (n + 1) : ℕ) : ℤ) ≤ Divisor.dim E := by
        exact_mod_cast hlow
      _ ≤ (n : ℤ) * Divisor.degree B + Divisor.degree C + q := by
        simpa only [E, q, nsmul_eq_mul] using hupp
      _ = (n : ℤ) * d + e + q := by rw [← hd, ← he]
  have hle : Module.finrank k⟮x⟯ F ≤ d := by
    by_contra hnot
    have hgt : d < Module.finrank k⟮x⟯ F := Nat.lt_of_not_ge hnot
    have hgtZ : (d : ℤ) + 1 ≤ Module.finrank k⟮x⟯ F := by exact_mod_cast hgt
    dsimp only [n] at hineq
    push_cast at hineq
    have hfactor : 0 ≤ (e : ℤ) + q + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hgtZ hfactor
    nlinarith
  have hdegree_ge : (Module.finrank k⟮x⟯ F : ℤ) ≤ Divisor.degree B := by
    rw [← hd]
    exact_mod_cast hle
  let _ : FiniteDimensional k⟮x⁻¹⟯ F := by
    rw [IntermediateField.adjoin_simple_inv]
    exact hF.finiteDimensional_adjoin hx
  have hdegree_le := degree_zeros_le_finrank_adjoin hF (inv_ne_zero hx0)
  have hunit : Units.mk0 x⁻¹ (inv_ne_zero hx0) = (Units.mk0 x hx0)⁻¹ := by
    ext
    simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  rw [hunit, ← Divisor.poles_eq_zeros_inv hF (Units.mk0 x hx0),
    IntermediateField.adjoin_simple_inv] at hdegree_le
  exact le_antisymm (by simpa only [B] using hdegree_le) hdegree_ge

namespace Divisor

/-- **Stichtenoth, Theorem 1.4.11**: the pole divisor of a function `z` transcendental over `k`
has degree `[F : k(z)]`.  No exact-constant-field hypothesis is needed; correspondingly the
hypothesis is transcendence over `k`, not mere nonconstancy. -/
@[simp]
theorem degree_poles (hF : IsFunctionField k F) (z : Fˣ)
    (hz : ¬ IsAlgebraic k (z : F)) :
    degree (poles hF z) = (Module.finrank k⟮(z : F)⟯ F : ℤ) := by
  have hunit : Units.mk0 (z : F) (Units.ne_zero z) = z := by ext; rfl
  simpa only [hunit] using degree_poles_eq_finrank_adjoin hF hz (Units.ne_zero z)

/-- **Stichtenoth, Theorem 1.4.11**: the zero divisor of a function `z` transcendental over `k`
has degree `[F : k(z)]`.  No exact-constant-field hypothesis is needed; correspondingly the
hypothesis is transcendence over `k`, not mere nonconstancy. -/
@[simp]
theorem degree_zeros (hF : IsFunctionField k F) (z : Fˣ)
    (hz : ¬ IsAlgebraic k (z : F)) :
    degree (zeros hF z) = (Module.finrank k⟮(z : F)⟯ F : ℤ) := by
  have hzinv : ¬IsAlgebraic k (z⁻¹ : F) := fun h ↦ hz (IsAlgebraic.inv_iff.mp h)
  have hzinv' : ¬IsAlgebraic k ((z⁻¹ : Fˣ) : F) := by
    simpa only [Units.val_inv_eq_inv_val] using hzinv
  have h := degree_poles hF z⁻¹ hzinv'
  rw [poles_eq_zeros_inv, inv_inv, Units.val_inv_eq_inv_val,
    IntermediateField.adjoin_simple_inv] at h
  exact h

/-- **The product formula for an algebraic function field** (Stichtenoth, Theorem 1.4.11):
every principal divisor has degree zero. -/
@[simp]
theorem degree_principal (hF : IsFunctionField k F) (z : Fˣ) :
    degree (principal hF z) = 0 := by
  by_cases hz : IsAlgebraic k (z : F)
  · rw [principal_eq_zero_of_isAlgebraic hF hz, degree_zero]
  · rw [← zeros_sub_poles hF z, degree_sub, degree_zeros hF z hz, degree_poles hF z hz,
      sub_self]

/-- Residue-degree weighting agrees with the function-field divisor degree. -/
private theorem weightedDegree_placeDegree_eq_degree (D : Divisor k F) :
    WeilDivisor.weightedDegree (fun P : Place k F ↦ (P.degree : ℤ)) D = degree D := by
  rw [WeilDivisor.weightedDegree_apply, degree_apply]

end Divisor

namespace Place

/-- The function-field order system satisfies the weighted degree-zero condition required to
descend degree to divisor classes. -/
theorem isWeightedDegreeZero_orderSystem (hF : IsFunctionField k F) :
    (Place.orderSystem hF).IsWeightedDegreeZero fun P ↦ (P.degree : ℤ) := by
  intro g
  rw [Divisor.principalDivisor_eq, Divisor.weightedDegree_placeDegree_eq_degree,
    Divisor.degree_principal]

end Place

namespace Divisor

/-- The degree homomorphism on the divisor class group of an algebraic function field. -/
noncomputable def degreeClass (hF : IsFunctionField k F) :
    (Place.orderSystem hF).ClassGroup →+ ℤ :=
  (Place.orderSystem hF).weightedDegreeClass (fun P ↦ (P.degree : ℤ))
    (Place.isWeightedDegreeZero_orderSystem hF)

/-- The degree of a divisor class is the degree of any representative. -/
@[simp]
theorem degreeClass_divisorClass (hF : IsFunctionField k F) (D : Divisor k F) :
    degreeClass hF ((Place.orderSystem hF).divisorClass D) = degree D := by
  rw [degreeClass, (Place.orderSystem hF).weightedDegreeClass_divisorClass,
    weightedDegree_placeDegree_eq_degree]

/-- Linearly equivalent divisors have the same degree (Stichtenoth, Corollary 1.4.12(a)). -/
theorem degree_eq_of_linearlyEquivalent (hF : IsFunctionField k F) {A B : Divisor k F}
    (h : (Place.orderSystem hF).LinearlyEquivalent A B) : degree A = degree B := by
  simpa only [weightedDegree_placeDegree_eq_degree] using
    (Place.orderSystem hF).weightedDegree_eq_of_linearlyEquivalent
      (fun P ↦ (P.degree : ℤ)) (Place.isWeightedDegreeZero_orderSystem hF) h

end Divisor

/-- A divisor of negative degree has no nonzero functions in its Riemann–Roch space
(Stichtenoth, Corollary 1.4.12(b)). -/
theorem riemannRochSpace_eq_bot_of_degree_neg (hF : IsFunctionField k F) {D : Divisor k F}
    (hD : Divisor.degree D < 0) : riemannRochSpace D = ⊥ := by
  apply not_ne_iff.mp
  rw [riemannRochSpace_ne_bot_iff hF]
  rintro ⟨D', hD', hlin⟩
  have hmem : D' ∈ (Place.orderSystem hF).completeLinearSystem D :=
    (Place.orderSystem hF).mem_completeLinearSystem.mpr
      ⟨WeilDivisor.isEffective_iff_zero_le.mpr hD', hlin⟩
  have hempty := (Place.orderSystem hF).completeLinearSystem_eq_empty_of_weightedDegree_neg
    (fun P ↦ by positivity) (Place.isWeightedDegreeZero_orderSystem hF)
    (by simpa only [Divisor.weightedDegree_placeDegree_eq_degree] using hD)
  rw [hempty] at hmem
  exact hmem

/-- A divisor of negative degree has Riemann–Roch dimension zero. -/
theorem Divisor.dim_eq_zero_of_degree_neg (hF : IsFunctionField k F) {D : Divisor k F}
    (hD : Divisor.degree D < 0) : Divisor.dim D = 0 := by
  exact (Divisor.dim_eq_zero_iff_riemannRochSpace_eq_bot hF D).mpr
    (riemannRochSpace_eq_bot_of_degree_neg hF hD)

end TauCeti
