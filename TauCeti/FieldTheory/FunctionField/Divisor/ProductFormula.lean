/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic
public import TauCeti.FieldTheory.IntermediateField.Adjoin.Inv
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

/-- The powers of a transcendental element are linearly independent over the base field. -/
private theorem linearIndependent_powers (hx : Transcendental k (x : F)) :
    LinearIndependent k fun n : ℕ ↦ x ^ n := by
  have hpow (n : ℕ) : ((Algebra.lmul k F x) ^ n) 1 = x ^ n := by
    rw [← map_pow]
    simp [Algebra.coe_lmul_eq_mul]
  have h := (Polynomial.linearIndependent_powers_iff_aeval (Algebra.lmul k F x) 1).mpr
    (fun p hp ↦ (transcendental_iff.mp hx) p (by
      have happly : (Polynomial.aeval (Algebra.lmul k F x) p) 1 =
          (Algebra.lmul k F (Polynomial.aeval x p)) 1 :=
        congrArg (fun f : Module.End k F ↦ f 1)
          (Polynomial.aeval_algHom_apply (Algebra.lmul k F) x p)
      rw [hp] at happly
      simpa [Algebra.coe_lmul_eq_mul] using happly.symm))
  simpa only [hpow] using h

/-- A coefficient of an effective function-field divisor is at most its degree. -/
private theorem coeff_le_degree_of_effective (hF : IsFunctionField k F) {D : Divisor k F}
    (hD : 0 ≤ D) (P : Place k F) : D.coeff P ≤ Divisor.degree D := by
  classical
  have hcoeff : 0 ≤ D.coeff P := by
    simpa using WeilDivisor.coeff_le_coeff hD P
  have hP : 1 ≤ (P.degree : ℤ) := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hsingle : (Finsupp.single P (D.coeff P) : Divisor k F) ≤ D := by
    rw [Finsupp.le_def]
    intro Q
    rw [Finsupp.single_apply]
    split
    · subst Q
      exact le_rfl
    · simpa only [Finsupp.zero_apply] using Finsupp.le_def.mp hD Q
  calc
    D.coeff P ≤ D.coeff P * P.degree := by nlinarith
    _ = Divisor.degree (Finsupp.single P (D.coeff P)) := (Divisor.degree_single P _).symm
    _ ≤ Divisor.degree D := Divisor.degree_le_of_le hsingle

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

/-- The order of a nonzero function at a place is bounded below by minus the degree of its pole
divisor, since that pole contributes its order to the degree. -/
private theorem neg_degree_poles_le_ord (hF : IsFunctionField k F) {u : F} (hu : u ≠ 0)
    (P : Place k F) :
    -Divisor.degree (Divisor.poles hF (Units.mk0 u hu)) ≤ P.ord u := by
  have hD : (0 : Divisor k F) ≤ Divisor.poles hF (Units.mk0 u hu) :=
    WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF _)
  have hcoeff := coeff_le_degree_of_effective hF hD P
  rw [Divisor.coeff_poles, Units.val_mk0] at hcoeff
  omega

/-- **The growth estimate** behind Stichtenoth's proof of Theorem 1.4.11: if the finitely many
functions `c i` are linearly independent over `k⟮x⟯`, integral over `k[x]`, and have no pole of
order exceeding `C`, then the products `c i * x ^ j` with `j ≤ n` are `#ι * (n + 1)` functions
lying in the Riemann–Roch space of `(C + n) • (x)∞` and linearly independent over `k`. -/
private theorem card_mul_succ_le_dim_smul_poles (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) (hx0 : x ≠ 0) {ι : Type*} [Fintype ι] {c : ι → F}
    (hcLI : LinearIndependent k⟮x⟯ c)
    (hcint : ∀ i, IsIntegral (Algebra.adjoin k ({x} : Set F)) (c i)) {C : ℕ}
    (hord : ∀ (i : ι) (P : Place k F), -(C : ℤ) ≤ P.ord (c i)) (n : ℕ) :
    Fintype.card ι * (n + 1) ≤
      Divisor.dim (((C + n : ℕ) : ℤ) • Divisor.poles hF (Units.mk0 x hx0)) := by
  classical
  let B : Divisor k F := Divisor.poles hF (Units.mk0 x hx0)
  let a : Fin (n + 1) → k⟮x⟯ := fun j ↦ ⟨x ^ (j : ℕ), by
    simpa using IntermediateField.pow_mem k⟮x⟯
      (IntermediateField.mem_adjoin_simple_self k x) (j : ℕ)⟩
  have haF : LinearIndependent k fun j : Fin (n + 1) ↦ x ^ (j : ℕ) :=
    (linearIndependent_powers hx).comp _ Fin.val_injective
  have ha : LinearIndependent k a := by
    rw [Fintype.linearIndependent_iff] at haF ⊢
    intro d hd j
    apply haF d _ j
    have hdF := congrArg (fun z : k⟮x⟯ ↦ (z : F)) hd
    simpa [a] using hdF
  have hfamily : LinearIndependent k fun p : ι × Fin (n + 1) ↦ c p.1 * x ^ (p.2 : ℕ) := by
    simpa only [a, Algebra.smul_def, IntermediateField.algebraMap_apply, mul_comm] using
      (linearIndependent_equiv' (Equiv.prodComm ι (Fin (n + 1)))
        (g := fun p : ι × Fin (n + 1) ↦ a p.2 • c p.1) rfl).mpr
        (linearIndependent_smul ha hcLI)
  let E : Divisor k F := (((C + n : ℕ) : ℤ) • B)
  have hmem (p : ι × Fin (n + 1)) : c p.1 * x ^ (p.2 : ℕ) ∈ riemannRochSpace E := by
    have hc0 := hcLI.ne_zero p.1
    have hxpow0 := pow_ne_zero (p.2 : ℕ) hx0
    rw [mem_riemannRochSpace_iff_neg_le_ord (mul_ne_zero hc0 hxpow0)]
    intro P
    by_cases hPx : P.ord x < 0
    · rw [P.ord_mul hc0 hxpow0, P.ord_pow]
      have hpoleCoeff : B.coeff P = -P.ord x := calc
        B.coeff P = -P.ord x ⊔ 0 := by
          simpa only [B, Units.val_mk0] using Divisor.coeff_poles hF (Units.mk0 x hx0) P
        _ = -P.ord x := by omega
      have hpole : B P = -P.ord x := hpoleCoeff
      have hj : p.2.val ≤ n := Nat.le_of_lt_succ p.2.isLt
      have hjZ : (p.2.val : ℤ) ≤ n := by exact_mod_cast hj
      have hnonneg : 0 ≤ (C : ℤ) + n - p.2.val := by omega
      have hd : P.ord x ≤ -1 := by omega
      have hmul : ((C : ℤ) + n - p.2.val) * P.ord x ≤
          -((C : ℤ) + n - p.2.val) :=
        by simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hd hnonneg
      calc
        -E.coeff P = ((C : ℤ) + n) * P.ord x := by
          simp only [E, WeilDivisor.coeff, Finsupp.smul_apply, smul_eq_mul, hpole]
          push_cast
          ring
        _ = ((C : ℤ) + n - p.2.val) * P.ord x + p.2.val * P.ord x := by ring
        _ ≤ -((C : ℤ) + n - p.2.val) + p.2.val * P.ord x :=
          by simpa only [add_comm] using add_le_add_right hmul (p.2.val * P.ord x)
        _ ≤ P.ord (c p.1) + p.2.val * P.ord x := by
          have := hord p.1 P
          omega
    · have hPx' : 0 ≤ P.ord x := by omega
      have hcP : c p.1 ∈ P.integers := P.mem_integers_of_isIntegral_adjoin
        (P.mem_integers_iff_ord_nonneg.mpr hPx') (hcint p.1)
      have hcP' := P.mem_integers_iff_ord_nonneg.mp hcP
      rw [P.ord_mul hc0 hxpow0, P.ord_pow]
      have hpoleCoeff : B.coeff P = 0 := calc
        B.coeff P = -P.ord x ⊔ 0 := by
          simpa only [B, Units.val_mk0] using Divisor.coeff_poles hF (Units.mk0 x hx0) P
        _ = 0 := by omega
      have hpole : B P = 0 := hpoleCoeff
      calc
        -E.coeff P = 0 := by
          simp only [E, WeilDivisor.coeff, Finsupp.smul_apply, smul_eq_mul, hpole, mul_zero,
            neg_zero]
        _ ≤ P.ord (c p.1) + (p.2.val : ℤ) * P.ord x :=
          add_nonneg hcP' (mul_nonneg (by positivity) hPx')
  let v : ι × Fin (n + 1) → riemannRochSpace E :=
    fun p ↦ ⟨c p.1 * x ^ (p.2 : ℕ), hmem p⟩
  have hcomp : (riemannRochSpace E).subtype ∘ v =
      fun p ↦ c p.1 * x ^ (p.2 : ℕ) := rfl
  have hv : LinearIndependent k v :=
    LinearIndependent.of_comp (riemannRochSpace E).subtype (hcomp.symm ▸ hfamily)
  let _ := finiteDimensional_riemannRochSpace hF E
  rw [Divisor.dim_def]
  simpa [E, B] using hv.fintype_card_le_finrank

/-- The pole divisor of a transcendental function has degree equal to the degree of the resulting
rational subfield.  This is the growth argument in Stichtenoth's proof of Theorem 1.4.11. -/
private theorem degree_poles_eq_finrank_adjoin (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) (hx0 : x ≠ 0) :
    Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) =
      (Module.finrank k⟮x⟯ F : ℤ) := by
  classical
  let _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  let _ : Algebra.IsAlgebraic k⟮x⟯ F := Algebra.IsAlgebraic.of_finite k⟮x⟯ F
  let _ : Algebra.IsAlgebraic (Algebra.adjoin k ({x} : Set F)) F :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin k ({x} : Set F)) k⟮x⟯ F
  let b := Module.finBasis k⟮x⟯ F
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples
    (Algebra.adjoin k ({x} : Set F)) (Finset.univ.image b)
  let c : Fin (Module.finrank k⟮x⟯ F) → F := fun i ↦
    algebraMap (Algebra.adjoin k ({x} : Set F)) F y * b i
  have hcint (i) : IsIntegral (Algebra.adjoin k ({x} : Set F)) (c i) :=
    by simpa only [c, Algebra.smul_def] using hy (b i) (by simp)
  have hyF : algebraMap (Algebra.adjoin k ({x} : Set F)) F y ≠ 0 := by
    simpa using hy0
  have hcLI : LinearIndependent k⟮x⟯ c := by
    have hinj : Function.Injective (LinearMap.mulLeft k⟮x⟯
        (algebraMap (Algebra.adjoin k ({x} : Set F)) F y)) :=
      fun u v huv ↦ mul_left_cancel₀ hyF huv
    -- Unfolding `c` exposes it as the image of the basis under injective left multiplication.
    change LinearIndependent k⟮x⟯ fun i ↦
      algebraMap (Algebra.adjoin k ({x} : Set F)) F y * b i
    exact b.linearIndependent.map' (LinearMap.mulLeft k⟮x⟯
      (algebraMap (Algebra.adjoin k ({x} : Set F)) F y))
      (LinearMap.ker_eq_bot_of_injective hinj)
  let B : Divisor k F := Divisor.poles hF (Units.mk0 x hx0)
  let C : ℕ := ∑ i, (Divisor.degree
    (Divisor.poles hF (Units.mk0 (c i) (hcLI.ne_zero i)))).toNat
  have hord (i) (P : Place k F) : -(C : ℤ) ≤ P.ord (c i) := by
    have hterm : (Divisor.degree
        (Divisor.poles hF (Units.mk0 (c i) (hcLI.ne_zero i)))).toNat ≤ C := by
      simpa only [C] using Finset.single_le_sum
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin (Module.finrank k⟮x⟯ F)))) ↦
          Nat.zero_le (Divisor.degree
            (Divisor.poles hF (Units.mk0 (c j) (hcLI.ne_zero j)))).toNat)
        (Finset.mem_univ i)
    have hpole := neg_degree_poles_le_ord hF (hcLI.ne_zero i) P
    omega
  have hlower (n : ℕ) :
      Module.finrank k⟮x⟯ F * (n + 1) ≤
        Divisor.dim (((C + n : ℕ) : ℤ) • B) := by
    simpa only [B, Fintype.card_fin] using
      card_mul_succ_le_dim_smul_poles hF hx hx0 hcLI hcint hord n
  have hB : 0 ≤ B :=
    WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF _)
  have hBdeg : 0 ≤ Divisor.degree B := Divisor.degree_nonneg hB
  let d := (Divisor.degree B).toNat
  have hd : (d : ℤ) = Divisor.degree B := by
    exact Int.toNat_of_nonneg hBdeg
  let q := Module.finrank k (algebraicClosure k F)
  let n := C * d + q
  let E : Divisor k F := (((C + n : ℕ) : ℤ) • B)
  have hE : 0 ≤ E := by
    exact smul_nonneg (by positivity) hB
  have hlow : Module.finrank k⟮x⟯ F * (n + 1) ≤ Divisor.dim E := by
    simpa only [E] using hlower n
  have hupp := Divisor.dim_le_degree_posPart_add_finrank hF E
  rw [WeilDivisor.posPart_eq_self_iff_isEffective.mpr
    (WeilDivisor.isEffective_iff_zero_le.mpr hE), Divisor.degree_zsmul] at hupp
  have hineq : ((Module.finrank k⟮x⟯ F * (n + 1) : ℕ) : ℤ) ≤
      ((C + n : ℕ) : ℤ) * d + q := by
    calc
      ((Module.finrank k⟮x⟯ F * (n + 1) : ℕ) : ℤ) ≤ Divisor.dim E := by
        exact_mod_cast hlow
      _ ≤ ((C + n : ℕ) : ℤ) * Divisor.degree B + q := by
        simpa only [E, q] using hupp
      _ = ((C + n : ℕ) : ℤ) * d + q := by rw [← hd]
  have hle : Module.finrank k⟮x⟯ F ≤ d := by
    by_contra hnot
    have hgt : d < Module.finrank k⟮x⟯ F := Nat.lt_of_not_ge hnot
    have hgtZ : (d : ℤ) + 1 ≤ Module.finrank k⟮x⟯ F := by exact_mod_cast hgt
    dsimp only [n] at hineq
    push_cast at hineq
    have hfactor : 0 ≤ (C : ℤ) * d + q + 1 := by positivity
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
