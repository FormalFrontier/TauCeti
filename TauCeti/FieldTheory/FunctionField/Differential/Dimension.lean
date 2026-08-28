/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Weil
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty

/-!
# The dimension of the space of Weil differentials

For an algebraic function field `F / k` with exact constant field this file computes the two
dimensions of the space of Weil differentials, Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., Lemma 1.5.7 and Proposition 1.5.9:

`dim_k Ω_F(D) = i(D)` and `dim_F Ω_F = 1`.

The first is formal.  By construction `Ω_F(D)` is the annihilator of `A_F(D) + F` in the dual of
`A_F`, so `Submodule.dualQuotEquivDualAnnihilator` identifies it with the dual of the cokernel
`A_F ⧸ (A_F(D) + F)`, whose dimension is the index of specialty
(`TauCeti.finrank_quotient_repartitionSpace`).  In particular `Ω_F ≠ 0`, because a divisor of
degree at most `-2` is special.

The second is the theorem with content.  Suppose `ω₁` and `ω₂` are Weil differentials, bounded by
`D₁` and `D₂`, with `ω₂` not a function multiple of `ω₁`.  For `x ∈ L(Dᵢ + B)` the differential
`x · ωᵢ` is bounded by `-B`, and the resulting `k`-linear map
`L(D₁ + B) × L(D₂ + B) → Ω_F(-B)` is injective, so

`ℓ(D₁ + B) + ℓ(D₂ + B) ≤ dim_k Ω_F(-B) = i(-B) = deg B - 1 + g`

for every `B > 0`, while Riemann's theorem bounds the left-hand side below by
`2 · deg B + deg D₁ + deg D₂ + 2 - 2g`.  Divisors of arbitrarily large degree exist, so for `B`
large the two bounds collide and no such `ω₂` exists.

## Main results

* `TauCeti.finrank_weilDifferentialFiltration`: **Stichtenoth, Lemma 1.5.7**,
  `dim_k Ω_F(D) = i(D)`, together with
  `TauCeti.finiteDimensional_weilDifferentialFiltration`.
* `TauCeti.finrank_weilDifferentialFiltration_zero`: `dim_k Ω_F(0) = g` (Remark 1.5.12).
* `TauCeti.weilDifferentialSpace_ne_bot`: there is a nonzero Weil differential.
* `TauCeti.exists_repartitionDualMul_eq`: every Weil differential is a function multiple of a
  fixed nonzero one.
* `TauCeti.finrank_weilDifferentialSpace`: **Stichtenoth, Proposition 1.5.9**, `dim_F Ω_F = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### `dim_k Ω_F(D) = i(D)` -/

/-- The Weil differentials bounded by a divisor form a finite-dimensional `k`-space: they are the
dual of the finite-dimensional cokernel `A_F ⧸ (A_F(D) + F)`. -/
theorem finiteDimensional_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    FiniteDimensional k ↥(weilDifferentialFiltration D) := by
  rw [weilDifferentialFiltration_eq_dualAnnihilator,
    submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf]
  exact Submodule.finite_dualAnnihilator_iff.mpr
    (finiteDimensional_quotient_repartitionSpace hF hex D)

/-- **Stichtenoth, Lemma 1.5.7**: `dim_k Ω_F(D) = i(D)`.  The Weil differentials bounded by `D`
are the annihilator of `A_F(D) + F`, hence the dual of the cokernel `A_F ⧸ (A_F(D) + F)`, whose
dimension is the index of specialty. -/
theorem finrank_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    (Module.finrank k ↥(weilDifferentialFiltration D) : ℤ) = Divisor.indexOfSpecialty D := by
  rw [← finrank_quotient_repartitionSpace hF hex D, weilDifferentialFiltration_eq_dualAnnihilator,
    submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf, Nat.cast_inj,
    ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **Stichtenoth, Remark 1.5.12**: the regular Weil differentials, those bounded by the zero
divisor, form a `k`-space of dimension the genus. -/
theorem finrank_weilDifferentialFiltration_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    Module.finrank k ↥(weilDifferentialFiltration (0 : Divisor k F)) = genus k F := by
  have h := finrank_weilDifferentialFiltration hF hex (0 : Divisor k F)
  rw [Divisor.indexOfSpecialty_def, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex,
    Divisor.degree_zero] at h
  omega

/-- The divisors bounding no nonzero Weil differential are exactly the nonspecial ones. -/
theorem weilDifferentialFiltration_eq_bot_iff_indexOfSpecialty_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    weilDifferentialFiltration D = ⊥ ↔ Divisor.indexOfSpecialty D = 0 :=
  (weilDifferentialFiltration_eq_bot_iff hF D).trans
    (adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff hF hex D)

/-- An algebraic function field has strictly positive divisors of arbitrarily large degree: a
multiple of a single place already works, because every place has degree at least one. -/
private theorem exists_pos_le_degree (hF : IsFunctionField k F) (c : ℤ) :
    ∃ B : Divisor k F, 0 < B ∧ c ≤ Divisor.degree B := by
  obtain ⟨P⟩ := Place.nonempty hF
  set n : ℕ := max 1 c.toNat
  have hP : (1 : ℤ) ≤ P.degree := by exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hdeg : Divisor.degree (n • WeilDivisor.ofPoint P) = (n : ℤ) * P.degree := by
    rw [map_nsmul, Divisor.degree_ofPoint, nsmul_eq_mul]
  have hle : (n : ℤ) ≤ (n : ℤ) * P.degree := le_mul_of_one_le_right (Int.natCast_nonneg n) hP
  have hcn : c ≤ (n : ℤ) := by
    have : c.toNat ≤ n := le_max_right _ _
    omega
  have hpos : (1 : ℤ) ≤ Divisor.degree (n • WeilDivisor.ofPoint P) :=
    hdeg ▸ le_trans (by exact_mod_cast le_max_left 1 c.toNat) hle
  have hnonneg : (0 : Divisor k F) ≤ n • WeilDivisor.ofPoint P :=
    nsmul_nonneg (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)) n
  refine ⟨n • WeilDivisor.ofPoint P, lt_of_le_of_ne hnonneg fun h ↦ ?_, hdeg ▸ hcn.trans hle⟩
  rw [← h, Divisor.degree_zero] at hpos
  omega

/-- **Stichtenoth, Lemma 1.5.7**, in the form that gets used: an algebraic function field has a
nonzero Weil differential.  A strictly positive divisor `B` of degree at least `2` has
`i(-B) = deg B - 1 + g > 0`, so `Ω_F(-B)` is already nonzero. -/
theorem weilDifferentialSpace_ne_bot (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) : weilDifferentialSpace k F ≠ ⊥ := by
  obtain ⟨B, hBpos, hBdeg⟩ := exists_pos_le_degree hF 2
  have hi : Divisor.indexOfSpecialty (-B) ≠ 0 := by
    rw [Divisor.indexOfSpecialty_def,
      Divisor.dim_eq_zero_of_lt_zero hF (neg_lt_zero.mpr hBpos), Divisor.degree_neg]
    omega
  have hne : weilDifferentialFiltration (-B) ≠ (⊥ : Submodule k _) := fun h ↦
    hi ((weilDifferentialFiltration_eq_bot_iff_indexOfSpecialty_eq_zero hF hex (-B)).mp h)
  exact fun h ↦ hne (le_bot_iff.mp (h ▸ weilDifferentialFiltration_le_weilDifferentialSpace (-B)))

/-! ### `dim_F Ω_F = 1` -/

/-- **Multiplying a Weil differential into a prescribed step of the filtration**: if `ω` is
bounded by `D` and the function `x` lies in `L(D + B)`, then `x · ω` is bounded by `-B`. -/
theorem repartitionDualMul_mem_weilDifferentialFiltration_neg (hF : IsFunctionField k F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} {D B : Divisor k F}
    (hω : ω ∈ weilDifferentialFiltration D) {x : F} (hx : x ∈ riemannRochSpace (D + B)) :
    repartitionDualMul hF x ω ∈ weilDifferentialFiltration (-B) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, (z : F) = x := ⟨Units.mk0 x hx0, rfl⟩
  have hle : -B ≤ D + Divisor.principal hF z := by
    refine sub_nonneg.mp ?_
    have h := (mem_riemannRochSpace_units_iff hF).mp hx
    have key : Divisor.principal hF z + (D + B) = D + Divisor.principal hF z - -B := by abel
    rwa [key] at h
  exact weilDifferentialFiltration_antitone hle
    ((repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mpr hω)

/-- The dimension estimate behind Proposition 1.5.9: if no nonzero pair of functions annihilates
the two Weil differentials `ω₁` and `ω₂`, then `(x₁, x₂) ↦ x₁ · ω₁ + x₂ · ω₂` embeds
`L(D₁ + B) × L(D₂ + B)` into `Ω_F(-B)`, whence `ℓ(D₁ + B) + ℓ(D₂ + B) ≤ i(-B)`. -/
private theorem dim_add_dim_le_indexOfSpecialty_neg (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω₁ ω₂ : Module.Dual k ↥(repartitionSpace k F)}
    {D₁ D₂ : Divisor k F} (h₁ : ω₁ ∈ weilDifferentialFiltration D₁)
    (h₂ : ω₂ ∈ weilDifferentialFiltration D₂)
    (hindep : ∀ x₁ x₂ : F,
      repartitionDualMul hF x₁ ω₁ + repartitionDualMul hF x₂ ω₂ = 0 → x₁ = 0 ∧ x₂ = 0)
    (B : Divisor k F) :
    (Divisor.dim (D₁ + B) : ℤ) + Divisor.dim (D₂ + B) ≤ Divisor.indexOfSpecialty (-B) := by
  have hfd₁ := finiteDimensional_riemannRochSpace hF (D₁ + B)
  have hfd₂ := finiteDimensional_riemannRochSpace hF (D₂ + B)
  have hfdΩ := finiteDimensional_weilDifferentialFiltration hF hex (-B)
  set ψ := LinearMap.coprod
    (((LinearMap.applyₗ ω₁).comp (repartitionDualMul hF).toLinearMap).comp
      (riemannRochSpace (D₁ + B)).subtype)
    (((LinearMap.applyₗ ω₂).comp (repartitionDualMul hF).toLinearMap).comp
      (riemannRochSpace (D₂ + B)).subtype)
  have hψ : ∀ p : ↥(riemannRochSpace (D₁ + B)) × ↥(riemannRochSpace (D₂ + B)),
      ψ p = repartitionDualMul hF (p.1 : F) ω₁ + repartitionDualMul hF (p.2 : F) ω₂ :=
    fun _ ↦ rfl
  have hmem : ∀ p, ψ p ∈ weilDifferentialFiltration (-B) := fun p ↦ by
    rw [hψ]
    exact Submodule.add_mem _
      (repartitionDualMul_mem_weilDifferentialFiltration_neg hF h₁ p.1.2)
      (repartitionDualMul_mem_weilDifferentialFiltration_neg hF h₂ p.2.2)
  have hinj : Function.Injective (ψ.codRestrict (weilDifferentialFiltration (-B)) hmem) := by
    intro p q hpq
    have h := congrArg Subtype.val hpq
    simp only [LinearMap.codRestrict_apply, hψ] at h
    have hzero : repartitionDualMul hF ((p.1 : F) - (q.1 : F)) ω₁
        + repartitionDualMul hF ((p.2 : F) - (q.2 : F)) ω₂ = 0 := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [sub_add_sub_comm, h, sub_self]
    obtain ⟨hp₁, hp₂⟩ := hindep _ _ hzero
    exact Prod.ext (Subtype.ext (sub_eq_zero.mp hp₁)) (Subtype.ext (sub_eq_zero.mp hp₂))
  have hbound := LinearMap.finrank_le_finrank_of_injective
    (f := ψ.codRestrict (weilDifferentialFiltration (-B)) hmem) hinj
  rw [Module.finrank_prod] at hbound
  have hΩ := finrank_weilDifferentialFiltration hF hex (-B)
  rw [Divisor.dim_def, Divisor.dim_def]
  omega

/-- **Stichtenoth, Proposition 1.5.9**, in element form: every Weil differential is a function
multiple of any fixed nonzero one. -/
theorem exists_repartitionDualMul_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω₁ ω₂ : Module.Dual k ↥(repartitionSpace k F)}
    (h₁ : ω₁ ∈ weilDifferentialSpace k F) (hω₁ : ω₁ ≠ 0)
    (h₂ : ω₂ ∈ weilDifferentialSpace k F) :
    ∃ c : F, repartitionDualMul hF c ω₁ = ω₂ := by
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨D₁, hD₁⟩ := mem_weilDifferentialSpace_iff.mp h₁
  obtain ⟨D₂, hD₂⟩ := mem_weilDifferentialSpace_iff.mp h₂
  -- `ω₁` and `ω₂` are independent over `F`: a relation with `x₂ ≠ 0` would exhibit `ω₂` as a
  -- multiple of `ω₁`, and one with `x₂ = 0` would make `ω₁` vanish.
  have hindep : ∀ x₁ x₂ : F,
      repartitionDualMul hF x₁ ω₁ + repartitionDualMul hF x₂ ω₂ = 0 → x₁ = 0 ∧ x₂ = 0 := by
    intro x₁ x₂ hx
    have hx₂ : x₂ = 0 := by
      by_contra hx₂
      refine hcon (-(x₂⁻¹ * x₁)) ?_
      have h := congrArg (repartitionDualMul hF x₂⁻¹) hx
      rw [map_add, map_zero, repartitionDualMul_repartitionDualMul,
        repartitionDualMul_repartitionDualMul, inv_mul_cancel₀ hx₂, map_one,
        Module.End.one_apply] at h
      rw [map_neg, LinearMap.neg_apply, eq_comm, eq_neg_iff_add_eq_zero, add_comm]
      exact h
    subst hx₂
    rw [map_zero, LinearMap.zero_apply, add_zero] at hx
    refine ⟨?_, rfl⟩
    by_contra hx₁
    refine hω₁ ?_
    have h := congrArg (repartitionDualMul hF x₁⁻¹) hx
    rwa [repartitionDualMul_repartitionDualMul, inv_mul_cancel₀ hx₁, map_one,
      Module.End.one_apply, map_zero] at h
  -- a divisor `B` of large degree makes the estimate and Riemann's theorem incompatible
  obtain ⟨B, hBpos, hBdeg⟩ := exists_pos_le_degree hF
    (3 * genus k F - Divisor.degree D₁ - Divisor.degree D₂)
  have hkey := dim_add_dim_le_indexOfSpecialty_neg hF hex hD₁ hD₂ hindep B
  have hr₁ := Divisor.degree_add_one_sub_genus_le_dim hF (D₁ + B)
  have hr₂ := Divisor.degree_add_one_sub_genus_le_dim hF (D₂ + B)
  rw [Divisor.indexOfSpecialty_def, Divisor.dim_eq_zero_of_lt_zero hF (neg_lt_zero.mpr hBpos),
    Divisor.degree_neg] at hkey
  rw [Divisor.degree_add] at hr₁ hr₂
  omega

/-- **Stichtenoth, Proposition 1.5.9**: the Weil differentials of an algebraic function field with
exact constant field form a one-dimensional vector space over the function field itself. -/
theorem finrank_weilDifferentialSpace (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    letI := weilDifferentialSpaceModule hF
    Module.finrank F ↥(weilDifferentialSpace k F) = 1 := by
  let := weilDifferentialSpaceModule hF
  obtain ⟨ω, hωmem, hω0⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  refine (finrank_eq_one_iff_of_nonzero' (V := ↥(weilDifferentialSpace k F)) ⟨ω, hωmem⟩
    (fun h ↦ hω0 (congrArg Subtype.val h))).mpr fun w ↦ ?_
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex hωmem hω0 w.2
  exact ⟨c, Subtype.ext ((coe_weilDifferentialSpaceModule_smul hF c _).trans hc)⟩

end TauCeti
