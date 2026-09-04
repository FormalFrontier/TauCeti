/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Prime
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The Fourier-coefficient recurrence for `Tₚ`, at every prime

`HeckeSlash/Prime.lean` writes the Hecke operator of the double coset `Γ₁(N) · diag(1, p) · Γ₁(N)`
as a sum of slashes,

`Tₚ f = ∑_{b < p} f ∣[k] !![1, b; 0, p]  +  (⟨p⟩ f) ∣[k] !![p, 0; 0, 1]`,

and the two `q`-expansion halves are already computed elsewhere: the upper-triangular sum reads
off the coefficients of `f` along `p ℕ` (`UpperTri/QExpansion.lean`) and the rational diagonal
slash is `p ^ (k - 1)` times a level raise (`Diagonal/QExpansion.lean`). This file adds them,
turning the slash-level identity into Diamond–Shurman's recurrence on Fourier coefficients:

`aₘ(Tₚ f) = a_{p m}(f) + p^{k−1} a_{m/p}(⟨p⟩ f)`,

and on a nebentypus space `M_k(N, χ)` with `p ∤ N`, where the diamond acts by the scalar `χ(p)`,

`aₘ(Tₚ f) = a_{p m}(f) + χ(p) p^{k−1} a_{m/p}(f)`.

**One formula, both cases.** As at the level of slashes, there is no case split on whether `p`
divides the level: `a_{m/p}` is read as an explicit `if p ∣ m`, and at `p ∣ N` the zero-extended
diamond `⟨p⟩` of `DiamondOperators.lean` vanishes, so the recurrence degenerates to
`aₘ(Tₚ f) = a_{p m}(f)` — the operator modern papers write `Uₚ`. Following Miyake,
Diamond–Shurman and Shimura, `Uₚ` is not a second operator, only this case of `Tₚ`.

The `Nat` division in `a_{m/p}` is guarded by that `if`: without it, `m / p` would silently
round down at indices `p ∤ m` and name a coefficient the recurrence does not contain.

## Main results

* `HeckeRing.GL2.qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime` and
  its cusp-form counterpart: **the recurrence**, uniformly at every prime.
* `qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace`
  and its cusp-form counterpart: the recurrence on a nebentypus space at a good prime, with
  `χ(p)` in place of the diamond.
* `HeckeRing.GL2.qExpansion_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime`: the same
  identity between power series, the diamond term appearing as a `PowerSeries.expand`.
* `HeckeRing.GL2.qExpansion_coeff_one_heckeSlashGamma1ModularFormEnd_diagCosetGamma1`:
  `a₁(Tₚ f) = a_p(f)`, and
  `HeckeRing.GL2.eq_qExpansion_coeff_of_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_eq_smul`:
  **the Hecke eigenvalue of a normalized eigenvector is `a_p`**.

## Provenance

No code is transcribed. The Fourier-side statements of the AINTLIB `LeanModularForms` project
live in `HeckeRIngs/GL2/FourierHecke.lean` (<https://github.com/CBirkbeck/AINTLIB>, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck) and carry the hypotheses
`f ∈ modFormCharSpace k χ` and `Nat.Coprime p N`; those hypotheses are kept here rather than
cleaned away. The derivation itself goes through this repository's own double-coset operator
(`HeckeSlash/Prime.lean`) and the additivity of the `q`-expansion, not through a bespoke
definition of `Tₚ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.2 and equations (5.3)--(5.4).
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
* T. Miyake, *Modular forms*, §4.5, Lemma 4.5.7: `T(n)` is defined for every `n ≥ 1` with the
  nebentypus extended by `χ(d) = 0` at `(d, N) > 1`, which is the convention under which the
  `p ∣ N` case below is `Tₚ` itself rather than a separate operator.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
  HeckeRing.GLn PowerSeries

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)

variable [NeZero N]

-- `NeZero N` is not needed here: the level-raise coefficient identity this closes with
-- (`ModularForm.qExpansion_slash_natDiagGL_d_one_coeff_Gamma1`) asks only for `NeZero p`.
omit [NeZero N] in
private theorem qExpansion_coeff_add_slash_scaleRep [NeZero p]
    {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k]
    (f : F) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hSum : AnalyticAt ℂ (cuspFunction 1
      (heckeSlashUpperTri k p ⇑f + ⇑g ∣[k] (scaleRep p : GL (Fin 2) ℚ))) 0) (m : ℕ) :
    (qExpansion 1 (heckeSlashUpperTri k p ⇑f + ⇑g ∣[k] (scaleRep p : GL (Fin 2) ℚ))).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (k - 1) * (qExpansion 1 g).coeff (m / p) else 0 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hΓ : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods :=
    TauCeti.one_mem_strictPeriods_Gamma1_map N
  let _ : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨((Gamma1 N).map (mapGL ℝ)).isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hU : AnalyticAt ℂ (cuspFunction 1 (heckeSlashUpperTri k p ⇑f)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
      (periodic_heckeSlashUpperTri k p
        (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ))
      (mdifferentiable_heckeSlashUpperTri k p (ModularFormClass.holo f))
      (isBoundedAtImInfty_heckeSlashUpperTri k p (ModularFormClass.bdd_at_infty f))
  have hD : AnalyticAt ℂ (cuspFunction 1 (⇑g ∣[k] (scaleRep p : GL (Fin 2) ℚ))) 0 := by
    have hsub := hSum.sub hU
    rw [← cuspFunction_sub hSum.continuousAt hU.continuousAt] at hsub
    simpa only [add_sub_cancel_left] using hsub
  rw [UpperHalfPlane.qExpansion_add hU hD, map_add]
  congr 1
  · exact qExpansion_coeff_heckeSlashUpperTri' k p hΓ hp f m
  · rw [scaleRep_def]
    exact ModularForm.qExpansion_slash_natDiagGL_d_one_coeff_Gamma1 N p
      g m

/-- **The Fourier-coefficient recurrence for `Tₚ` on `M_k(Γ₁(N))`, at every prime.**

`aₘ(Tₚ f) = a_{p m}(f) + p^{k−1} a_{m/p}(⟨p⟩ f)`,

where the second term is present only when `p ∣ m`. There is no case split on the level: at
`p ∣ N` the zero-extended diamond `⟨p⟩` vanishes and the recurrence degenerates to
`aₘ(Tₚ f) = a_{p m}(f)`. -/
theorem qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime
    (hp : p.Prime) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (k - 1) * (qExpansion 1 (diamondOpNat k p f)).coeff (m / p)
        else 0 := by
  have _ : NeZero p := ⟨hp.ne_zero⟩
  have hΓ : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods :=
    TauCeti.one_mem_strictPeriods_Gamma1_map N
  have hSum := ModularFormClass.analyticAt_cuspFunction_zero
    (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f) one_pos hΓ
  rw [coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f] at hSum
  rw [coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f]
  exact qExpansion_coeff_add_slash_scaleRep k f _ hSum m

/-- **The Fourier-coefficient recurrence for `Tₚ` on `S_k(Γ₁(N))`, at every prime** — the same
formula, with the cusp-form diamond operator. -/
theorem qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime
    (hp : p.Prime) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (k - 1) * (qExpansion 1 (diamondOpCuspNat k p f)).coeff (m / p)
        else 0 := by
  have _ : NeZero p := ⟨hp.ne_zero⟩
  have hΓ : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods :=
    TauCeti.one_mem_strictPeriods_Gamma1_map N
  have hSum := ModularFormClass.analyticAt_cuspFunction_zero
    (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f) one_pos hΓ
  rw [coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f] at hSum
  rw [coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f]
  exact qExpansion_coeff_add_slash_scaleRep k f
    (diamondOpCuspNat k p f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hSum m

/-- **Diamond–Shurman's recurrence on a nebentypus space `M_k(N, χ)` at a good prime.**
For `p ∤ N` the diamond acts by the scalar `χ(p)`, so

`aₘ(Tₚ f) = a_{p m}(f) + χ(p) p^{k−1} a_{m/p}(f)`. -/
theorem qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace
    (hp : p.Prime) (h : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (χ (ZMod.unitOfCoprime p h) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f).coeff (m / p) else 0 := by
  rw [qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f m,
    diamondOpNat_of_coprime k h, diamondOp_apply_of_mem_modFormCharSpace k χ _ hf,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
  refine congrArg _ (if_congr Iff.rfl ?_ rfl)
  rw [map_smul, smul_eq_mul]
  ring

/-- **Diamond–Shurman's recurrence on a nebentypus space `S_k(N, χ)` at a good prime.** -/
theorem qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace
    (hp : p.Prime) (h : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (χ (ZMod.unitOfCoprime p h) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f).coeff (m / p) else 0 := by
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f m,
    diamondOpCuspNat_of_coprime k h, diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
  refine congrArg _ (if_congr Iff.rfl ?_ rfl)
  rw [map_smul, smul_eq_mul]
  ring

/-- **The recurrence as an identity of power series.** The `q`-expansion of `Tₚ f` is the
subseries of `f` along `p ℕ`, reindexed, plus `p^{k−1}` times the `p`-fold expansion of the
`q`-expansion of `⟨p⟩ f`. -/
theorem qExpansion_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime
    (hp : p.Prime) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion 1 (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f) =
      (PowerSeries.mk fun m ↦ (qExpansion 1 f).coeff (p * m)) +
        (p : ℂ) ^ (k - 1) • (qExpansion 1 (diamondOpNat k p f)).expand p hp.ne_zero :=
  PowerSeries.ext fun m ↦ by
    rw [qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f m,
      map_add, PowerSeries.coeff_mk, map_smul, PowerSeries.coeff_expand, smul_eq_mul]
    split_ifs <;> simp

/-- **The recurrence as an identity of power series, on cusp forms.** -/
theorem qExpansion_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime
    (hp : p.Prime) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f) =
      (PowerSeries.mk fun m ↦ (qExpansion 1 f).coeff (p * m)) +
        (p : ℂ) ^ (k - 1) • (qExpansion 1 (diamondOpCuspNat k p f)).expand p hp.ne_zero :=
  PowerSeries.ext fun m ↦ by
    rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f m,
      map_add, PowerSeries.coeff_mk, map_smul, PowerSeries.coeff_expand, smul_eq_mul]
    split_ifs <;> simp

/-- **The first coefficient of `Tₚ f` is the `p`-th coefficient of `f`**, at every prime and
every level: `p ∤ 1`, so the diamond term of the recurrence is absent. This is what turns a
Hecke eigenvalue into a Fourier coefficient. -/
theorem qExpansion_coeff_one_heckeSlashGamma1ModularFormEnd_diagCosetGamma1
    (hp : p.Prime) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (qExpansion 1 (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f)).coeff 1 =
      (qExpansion 1 f).coeff p := by
  have h1 : ¬ p ∣ 1 := fun h ↦ hp.ne_one (Nat.dvd_one.mp h)
  rw [qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f 1, mul_one]
  simp [h1]

/-- **The first coefficient of `Tₚ f` on cusp forms.** -/
theorem qExpansion_coeff_one_heckeSlashGamma1CuspFormEnd_diagCosetGamma1
    (hp : p.Prime) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f)).coeff 1 =
      (qExpansion 1 f).coeff p := by
  have h1 : ¬ p ∣ 1 := fun h ↦ hp.ne_one (Nat.dvd_one.mp h)
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f 1, mul_one]
  simp [h1]

/-- **The Hecke eigenvalue of a normalized eigenvector is its `p`-th Fourier coefficient.**
If `Tₚ f = c f` and `f` is normalized (`a₁(f) = 1`), then `c = a_p(f)`. This is the identity
that lets eigenvalue systems be read off `q`-expansions. -/
theorem eq_qExpansion_coeff_of_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_eq_smul
    (hp : p.Prime) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} {c : ℂ}
    (hc : heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f = c • f)
    (h1 : (qExpansion 1 f).coeff 1 = 1) : c = (qExpansion 1 f).coeff p := by
  have h := qExpansion_coeff_one_heckeSlashGamma1ModularFormEnd_diagCosetGamma1 k hp f
  rwa [hc, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    map_smul, smul_eq_mul, h1, mul_one] at h

/-- **The Hecke eigenvalue of a normalized eigenvector, on cusp forms.** -/
theorem eq_qExpansion_coeff_of_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_eq_smul
    (hp : p.Prime) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {c : ℂ}
    (hc : heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f = c • f)
    (h1 : (qExpansion 1 f).coeff 1 = 1) : c = (qExpansion 1 f).coeff p := by
  have h := qExpansion_coeff_one_heckeSlashGamma1CuspFormEnd_diagCosetGamma1 k hp f
  rwa [hc, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    map_smul, smul_eq_mul, h1, mul_one] at h

end HeckeRing.GL2

end
