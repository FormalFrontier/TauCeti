/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The `q`-expansion of a rational diagonal slash

The coprime-prime Hecke operator has, besides its upper-triangular sum, a term obtained by
slashing by the rational matrix `diag(d, 1)`. The same real matrix already defines the
level-raising degeneracy map `V_d`; this file identifies the two constructions and transfers the
existing `q ↦ q ^ d` formula for `V_d` to the rational slash action.

With the arithmetic normalization of the slash action, the unnormalised diagonal term is

`f ∣[k] diag(d, 1) = d ^ (k - 1) V_d f`.

Consequently its `n`-th Fourier coefficient is `d ^ (k - 1) a_(n / d)` when `d ∣ n`, and zero
otherwise. This is the second term in the roadmap's recurrence
`a_n(T_p f) = a_(p n)(f) + χ(p) p ^ (k - 1) a_(n / p)(f)`; the factor `χ(p)` comes separately
from the diamond operator and is not part of the diagonal slash.

## Main results

* `TauCeti.map_natDiagGL_d_one_eq_scaleGL`: the rational diagonal representative maps to the real
  scaling matrix used by `V_d`.
* `TauCeti.slash_natDiagGL_d_one_eq_smul_levelRaise`: the rational diagonal slash is
  `d ^ (k - 1)` times the degeneracy map.
* `ModularForm.qExpansion_slash_natDiagGL_d_one` and
  `CuspForm.qExpansion_slash_natDiagGL_d_one`: the resulting power-series identities.
* The corresponding `_coeff` lemmas give the divisibility-conditional coefficient formula.

## Provenance

The pointwise prime case corresponds to the private theorem `slash_T_p_lower_eval` in the
AINTLIB `LeanModularForms` project
([`LeanModularForms/Modularforms/QExpansionSlash.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `112d12d95`, Apache-2.0, LeanModularForms contributors). No code is transcribed: the
result here is stated for every positive `d` and proved by identifying the rational matrix with
Tau Ceti's existing `scaleGL`, after which the degeneracy-map and `q`-expansion APIs supply the
formula without repeating AINTLIB's direct analytic argument.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.2--5.3.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Function HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {k : ℤ} {d : ℕ}

/-- The positive rational diagonal matrix `diag(d, 1)` maps to the real scaling matrix used to
define the degeneracy operator `V_d`. -/
lemma map_natDiagGL_d_one_eq_scaleGL [NeZero d] :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (natDiagGL 2 ![d, 1]) = scaleGL d := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, natDiagGL_coe 2 ![d, 1]
    (fun i ↦ by fin_cases i <;> simp [hd]), coe_scaleGL]
  fin_cases i <;> fin_cases j <;> simp

/-- Slashing by the rational matrix `diag(d, 1)` is the same as slashing by `scaleGL d`, its
real image. In particular it rescales the argument by `d` and contributes the arithmetic
normalizing factor `d ^ (k - 1)`. -/
lemma slash_natDiagGL_d_one_apply [NeZero d] (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ)) τ =
      (d : ℂ) ^ (k - 1) * f (scaleGL d • τ) := by
  rw [ModularForm.rat_slash, map_natDiagGL_d_one_eq_scaleGL, slash_scaleGL_apply]

/-- **The rational diagonal slash is a scaled degeneracy map.** The target group hypothesis is
exactly the one needed to package `τ ↦ f (dτ)` as `V_d f`; the equality itself is pointwise and
contains no group-theoretic argument. -/
lemma slash_natDiagGL_d_one_eq_smul_levelRaise {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}
    [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    ⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ) =
      (d : ℂ) ^ (k - 1) • ⇑(ModularForm.levelRaise d hle f) := by
  ext τ
  rw [slash_natDiagGL_d_one_apply, Pi.smul_apply, smul_eq_mul, ModularForm.levelRaise_apply]

/-- **The `q`-expansion of the rational diagonal slash.** Slashing by `diag(d, 1)` multiplies
the level-raised expansion by `d ^ (k - 1)`, so the result is
`d ^ (k - 1) • (qExpansion f).expand d`. -/
theorem _root_.ModularForm.qExpansion_slash_natDiagGL_d_one
    {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ)) =
      (d : ℂ) ^ (k - 1) • (qExpansion 1 f).expand d (NeZero.ne d) := by
  rw [slash_natDiagGL_d_one_eq_smul_levelRaise hle f,
    UpperHalfPlane.qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.levelRaise d hle f) one_pos h𝒢'),
    ModularForm.qExpansion_levelRaise h𝒢 h𝒢' hle]

/-- The coefficient form of `qExpansion_slash_natDiagGL_d_one`: the diagonal term contributes
`d ^ (k - 1) a_(n / d)` on indices divisible by `d`, and zero elsewhere. -/
theorem _root_.ModularForm.qExpansion_slash_natDiagGL_d_one_coeff
    {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) (n : ℕ) :
    (qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ))).coeff n =
      if d ∣ n then (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [ModularForm.qExpansion_slash_natDiagGL_d_one h𝒢 h𝒢' hle f, PowerSeries.coeff_smul,
    PowerSeries.coeff_expand]
  split_ifs <;> simp

/-- **The diagonal-slash coefficient formula at `Γ₁`.** The source form has level `M`, while
`Gamma1_map_le_conjAct_scaleGL` packages its scaled translate at level `dM`; this specialization
is the form needed by the coprime Hecke recurrence. -/
theorem _root_.ModularForm.qExpansion_slash_natDiagGL_d_one_coeff_Gamma1
    (M d : ℕ) [NeZero M] [NeZero d]
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ))).coeff n =
      if d ∣ n then (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (n / d) else 0 := by
  let _ : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  refine ModularForm.qExpansion_slash_natDiagGL_d_one_coeff ?_ ?_
    (Gamma1_map_le_conjAct_scaleGL M d) f n <;>
    simp [CongruenceSubgroup.strictPeriods_Gamma1]

/-- The rational diagonal-slash `q`-expansion for a cusp form. This is the modular-form theorem
applied to the canonical coercion, whose underlying function and `q`-expansion are unchanged. -/
theorem _root_.CuspForm.qExpansion_slash_natDiagGL_d_one
    {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ)) =
      (d : ℂ) ^ (k - 1) • (qExpansion 1 f).expand d (NeZero.ne d) :=
  ModularForm.qExpansion_slash_natDiagGL_d_one h𝒢 h𝒢' hle (f : ModularForm 𝒢 k)

/-- The coefficient form of `CuspForm.qExpansion_slash_natDiagGL_d_one`. -/
theorem _root_.CuspForm.qExpansion_slash_natDiagGL_d_one_coeff
    {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) (n : ℕ) :
    (qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ))).coeff n =
      if d ∣ n then (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (n / d) else 0 :=
  ModularForm.qExpansion_slash_natDiagGL_d_one_coeff h𝒢 h𝒢' hle
    (f : ModularForm 𝒢 k) n

/-- The diagonal-slash coefficient formula for a cusp form at `Γ₁`, obtained from the general
cusp-form identity using the standard level transport `Γ₁(dM) ≤ diag(d,1)⁻¹ Γ₁(M) diag(d,1)`. -/
theorem _root_.CuspForm.qExpansion_slash_natDiagGL_d_one_coeff_Gamma1
    (M d : ℕ) [NeZero M] [NeZero d]
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (⇑f ∣[k] (natDiagGL 2 ![d, 1] : GL (Fin 2) ℚ))).coeff n =
      if d ∣ n then (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (n / d) else 0 := by
  let _ : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  refine CuspForm.qExpansion_slash_natDiagGL_d_one_coeff ?_ ?_
    (Gamma1_map_le_conjAct_scaleGL M d) f n <;>
    simp [CongruenceSubgroup.strictPeriods_Gamma1]

end TauCeti

end
