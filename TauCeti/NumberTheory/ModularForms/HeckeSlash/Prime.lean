/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.DoubleCoset

/-!
# The classical `Tₚ` on `M_k(Γ₁(N))` and `S_k(Γ₁(N))`, at every prime

`HeckeSlash/UpperTri/DoubleCoset.lean` identifies the Hecke operator of the double coset
`Γ₁(N) · diag(1, p) · Γ₁(N)` with the upper-triangular sum `∑_{b < p} f ∣[k] !![1, b; 0, p]`,
but only for `p ∣ N`, because only there do the `p` upper-triangular matrices exhaust the coset.
With the good-prime decomposition of `HeckeRing/GL2/Gamma1/CoprimeCosets.lean` in hand, this file
completes the identification at every prime:

`Tₚ f = ∑_{b < p} f ∣[k] !![1, b; 0, p]  +  (⟨p⟩ f) ∣[k] !![p, 0; 0, 1]`.

**One formula, both cases.** The extra term is not conditional. At `p ∤ N` it is the slash by the
twisted representative `σ · diag(p, 1)`, and slashing by `σ ∈ Γ₀(N)` — an element with lower-right
entry `p` — is by definition the diamond operator `⟨p⟩`
(`slash_mapGL_gamma0Twist_eq_diamondOpNat`). At `p ∣ N`
the zero-extended `⟨p⟩` of `DiamondOperators.lean` *vanishes*, so the term disappears and the
formula degenerates to the `p ∣ N` statement already proved. That is exactly the uniformity the
ModularForms roadmap asks for: `Tₚ` is one operator, defined for every `p`, with the modern `Uₚ`
recovered as the `p ∣ N` case and not introduced separately.

⚠ The twist is essential. Over `Γ₁(N)` the untwisted `f ∣[k] !![p, 0; 0, 1]` is *not* a term
of the coset sum. The matrix `σ · diag(p, 1)` is the missing right-coset representative, and
`f ∣[k] (σ · diag(p, 1)) = (⟨p⟩ f) ∣[k] diag(p, 1)`. On a form of nebentypus `χ` the diamond
acts by the scalar `χ(p)`, which is where the classical factor `χ(p)` in
`aₘ(Tₚ f) = a_{m p}(f) + χ(p) p^{k−1} a_{m/p}(f)` comes from
(`coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace`); the two spellings
agree exactly when `χ(p) = 1`.

## Main results

* `HeckeRing.GL2.heckeSlashSum_diagCosetGamma1_of_coprime`: the slash sum of the double coset at
  a prime `p ∤ N`, over the `p + 1` representatives.
* `HeckeRing.GL2.coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime`,
  `HeckeRing.GL2.coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime`: **the classical `Tₚ`,
  at every prime**, on `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `HeckeRing.GL2.coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace` and
  its cusp-form counterpart: the same formula on a nebentypus space, with the diamond replaced by
  the scalar `χ(p)`.

## Provenance

No code is transcribed. The shape of the formula is that of `heckeT_p_fun` in the AINTLIB
`LeanModularForms` project (`HeckeRIngs/GL2/HeckeT_p.lean`, Chris Birkbeck, Apache-2.0), whose
extra term likewise carries the diamond operator; the derivation here goes through the abstract
double coset and this repository's own coset decomposition rather than through a bespoke
definition of the operator.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.1 and §5.2–5.3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)

variable [NeZero N]

/-- **The slash sum of the `Tₚ` double coset at a prime `p ∤ N`.** This is
`heckeSlashSum_coe_eq_sum_of_rightCosets` fed with the `p + 1`-fold decomposition of
`HeckeRing/GL2/Gamma1/CoprimeCosets.lean`; slash-invariance of `f`, the one hypothesis that lemma
needs, is carried by the form class. -/
theorem heckeSlashSum_diagCosetGamma1_of_coprime (hp : p.Prime) (h : Nat.Coprime p N)
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    heckeSlashSum k (diagCosetGamma1 N p) ⇑f =
      heckeSlashUpperTri k p ⇑f + ⇑f ∣[k] (mapGL ℚ (gamma0Twist N p h) * scaleRep p) := by
  rw [heckeSlashSum_coe_eq_sum_of_rightCosets k (diagCosetGamma1 N p)
      (primeRep (gamma0Twist N p h) p)
      (doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets_of_prime hp
        (gamma0Twist_apply_one_zero h) (gamma0Twist_apply_one_one h))
      (op_primeRep_smul_injective (G := Gamma1 N) hp.one_lt (gamma0Twist_apply_one_zero h)
        (gamma0Twist_apply_one_one h)) f,
    Fintype.sum_option, heckeSlashUpperTri_def]
  simp only [primeRep_some, primeRep_none]
  exact add_comm _ _

/-- **The classical `Tₚ` on `M_k(Γ₁(N))`, at every prime.** The Hecke operator of the double
coset `Γ₁(N) · diag(1, p) · Γ₁(N)` is

`Tₚ f = ∑_{b < p} f ∣[k] !![1, b; 0, p] + (⟨p⟩ f) ∣[k] !![p, 0; 0, 1]`,

with **no** case split on whether `p` divides the level: at `p ∣ N` the zero-extended diamond
`⟨p⟩` vanishes and the formula reduces to the upper-triangular sum, the operator modern papers
write `Uₚ`. -/
theorem coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime (hp : p.Prime)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f) =
      heckeSlashUpperTri k p ⇑f + ⇑(diamondOpNat k p f) ∣[k] scaleRep p := by
  rw [coe_heckeSlashGamma1ModularFormEnd]
  by_cases h : Nat.Coprime p N
  · rw [heckeSlashSum_diagCosetGamma1_of_coprime k hp h f, SlashAction.slash_mul,
      slash_mapGL_gamma0Twist_eq_diamondOpNat k h f]
  · have hpN : p ∣ N := hp.dvd_iff_not_coprime.mpr h
    rw [heckeSlashSum_diagCosetGamma1 k hpN f, diamondOpNat_of_not_coprime k h]
    simp

/-- **The classical `Tₚ` on `S_k(Γ₁(N))`, at every prime** — the same formula, with the
cusp-form diamond operator. -/
theorem coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime (hp : p.Prime)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f) =
      heckeSlashUpperTri k p ⇑f + ⇑(diamondOpCuspNat k p f) ∣[k] scaleRep p := by
  rw [coe_heckeSlashGamma1CuspFormEnd]
  by_cases h : Nat.Coprime p N
  · rw [heckeSlashSum_diagCosetGamma1_of_coprime k hp h f, SlashAction.slash_mul,
      slash_mapGL_gamma0Twist_eq_diamondOpCuspNat k h f]
  · have hpN : p ∣ N := hp.dvd_iff_not_coprime.mpr h
    rw [heckeSlashSum_diagCosetGamma1 k hpN f, diamondOpCuspNat_of_not_coprime k h]
    simp

/-- **`Tₚ` on a nebentypus space `M_k(N, χ)`, at a prime `p ∤ N`.** The diamond acts by the
scalar `χ(p)`, giving Diamond–Shurman's

`Tₚ f = ∑_{b < p} f ∣[k] !![1, b; 0, p] + χ(p) · f ∣[k] !![p, 0; 0, 1]`,

the slash-level form of the coefficient recurrence
`aₘ(Tₚ f) = a_{m p}(f) + χ(p) p^{k−1} a_{m/p}(f)`. -/
theorem coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace (hp : p.Prime)
    (h : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    ⇑(heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f) =
      heckeSlashUpperTri k p ⇑f + (χ (ZMod.unitOfCoprime p h) : ℂ) • (⇑f ∣[k] scaleRep p) := by
  rw [coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime k hp f,
    diamondOpNat_of_coprime k h, diamondOp_apply_of_mem_modFormCharSpace k χ _ hf]
  congr 1
  exact ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p) ⇑f _

/-- **`Tₚ` on a nebentypus space `S_k(N, χ)`, at a prime `p ∤ N`.** -/
theorem coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace (hp : p.Prime)
    (h : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    ⇑(heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f) =
      heckeSlashUpperTri k p ⇑f + (χ (ZMod.unitOfCoprime p h) : ℂ) • (⇑f ∣[k] scaleRep p) := by
  rw [coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp f,
    diamondOpCuspNat_of_coprime k h, diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf]
  congr 1
  exact ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p) ⇑f _

end HeckeRing.GL2

end
