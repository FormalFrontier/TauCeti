/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.ModularForm

/-!
# The normalisation lemma: the double coset of `diag(1, p)` is the classical `Uₚ`

Two Hecke operators on `M_k(Γ₁(N))` have been built independently. `HeckeSlash/Gamma1.lean`
attaches one to an **arbitrary double coset** of the Hecke triple `(Γ₁(N), Δ₀(N))`, by slashing
against representatives of the coset and summing; `UpperTri/ModularForm.lean` builds the
**classical** operator at `p ∣ N`, the sum of the slashes by `!![1, b; 0, p]` for `b < p`, and
computes its effect on `q`-expansions. Nothing so far connects them, and until something does,
"the Hecke operator" names two objects.

This file identifies them, which is the roadmap's flagged *normalisation lemma*: for `p ∣ N`,

`heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) = heckeSlashUpperTriModularFormEnd k hpN`,

and likewise on cusp forms. The abstract operator therefore satisfies the classical recurrence
`aₘ(Tₚ f) = a_{p m}(f)` and preserves each nebentypus space, both recorded below.

## How the two are matched

`HeckeSlash/Independence.lean` already shows that the abstract operator is the sum of the slashes
over **any** decomposition of the double coset into right cosets
(`heckeSlashSum_coe_eq_sum_of_rightCosets`); what was missing was a decomposition to feed it. That
is `HeckeRing/GL2/Gamma1/UpperTriCosets.lean`: at `p ∣ N` the `p` cosets
`Γ₁(N) · !![1, b; 0, p]` cover `Γ₁(N) · diag(1, p) · Γ₁(N)` and are pairwise distinct. Feeding
those in turns the abstract sum into `heckeSlashUpperTri`, and the two bundled endomorphisms
then agree because both are that function on the underlying `ℍ → ℂ`.

## Why `p ∣ N` and no primality

`p ∣ N` is what makes the `p` upper-triangular representatives exhaust the coset; for `p ∤ N` and
`p` prime there is one further coset and the identification below is false as stated. No
primality is needed anywhere: at `p ∣ N` the count is `p` for every `p`, prime or not.

Following Miyake, Diamond–Shurman and Shimura, no separate `Uₚ` is introduced — this *is* `Tₚ` at
`p ∣ N`, and the identification proved here is what lets literature stated in either vocabulary be
consumed.

## Main results

* `HeckeRing.GL2.heckeSlashSum_diagCosetGamma1`: on underlying functions, the abstract slash sum
  of `diagCosetGamma1 N p` is `heckeSlashUpperTri k p`.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diagCosetGamma1`,
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_diagCosetGamma1`: **the normalisation lemma**, on
  `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `HeckeRing.GL2.qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1`,
  `HeckeRing.GL2.qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1`: the abstract
  operator sends `aₘ` to `a_{p m}`.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diagCosetGamma1_mem_modFormCharSpace`,
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_diagCosetGamma1_mem_cuspFormCharSpace`: it preserves
  the nebentypus.

## Provenance

No code is transcribed. The identification is the normalisation lemma the ModularForms roadmap
asks Layer 2(b) to keep; on the AINTLIB side (`LeanModularForms`, Chris Birkbeck, Apache-2.0) the
`p ∣ N` operator is the `heckeT_p_divN` branch of `heckeT_p_all`
(`LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean`), and the statement below is what ties that
branch to the abstract double-coset ring.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.2, Proposition 5.2.1.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- A divisor of a nonzero level is positive: the side condition the coset decomposition asks
for, which `p ∣ N` and `NeZero N` already supply. -/
private lemma pos_of_dvd (hpN : p ∣ N) : 0 < p :=
  Nat.pos_of_ne_zero fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))

/-- **The abstract slash sum of `diag(1, p)` is the classical upper-triangular sum**, for
`p ∣ N`. This is `heckeSlashSum_coe_eq_sum_of_rightCosets` fed with the decomposition of
`HeckeRing/GL2/Gamma1/UpperTriCosets.lean`; slash-invariance of `f`, the one hypothesis that
lemma needs, is carried by the form class. -/
theorem heckeSlashSum_diagCosetGamma1 (hpN : p ∣ N) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    heckeSlashSum k (diagCosetGamma1 N p) ⇑f = heckeSlashUpperTri k p ⇑f :=
  (heckeSlashSum_coe_eq_sum_of_rightCosets k (diagCosetGamma1 N p) (upperTriRep p)
    (doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets (pos_of_dvd hpN) hpN)
    op_upperTriRep_smul_injective f).trans (heckeSlashUpperTri_def k p ⇑f).symm

/-- **The normalisation lemma on `M_k(Γ₁(N))`.** For `p ∣ N` the Hecke operator of the double
coset `Γ₁(N) · diag(1, p) · Γ₁(N)` is the classical operator of `UpperTri/ModularForm.lean` —
the operator modern papers write `Uₚ`. -/
@[simp]
theorem heckeSlashGamma1ModularFormEnd_diagCosetGamma1 (hpN : p ∣ N) :
    heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) =
      heckeSlashUpperTriModularFormEnd k hpN :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1ModularFormEnd, coe_heckeSlashUpperTriModularFormEnd,
      heckeSlashSum_diagCosetGamma1 k hpN f]

/-- **The normalisation lemma on `S_k(Γ₁(N))`.** -/
@[simp]
theorem heckeSlashGamma1CuspFormEnd_diagCosetGamma1 (hpN : p ∣ N) :
    heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) = heckeSlashUpperTriCuspFormEnd k hpN :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1CuspFormEnd, coe_heckeSlashUpperTriCuspFormEnd,
      heckeSlashSum_diagCosetGamma1 k hpN f]

/-- **The `q`-expansion recurrence for the double-coset operator**: at `p ∣ N` its coefficient at
`m` is the coefficient of the original form at `p m`. -/
theorem qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1 (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f)).coeff m
      = (qExpansion 1 f).coeff (p * m) := by
  rw [heckeSlashGamma1ModularFormEnd_diagCosetGamma1 k hpN,
    qExpansion_coeff_heckeSlashUpperTriModularFormEnd]

/-- **The `q`-expansion recurrence for the double-coset operator on cusp forms.** -/
theorem qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1 (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f)).coeff m
      = (qExpansion 1 f).coeff (p * m) := by
  rw [heckeSlashGamma1CuspFormEnd_diagCosetGamma1 k hpN,
    qExpansion_coeff_heckeSlashUpperTriCuspFormEnd]

/-- **The double-coset operator preserves the nebentypus** at `p ∣ N`: it maps `M_k(N, χ)` into
itself. -/
theorem heckeSlashGamma1ModularFormEnd_diagCosetGamma1_mem_modFormCharSpace (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeSlashGamma1ModularFormEnd k (diagCosetGamma1 N p) f ∈ modFormCharSpace k χ := by
  rw [heckeSlashGamma1ModularFormEnd_diagCosetGamma1 k hpN]
  exact heckeSlashUpperTriModularFormEnd_mem_modFormCharSpace k hpN χ hf

/-- **The double-coset operator preserves the nebentypus on cusp forms** at `p ∣ N`. -/
theorem heckeSlashGamma1CuspFormEnd_diagCosetGamma1_mem_cuspFormCharSpace (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) f ∈ cuspFormCharSpace k χ := by
  rw [heckeSlashGamma1CuspFormEnd_diagCosetGamma1 k hpN]
  exact heckeSlashUpperTriCuspFormEnd_mem_cuspFormCharSpace k hpN χ hf

end HeckeRing.GL2

end
