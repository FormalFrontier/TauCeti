/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ConductorDichotomy
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent

/-!
# A form with a periodic level-`l` descent is old

Let `l` be a divisor of `N` other than `1`, and let `φ : ℍ → ℂ` be invariant under the weight-`k`
slash action of `T`. If the level-raise `l ^ (1 - k) • (φ ∣[k] diag(l, 1))` is a cusp form `f` of
level `Γ₁(N)` lying in the nebentypus space `S_k(N, χ)`, then `f` is old.

`ConductorDichotomy.lean` proves Miyake's Theorem 4.6.4 under exactly those hypotheses: *either*
`χ` factors through `N / l` and `φ` is itself a cusp form of level `Γ₁(N / l)`, *or* `φ` is
identically zero. Both horns say the same thing about `f`. On the first it is the level-raise
`V_l F` of a genuine cusp form of the proper divisor level `N / l`; on the second it is `0`; and
`TauCeti.cuspFormsOld` contains both.

## Why `l ≠ 1` is the only arithmetic hypothesis

`TauCeti.cuspFormsOld` is spanned by the level-raises from **proper** divisor levels, so what the
argument needs of `l` is exactly that `N / l` be a proper divisor of `N` — that is, `l ≠ 1`, which
together with `l ∣ N` and `N ≠ 0` gives `N / l < N`. Neither result asks `l` to be prime.

The two entry points differ in where the descent comes from.
`mem_cuspFormsOld_of_slash_T_eq` takes `φ` from the caller, so no hypothesis on the
`q`-expansion of `f` appears in it at all; `mem_cuspFormsOld_of_qExpansionSupportedOnDvd`
instead assumes `QExpansionSupportedOnDvd l f` and obtains `φ` from it.

## Main results

* `TauCeti.mem_cuspFormsOld_of_slash_T_eq`: a cusp form of level `Γ₁(N)` with a nebentypus, whose
  level-`l` descent is invariant under the weight-`k` slash action of `T`, is old.
* `TauCeti.mem_cuspFormsOld_of_qExpansionSupportedOnDvd`: **the Atkin–Lehner step at one
  divisor** — the same conclusion from the `q`-expansion support condition alone, the descent
  being supplied by `Newforms/Descent.lean`.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck, Apache-2.0) at
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
`projects/LeanModularForms/LeanModularForms/Eigenforms/AtkinLehner.lean` — the case split of
`qSupportedOnDvd_mem_cuspFormsOld_of_char` (lines 169-192).

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
* Miyake, *Modular forms*, Section 4.6 (Theorem 4.6.4 is the dichotomy consumed here).
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **A cusp form with a `T`-periodic level-`l` descent is old.** If `f ∈ S_k(N, χ)` is the
level-raise `l ^ (1 - k) • (φ ∣[k] diag(l, 1))` of a function `φ : ℍ → ℂ` invariant under the
weight-`k` slash action of `T`, and `l` is a divisor of `N` other than `1`, then `f` lies in the
old subspace `S_k(Γ₁(N))ᵒˡᵈ`.

This is the level-lowering dichotomy `TauCeti.exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero`
read for its common conclusion: on the descent horn `φ` is a cusp form of level `Γ₁(N / l)` and
`f` is its level-raise, and on the vanishing horn `φ = 0` forces `f = 0`. Both are old. -/
theorem mem_cuspFormsOld_of_slash_T_eq {l : ℕ} (hl : l ≠ 1) (hlN : l ∣ N)
    (χ : DirichletCharacter ℂ N) (φ : ℍ → ℂ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hf : haveI : NeZero l := NeZero.of_dvd hlN
      ⇑f = (l : ℂ) ^ (1 - k) • (φ ∣[k] scaleGL l))
    (hT : φ ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = φ) :
    f ∈ cuspFormsOld N k := by
  have : NeZero l := NeZero.of_dvd hlN
  have hdvd : l * (N / l) ∣ N := (Nat.mul_div_cancel' hlN).dvd
  have hM : N / l ≠ N :=
    Nat.ne_of_lt (Nat.div_lt_self (NeZero.pos N) (by have := NeZero.ne l; omega))
  rcases exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero hlN k χ φ f hfχ hf hT with
    ⟨_, F, _, hF⟩ | hφ
  · -- `f` and the level-raise of `F` have the same underlying function, and coercion is injective
    have hcoe : ⇑f = ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) F) := by
      rw [CuspForm.coe_levelRaise, hF, hf]
    rw [DFunLike.coe_injective hcoe]
    exact levelRaise_mem_cuspFormsOld hdvd hM k F
  · have hf0 : f = 0 := DFunLike.coe_injective <| by
      rw [hf, hφ, SlashAction.zero_slash, smul_zero, FunLike.coe_zero]
    exact hf0 ▸ (cuspFormsOld N k).zero_mem

/-- **The Atkin–Lehner step at one divisor.** A cusp form of level `Γ₁(N)` with a nebentypus,
whose period-one `q`-expansion is supported on the multiples of a divisor `l ≠ 1` of `N`, is old.

The support condition is the only thing asked of the `q`-expansion, and `l` need not be prime.

⚠ The hypothesis is support on the multiples of **one** divisor `l`, for a form in **one**
character space. Diamond–Shurman Theorem 5.7.1 assumes instead that `aₙ(f) = 0` at every `n`
coprime to `N`, a condition naming no divisor. The two are not interchangeable, and the
implication runs one way: since `l ∣ N` and `l ≠ 1`, every `n` coprime to `N` is in particular
not divisible by `l`, so `QExpansionSupportedOnDvd l` is the stronger hypothesis — it kills
every index off the multiples of `l`, not merely those prime to `N`. The two agree only in the
degenerate case where `l` is prime and `N` is a power of `l`: if they agree then every prime `q`
dividing `N` satisfies `l ∣ q`, forcing `q = l`. Getting from Diamond–Shurman's hypothesis to
this one therefore means splitting `f` across the primes dividing `N`. -/
theorem mem_cuspFormsOld_of_qExpansionSupportedOnDvd {l : ℕ} (hl : l ≠ 1) (hlN : l ∣ N)
    (χ : DirichletCharacter ℂ N) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hf : haveI : NeZero l := NeZero.of_dvd hlN
      QExpansionSupportedOnDvd l f) :
    f ∈ cuspFormsOld N k := by
  -- The support condition is spent entirely on manufacturing the descent: `Descent.lean` turns
  -- it into a `T`-invariant `φ` with `f = l ^ (1 - k) • (φ ∣[k] diag(l, 1))`, and
  -- `mem_cuspFormsOld_of_slash_T_eq` reads the level-lowering dichotomy off that.
  have : NeZero l := NeZero.of_dvd hlN
  obtain ⟨φ, hφ, hT⟩ :=
    CuspForm.exists_eq_smul_slash_scaleGL_and_slash_T_eq_of_qExpansionSupportedOnDvd f hf
  exact mem_cuspFormsOld_of_slash_T_eq hl hlN χ φ hfχ hφ hT

end TauCeti

end
