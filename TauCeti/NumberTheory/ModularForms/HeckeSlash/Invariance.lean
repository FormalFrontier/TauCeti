/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Reindex

/-!
# The slash sum of a `Γ₁`-invariant function is `Γ₂`-invariant

`heckeSlashSum` is a sum over *chosen* coset representatives, and `HeckeSlash/Basic.lean` records
that on a general `f : ℍ → ℂ` the value depends on those choices. This file proves the theorem
that repairs it: if `f` is invariant under the weight-`k` slash action of `Γ₁`, then
`heckeSlashSum k D f` is invariant under that of `Γ₂`.

That is the content of Shimura's Proposition 3.37 — right multiplication by `γ ∈ Γ₂` merely
**permutes** the right cosets `Γ₁ aᵥ` of the decomposition, so the sum is unchanged. Concretely
`aᵥ γ = δ τᵥ⁻¹ γ = δ (γ⁻¹ τᵥ)⁻¹`, so the permutation is `v ↦ γ⁻¹ • v` for the action of `Γ₂` on
`Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)` — `MulAction.toPerm` at `γ⁻¹` — and the per-summand step is
`slash_rightCosetRep_of_mem_right` from `HeckeSlash/Reindex.lean`.

⚠ The two groups are different: the hypothesis is invariance under `Γ₁` and the conclusion is
invariance under `Γ₂`. They agree on a diagonal triple `HeckeCoset Δ Γ Γ`, which is where the
Hecke operators of Layer 2(b) live, but nothing here needs them to.

## Main results

* `HeckeRing.GL2.heckeSlashSum_slash_invariant`: for `γ ∈ Γ₂` and `Γ₁`-invariant `f`,
  `heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f`.

## Provenance

The statement corresponds to `heckeSlash_slash_invariant` in the AINTLIB `LeanModularForms`
project ([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 198–246,
together with its helper `tRep_mul_eq_transpose`. No code is transcribed: that proof permutes a
*left*-coset index by transposing, so it holds only where every group in sight is transpose-stable
— level one — while the argument below is Shimura's own and quantifies over `γ ∈ Γ₂` at an
arbitrary triple. As in `Reindex.lean`, invariance is carried under the rational slash action
rather than routed through a real subgroup, so AINTLIB's `mem_SL_exists_H` bridge is not needed.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂) [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- The enumeration the reindexing argument needs, chosen exactly as in `HeckeSlash/Basic.lean`
so that the two `∑`s are the same term. -/
noncomputable local instance : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The slash sum of a `Γ₁`-invariant function is `Γ₂`-invariant.** For `f` invariant under the
weight-`k` slash action of `Γ₁` and `γ ∈ Γ₂`,
`heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f`.

The proof is Shimura's — right multiplication by `γ` permutes the summands — and the permutation
is `MulAction.toPerm` applied to `γ⁻¹`, acting on the right-coset index `Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)`.

⚠ This proves invariance of the sum formed from the representatives `D.out` and `v.out` that
`heckeSlashSum` fixes. It does **not** state that sums formed from *different* choices of
representatives agree; that would be a separate theorem, and none is available yet. -/
theorem heckeSlashSum_slash_invariant (f : ℍ → ℂ) (hf : ∀ δ ∈ Γ₁, f ∣[k] δ = f)
    {γ : GL (Fin 2) ℚ} (hγ : γ ∈ Γ₂) :
    heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f := by
  -- Slashing the `v`-th summand by `γ` gives the summand at the permuted index.
  have hperm (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :
      (f ∣[k] rightCosetRep D v) ∣[k] γ =
        f ∣[k] rightCosetRep D ((⟨γ, hγ⟩ : Γ₂)⁻¹ • v) := by
    rw [← SlashAction.slash_mul k (rightCosetRep D v) γ f, rightCosetRep_def D v,
      show (D.out : GL (Fin 2) ℚ) * ((v.out : GL (Fin 2) ℚ))⁻¹ * γ =
        (D.out : GL (Fin 2) ℚ) * (γ⁻¹ * (v.out : GL (Fin 2) ℚ))⁻¹ from by group,
      slash_rightCosetRep_of_mem_right k D (mul_mem (inv_mem hγ) v.out.2) f hf]
    exact congrArg (f ∣[k] rightCosetRep D ·)
      (MulAction.Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ₂)⁻¹ v)
  rw [heckeSlashSum_def, SlashAction.sum_slash]
  -- `MulAction.toPerm` of `γ⁻¹` is the reindexing bijection. Its compatibility hypothesis is
  -- `hperm` up to `toPerm_apply`, which is stated rather than left to defeq.
  exact Fintype.sum_equiv (MulAction.toPerm (⟨γ, hγ⟩ : Γ₂)⁻¹) _ _ fun v ↦ by
    simpa only [MulAction.toPerm_apply] using hperm v

end HeckeRing.GL2
