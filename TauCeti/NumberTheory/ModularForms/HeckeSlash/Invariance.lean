/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Reindex

/-!
# The slash sum is `SL₂(ℤ)`-invariant

`heckeSlashSum` is a sum over *chosen* coset representatives, and `HeckeSlash/Basic.lean` records
that on a general `f : ℍ → ℂ` the value depends on those choices. This file proves the theorem
that repairs it: if `f` is invariant under the weight-`k` slash action of `SL₂(ℤ)`, then so is
`heckeSlashSum k D f`.

That is the content of the proof of Shimura's Proposition 3.37 — right multiplication by
`γ ∈ SL₂(ℤ)` merely **permutes** the representatives, so the sum is unchanged. The permutation is
`MulAction.toPerm` for the action of `SL₂(ℤ)` on `DecompQuotient`, and the per-summand step is
`slash_transposeRep_of_mem_SLnZ` from `HeckeSlash/Reindex.lean`.

## Main results

* `HeckeRing.GL2.heckeSlashSum_slash_invariant_of_mem_SLnZ`: for `γ ∈ SL₂(ℤ)` and
  slash-invariant `f`, `heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f`.
* `HeckeRing.GL2.heckeSlashSumFormₗ`: the slash sum as a `ℂ`-linear operator on
  `SlashInvariantForm`.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 198–224:
`tRep_mul_eq_transpose` and `heckeSlash_slash_invariant`.

Restated against TauCeti's `SLnZ`/`posDetInt` Hecke pair and `transposeGLEquiv`. As in
`Reindex.lean`, the invariance hypothesis is carried at `SLnZ 2` under the rational slash action
rather than routed through the real `𝒮ℒ`, so AINTLIB's `mem_SL_exists_H` bridge — which opens its
proof — is not needed here and the statement quantifies over `γ ∈ SLnZ 2` directly.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

-- Right multiplication of a representative by `γ` is the transpose of left multiplication by
-- `γᵀ`, which is what turns the reindexing lemma into a permutation of the index type.
private lemma transposeRep_mul (i : DecompQuotient (SLnZ 2) (SLnZ 2) D.out) (γ : GL (Fin 2) ℚ) :
    transposeRep D i * γ = (transposeGLEquiv 2 ((transposeGLEquiv 2 γ).unop *
      (i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop := by
  simp [transposeRep_def, map_mul, MulOpposite.unop_mul, transposeGLEquiv_transposeGLEquiv,
    mul_assoc]

/-- **The slash sum of a slash-invariant function is again slash-invariant.** For `f` invariant
under the weight-`k` slash action of `SL₂(ℤ)` and `γ ∈ SL₂(ℤ)`,
`heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f`.

The proof is Shimura's — right multiplication by `γ` permutes the summands — and the permutation
is `MulAction.toPerm` applied to `γᵀ`, the transpose appearing because the representatives are
transposed.

⚠ This proves invariance of the sum formed from the representatives `D.out` and `i.out` that
`heckeSlashSum` fixes. It does **not** state that sums formed from *different* choices of
representatives agree; that would be a separate theorem, and none is available yet. -/
theorem heckeSlashSum_slash_invariant_of_mem_SLnZ (f : ℍ → ℂ) (hf : ∀ δ ∈ SLnZ 2, f ∣[k] δ = f)
    {γ : GL (Fin 2) ℚ} (hγ : γ ∈ SLnZ 2) :
    heckeSlashSum k D f ∣[k] γ = heckeSlashSum k D f := by
  have hγT : (transposeGLEquiv 2 γ).unop ∈ SLnZ 2 := transposeGLEquiv_mem_SLnZ 2 hγ
  -- Slashing the `i`-th summand by `γ` gives the summand at the permuted index.
  have hperm (i : DecompQuotient (SLnZ 2) (SLnZ 2) D.out) :
      (f ∣[k] transposeRep D i) ∣[k] γ =
        f ∣[k] transposeRep D ((⟨_, hγT⟩ : SLnZ 2) • i) := by
    rw [← SlashAction.slash_mul k (transposeRep D i) γ f, transposeRep_mul, ← mul_one
      ((⟨_, hγT⟩ : SLnZ 2) * (i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ)),
      slash_transposeRep_of_mem_SLnZ k D (mul_mem hγT i.out.2) (one_mem _) f hf]
    exact congrArg (f ∣[k] transposeRep D ·)
      (MulAction.Quotient.mk_smul_out _ (⟨_, hγT⟩ : SLnZ 2) i)
  rw [heckeSlashSum_def, SlashAction.sum_slash]
  -- `MulAction.toPerm` of the transposed `γ` is the reindexing bijection. Its compatibility
  -- hypothesis is `hperm` up to `toPerm_apply`, which is stated rather than left to defeq.
  exact Fintype.sum_equiv (MulAction.toPerm (⟨_, hγT⟩ : SLnZ 2)) _ _ fun i ↦ by
    simpa only [MulAction.toPerm_apply] using hperm i

/-- The double-coset slash sum as a `ℂ`-linear operator on `SlashInvariantForm`. -/
noncomputable def heckeSlashSumFormₗ : SlashInvariantForm 𝒮ℒ k →ₗ[ℂ] SlashInvariantForm 𝒮ℒ k where
  toFun f :=
    SlashInvariantForm.mk (heckeSlashSum k D ⇑f) fun γ hγ ↦ by
      obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hγ
      have hSLnZ : (mapGL ℚ σ : GL (Fin 2) ℚ) ∈ SLnZ 2 := coe_mem_SLnZ 2 σ
      rw [← map_mapGL (S := ℚ) (T := ℝ) σ, ← ModularForm.rat_slash]
      exact heckeSlashSum_slash_invariant_of_mem_SLnZ k D (⇑f) (γ := mapGL ℚ σ)
        (fun g hg ↦ SlashInvariantFormClass.slash_eq_of_mem_SLnZ f g hg) hSLnZ
  map_add' f g := SlashInvariantForm.ext fun τ ↦ by
    simp only [SlashInvariantForm.coe_mk, FunLike.coe_add]
    exact congrFun (heckeSlashSum_add k D ⇑f ⇑g) τ
  map_smul' c f := SlashInvariantForm.ext fun τ ↦ by
    simp only [SlashInvariantForm.coe_mk, FunLike.coe_smul]
    exact congrFun (heckeSlashSum_smul k D c ⇑f) τ

@[simp]
lemma coe_heckeSlashSumFormₗ (f : SlashInvariantForm 𝒮ℒ k) :
    ⇑(heckeSlashSumFormₗ k D f) = heckeSlashSum k D ⇑f := (rfl)

/-- Pointwise evaluation of `heckeSlashSumFormₗ`. -/
@[simp]
lemma heckeSlashSumFormₗ_apply (f : SlashInvariantForm 𝒮ℒ k) (τ : ℍ) :
    heckeSlashSumFormₗ k D f τ = heckeSlashSum k D (⇑f) τ := (rfl)

end HeckeRing.GL2
