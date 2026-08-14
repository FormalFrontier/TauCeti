/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Reindex

/-!
# Slash-invariance of the double-coset Hecke slash sum

`heckeSlashSum` sums `f ∣[k] (σᵢ δ)ᵀ` over a left-coset decomposition of a double coset
`D = HδH` for `H = SLnZ 2`. This file proves Shimura's Proposition 3.30: if `f : ℍ → ℂ` is
invariant under the weight-`k` slash action of `SLnZ 2`, then `heckeSlashSum k D f` is also
invariant under `SLnZ 2`.

## Mathematical argument

Slashing `heckeSlashSum k D f` by `γ ∈ SLnZ 2` distributes across the finite sum. Transposition
is an anti-automorphism of `GL(2, ℚ)`, so right-slashing by `γ` multiplies each representative
`(σᵢ δ)ᵀ` on the right by `γ`, which equals `(γᵀ σᵢ δ)ᵀ`. Since `γᵀ ∈ SLnZ 2`, left
multiplication by `γᵀ` permutes the left cosets `DecompQuotient (SLnZ 2) (SLnZ 2) D.out`.
By `slash_transposeRep_of_mem_SLnZ`, each summand matches the representative attached to the
permuted class `γᵀ • i`. Reindexing the sum over the permutation recovers `heckeSlashSum k D f`.

## Main definitions

* `HeckeRing.GL2.heckeSlashSumForm`: the double-coset Hecke operator on `SlashInvariantForm`.
* `HeckeRing.GL2.heckeSlashSumFormₗ`: `heckeSlashSumForm` as a `ℂ`-linear operator.

## Main results

* `HeckeRing.GL2.heckeSlashSum_slash_eq`: `heckeSlashSum k D f` is invariant under slashing by
  any element of `SLnZ 2`, provided `f` is `SLnZ 2`-slash invariant.
* `HeckeRing.GL2.heckeSlashSumForm_apply`: the evaluation equation for `heckeSlashSumForm`.

## Provenance

Ported and extended from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.30.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- Right multiplication by `γ` on transposed representatives is left multiplication by
`transposeSLnZ γ` before transposition. -/
lemma transposeRep_mul_eq (i : DecompQuotient (SLnZ 2) (SLnZ 2) D.out) (γ : SLnZ 2) :
    transposeRep D i * (γ : GL (Fin 2) ℚ) =
      (transposeGLEquiv 2
        ((transposeSLnZ 2 γ : GL (Fin 2) ℚ) * (i.out : GL (Fin 2) ℚ) * D.out)).unop := by
  rw [transposeRep_def, coe_transposeSLnZ]
  have h_trans : (transposeGLEquiv 2 (transposeGLEquiv 2 (γ : GL (Fin 2) ℚ)).unop).unop =
      (γ : GL (Fin 2) ℚ) := transposeGLEquiv_transposeGLEquiv 2 (γ : GL (Fin 2) ℚ)
  have h_mul : (transposeGLEquiv 2 ((transposeGLEquiv 2 (γ : GL (Fin 2) ℚ)).unop *
      ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ)))).unop =
      (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop *
        (transposeGLEquiv 2 (transposeGLEquiv 2 (γ : GL (Fin 2) ℚ)).unop).unop := by
    simp only [map_mul, MulOpposite.unop_mul]
  rw [mul_assoc]
  rw [h_mul, h_trans]

/-- **Shimura Proposition 3.30 (slash-invariance under `SLnZ 2`)**: if `f : ℍ → ℂ` is invariant
under the weight-`k` slash action of `SLnZ 2`, then the double-coset slash sum
`heckeSlashSum k D f` is also invariant under `SLnZ 2`. -/
theorem heckeSlashSum_slash_eq (f : ℍ → ℂ) (hf : ∀ γ ∈ SLnZ 2, f ∣[k] γ = f) (γ : SLnZ 2) :
    heckeSlashSum k D f ∣[k] (γ : GL (Fin 2) ℚ) = heckeSlashSum k D f := by
  let B := transposeSLnZ 2 γ
  let e : DecompQuotient (SLnZ 2) (SLnZ 2) D.out ≃ DecompQuotient (SLnZ 2) (SLnZ 2) D.out :=
    MulAction.toPerm B
  have h_summand (i : DecompQuotient (SLnZ 2) (SLnZ 2) D.out) :
      (f ∣[k] transposeRep D i) ∣[k] (γ : GL (Fin 2) ℚ) = f ∣[k] transposeRep D (e i) := by
    rw [← SlashAction.slash_mul, transposeRep_mul_eq (D := D) i γ]
    have h_mem : (B : GL (Fin 2) ℚ) * (i.out : GL (Fin 2) ℚ) ∈ SLnZ 2 :=
      mul_mem B.2 i.out.2
    have h_slash := slash_transposeRep_of_mem_SLnZ k D h_mem (SLnZ 2).one_mem f hf
    have h_assoc : (B : GL (Fin 2) ℚ) * (i.out : GL (Fin 2) ℚ) * D.out =
        ((B : GL (Fin 2) ℚ) * (i.out : GL (Fin 2) ℚ)) * D.out * 1 := by simp [mul_assoc]
    rw [h_assoc, h_slash]
    have h_ei : e i = ⟦⟨(B : GL (Fin 2) ℚ) * (i.out : GL (Fin 2) ℚ), h_mem⟩⟧ := by
      change B • i = _
      calc
        B • i = QuotientGroup.mk (B * i.out) :=
          (MulAction.Quotient.mk_smul_out _ B i).symm
        _ = _ := congrArg QuotientGroup.mk (Subtype.ext (by rfl))
    rw [h_ei]
  rw [heckeSlashSum_def, SlashAction.sum_slash, Finset.sum_congr rfl fun i _ ↦ h_summand i]
  exact Equiv.sum_comp e (fun j ↦ f ∣[k] transposeRep D j)

/-- **The Hecke operator on `SlashInvariantForm`**: descending `heckeSlashSum` to
`SlashInvariantForm 𝒮ℒ k`. -/
noncomputable def heckeSlashSumForm (f : SlashInvariantForm 𝒮ℒ k) :
    SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlashSum k D ⇑f
  slash_action_eq' := fun γ hγ ↦ by
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hγ
    have h_SLnZ : (mapGL ℚ σ : GL (Fin 2) ℚ) ∈ SLnZ 2 := coe_mem_SLnZ 2 σ
    exact heckeSlashSum_slash_eq k D (⇑f)
      (fun g hg ↦ SlashInvariantFormClass.slash_eq_of_mem_SLnZ f g hg)
      ⟨mapGL ℚ σ, h_SLnZ⟩

@[simp]
lemma coe_heckeSlashSumForm (f : SlashInvariantForm 𝒮ℒ k) :
    ⇑(heckeSlashSumForm k D f) = heckeSlashSum k D ⇑f := (rfl)

/-- Pointwise evaluation of `heckeSlashSumForm`. -/
lemma heckeSlashSumForm_apply (f : SlashInvariantForm 𝒮ℒ k) (τ : ℍ) :
    heckeSlashSumForm k D f τ = heckeSlashSum k D (⇑f) τ := (rfl)

/-- The double-coset Hecke operator as a `ℂ`-linear map on `SlashInvariantForm`. -/
noncomputable def heckeSlashSumFormₗ : SlashInvariantForm 𝒮ℒ k →ₗ[ℂ] SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlashSumForm k D
  map_add' f g := SlashInvariantForm.ext (fun τ ↦ by
    rw [heckeSlashSumForm_apply, FunLike.coe_add, heckeSlashSum_add]
    rfl)
  map_smul' c f := SlashInvariantForm.ext (fun τ ↦ by
    rw [heckeSlashSumForm_apply, FunLike.coe_smul, heckeSlashSum_smul]
    rfl)

@[simp]
lemma heckeSlashSumFormₗ_apply (f : SlashInvariantForm 𝒮ℒ k) :
    heckeSlashSumFormₗ k D f = heckeSlashSumForm k D f := (rfl)

end HeckeRing.GL2
