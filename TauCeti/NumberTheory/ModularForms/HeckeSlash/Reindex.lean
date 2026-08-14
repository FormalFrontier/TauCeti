/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# Reindexing the slash sum: slashing by any element of a left coset

`heckeSlashSum` sums `f ∣[k] (σᵢ δ)ᵀ` over the left-coset decomposition of `HδH`. To show that
sum is unchanged by right multiplication — the statement that turns the sum into an operator,
and the proof of Shimura's Proposition 3.37 — one needs to know that the summand depends only on
the *coset* of `σᵢ`, not on the representative chosen, once `f` is slash-invariant.

That is what this file proves. For `h₁, h₂ ∈ H`,

`f ∣[k] (h₁ δ h₂)ᵀ = f ∣[k] transposeRep D ⟦h₁⟧`,

so an arbitrary element `h₁ δ h₂` of the double coset slashes exactly like the chosen
representative of `h₁`'s class.

## Why slash-invariance of `f` is needed, and where

Transposition turns left multiplication into right multiplication, so changing the
representative multiplies the transposed element **on the left** by a transposed element of
`H`. Slashing is a right action, so that extra factor does not simply cancel: it survives as
`f ∣[k] hᵀ`, and only vanishes because `f` is invariant under `H` — which is exactly the
hypothesis `hf`. Without it the sum genuinely depends on the choice, as `HeckeSlash/Basic.lean`'s
module docstring records.

## Main results

* `HeckeRing.GL2.slash_transposeRep_of_mem_SLnZ`: slashing by the transpose of `h₁ δ h₂` agrees
  with slashing by the representative attached to `h₁`.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 154–196:
`slash_left_H_transpose_mul`, `h_coset_mem_H`, `transpose_decomp_eq` and `slash_tRep_of_mem`.
Restated against TauCeti's `SLnZ` / `posDetInt` Hecke pair, `DoubleCoset.DecompQuotient`,
`transposeGLEquiv` and `transposeRep`, rather than AINTLIB's `GL_pair`, `decompQuot`,
`GL_transposeEquiv` and `tRep`. AINTLIB's `h_coset_mem_H` is not reproduced as a declaration: this
repository already owns exactly that statement as `DoubleCoset.conj_mem_of_mk_eq`, which is what
the proof below calls.

One deliberate deviation: the slash-invariance hypothesis is carried at `SLnZ 2` under the
rational slash action, rather than routed through the real `𝒮ℒ`. AINTLIB's
`slash_left_H_transpose_mul` crosses that bridge with a helper (`glMap_mem_SL`); here the
membership is already rational, so `transposeGLEquiv_mem_SLnZ` applies directly and that helper
is unnecessary. No claim is made about AINTLIB's other bridging helper `mem_SL_exists_H`, which
is used only by the invariance block that follows the ported range.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 *Action of double cosets on automorphic forms*, Proposition 3.37.

Shimura states the result this file supports inside the proof of Proposition 3.37: "Let `α ∈ Γ₂`.
Then `{Γ₁ aᵥ α}` coincides with `{Γ₁ aᵥ}` as a whole", from which `g ∣[α]ₖ = g` for
`g = f ∣[Γ₁ α Γ₂]ₖ`. He needs no transpose, because his decomposition `Γ₁ α Γ₂ = ⊔ᵥ Γ₁ aᵥ` puts
the group on the left already; the transpose here is an artefact of the handedness Mathlib's
`DecompQuotient` supplies, not of the mathematics.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

-- A transposed element of `H` on the left of a slash is absorbed by slash-invariance. This is the
-- single point at which `hf` enters the file — the "where" of the section above — which is why it
-- is named rather than inlined at its one call site.
--
-- Mathlib does not name this step: it open-codes the same composition inside
-- `SlashInvariantForm.translate` and `SlashInvariantForm.quotientFunc`. That convention does not
-- transfer here, because both of those carry invariance in a `[SlashInvariantFormClass F Γ k]`
-- instance and so recover it in one typeclass call at each site, whereas `hf` is a bare
-- hypothesis threaded through a three-step argument.
private lemma slash_transpose_mul_of_mem_SLnZ {h : GL (Fin 2) ℚ} (hh : h ∈ SLnZ 2)
    (g : GL (Fin 2) ℚ) (f : ℍ → ℂ) (hf : ∀ γ ∈ SLnZ 2, f ∣[k] γ = f) :
    f ∣[k] ((transposeGLEquiv 2 h).unop * g) = f ∣[k] g := by
  rw [SlashAction.slash_mul, hf _ (transposeGLEquiv_mem_SLnZ 2 hh)]

-- Splitting `(h₁ δ h₂)ᵀ` as the correction factor's transpose times the chosen representative.
private lemma transposeGLEquiv_eq_mul_transposeRep (q : DecompQuotient (SLnZ 2) (SLnZ 2) D.out)
    (h₁ h₂ : GL (Fin 2) ℚ) : (transposeGLEquiv 2 (h₁ * ↑D.out * h₂)).unop =
      (transposeGLEquiv 2 ((D.out : GL (Fin 2) ℚ)⁻¹ * ((q.out : GL (Fin 2) ℚ)⁻¹ * h₁) * ↑D.out *
        h₂)).unop * transposeRep D q := by
  -- Transposition is an anti-homomorphism, so the two `δ`s meet in the middle and cancel.
  -- `transposeRep` has no exposed body in a module file, so its characteristic equation
  -- `transposeRep_def` is the only way in; `simp [transposeRep]` and `unfold` both fail here.
  simp [transposeRep_def, ← MulOpposite.unop_mul, ← map_mul, mul_assoc]

/-- **An arbitrary element `h₁ δ h₂` of the double coset slashes like the representative attached
to `h₁`'s class.** For `h₁, h₂ ∈ H` and `f` invariant under the weight-`k` slash action of
`H = SLnZ 2`, `f ∣[k] (h₁ δ h₂)ᵀ = f ∣[k] transposeRep D ⟦h₁⟧`, where `δ = D.out`.

`hh₁` is part of the statement rather than a side condition: the right-hand side slashes by
`transposeRep D ⟦⟨h₁, hh₁⟩⟧`, a class built from `hh₁`. Membership is a `Prop`, so any proof of
`h₁ ∈ SLnZ 2` names the same class. Narrowing `hf` does not help: when `h₁` is the chosen
representative of its own class the absorbed factor is exactly `h₂ᵀ`, so quantifying over `h₂`
already reaches every element of `SLnZ 2`. Note also that `hf` is invariance under the *rational*
slash action, not one routed through the real `𝒮ℒ`.

This is the per-summand step behind Shimura's Proposition 3.37 (§3.4). The statement
that right multiplication permutes the summands of `heckeSlashSum` without changing the sum is a
separate argument, which is not formalised here. Mathlib's `SlashInvariantForm.quotientFunc_mk`
is the single-subgroup analogue, with no double coset and no transpose. -/
lemma slash_transposeRep_of_mem_SLnZ {h₁ h₂ : GL (Fin 2) ℚ} (hh₁ : h₁ ∈ SLnZ 2) (hh₂ : h₂ ∈ SLnZ 2)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ SLnZ 2, f ∣[k] γ = f) :
    f ∣[k] (transposeGLEquiv 2 (h₁ * ↑D.out * h₂)).unop = f ∣[k] transposeRep D ⟦⟨h₁, hh₁⟩⟧ := by
  rw [transposeGLEquiv_eq_mul_transposeRep D ⟦⟨h₁, hh₁⟩⟧ h₁ h₂]
  -- The leftover factor lies in `H`: `Quotient.out_eq` says the chosen representative of `⟦h₁⟧`
  -- is in `h₁`'s own class, and `conj_mem_of_mk_eq` turns that class equality into the
  -- conjugated membership in one step.
  exact slash_transpose_mul_of_mem_SLnZ k
    (mul_mem (conj_mem_of_mk_eq _ (Quotient.out_eq _)) hh₂) _ f hf

end HeckeRing.GL2
