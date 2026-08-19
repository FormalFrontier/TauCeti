/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# Reindexing the slash sum: slashing by any element of a double coset

`heckeSlashSum` sums `f ∣[k] (δ τᵥ⁻¹)` over the decomposition of `Γ₁ δ Γ₂` into right cosets
`Γ₁ aᵥ`. To show that sum is unchanged by right multiplication — the statement that turns the sum
into an operator, and the proof of Shimura's Proposition 3.37 — one needs to know that the
summand depends only on the *coset*, not on the representative chosen, once `f` is
slash-invariant.

That is what this file proves. For `h₁ ∈ Γ₁` and `h₂ ∈ Γ₂`,

`f ∣[k] (h₁ δ h₂⁻¹) = f ∣[k] rightCosetRep D ⟦h₂⟧`,

so an arbitrary element `h₁ δ h₂⁻¹` of the double coset slashes exactly like the chosen
representative of `h₂`'s class. Every element of `Γ₁ δ Γ₂` has this shape, `Γ₂` being a group.

## Why slash-invariance of `f` is needed, and where

Two representatives of the same right coset differ by a factor of `Γ₁` on the **left**. Slashing
is a right action, so that factor does not simply cancel: it survives as `f ∣[k] γ₁`, and only
vanishes because `f` is invariant under `Γ₁` — which is exactly the hypothesis `hf` below, used
once, in the last step.

Concretely, if `u` is the chosen representative of `⟦h₂⟧` then `δ (u⁻¹ h₂) δ⁻¹ ∈ Γ₁`
(`DoubleCoset.conj_mem_of_mk_eq`, the conjugation criterion for the stabiliser
`Γ₂ ∩ δ⁻¹Γ₁δ` indexing the quotient), and

`h₁ δ h₂⁻¹ = (h₁ · (δ (u⁻¹ h₂) δ⁻¹)⁻¹) · (δ u⁻¹)`

exhibits the left factor as an element of `Γ₁` and the right one as `rightCosetRep D ⟦h₂⟧`.

## Main results

* `HeckeRing.GL2.slash_rightCosetRep_of_mem`: the displayed identity.
* `HeckeRing.GL2.slash_rightCosetRep_of_mem_right`: its `h₁ = 1` case, the form the invariance
  proof consumes.

## Provenance

The statement corresponds to `slash_left_H_transpose_mul`, `transpose_decomp_eq` and
`slash_tRep_of_mem` in the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 154–196. No
code is transcribed: those declarations reindex a sum over *left* cosets and pay for it with a
transpose, which confines them to `SL₂(ℤ)`, whereas the identity below is Shimura's own
right-coset step and holds at an arbitrary triple. AINTLIB's `h_coset_mem_H` has no counterpart
either: this repository already owns exactly that statement as
`DoubleCoset.conj_mem_of_mk_eq`, which is what the proof below calls.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 *Action of double cosets on automorphic forms*, Proposition 3.37.

Shimura states the result this file supports inside the proof of Proposition 3.37: "Let
`α ∈ Γ₂`. Then `{Γ₁ aᵥ α}` coincides with `{Γ₁ aᵥ}` as a whole", from which `g ∣[α]ₖ = g` for
`g = f ∣[Γ₁ α Γ₂]ₖ`. Knowing that a given element of the double coset slashes like the chosen
representative of its coset is what makes that comparison of *sets* into a comparison of *sums*.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- **An arbitrary element `h₁ δ h₂⁻¹` of the double coset slashes like the representative
attached to `h₂`'s class.** For `h₁ ∈ Γ₁`, `h₂ ∈ Γ₂` and `f` invariant under the weight-`k` slash
action of `Γ₁`, `f ∣[k] (h₁ δ h₂⁻¹) = f ∣[k] rightCosetRep D ⟦h₂⟧`, where `δ = D.out`.

`hh₂` is part of the statement rather than a side condition: the right-hand side slashes by
`rightCosetRep D ⟦⟨h₂, hh₂⟩⟧`, a class built from `hh₂`. Membership is a `Prop`, so any proof of
`h₂ ∈ Γ₂` names the same class. Note that `hf` is invariance under the *rational* slash action,
not one routed through a real subgroup.

This is the per-summand step behind Shimura's Proposition 3.37 (§3.4). The statement that right
multiplication permutes the summands of `heckeSlashSum` without changing the sum is a separate
argument, in `HeckeSlash/Invariance.lean`. Mathlib's `SlashInvariantForm.quotientFunc_mk` is the
single-subgroup analogue, with no double coset. -/
lemma slash_rightCosetRep_of_mem {h₁ h₂ : GL (Fin 2) ℚ} (hh₁ : h₁ ∈ Γ₁) (hh₂ : h₂ ∈ Γ₂)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    f ∣[k] (h₁ * (D.out : GL (Fin 2) ℚ) * h₂⁻¹) =
      f ∣[k] rightCosetRep D ⟦⟨h₂, hh₂⟩⟧ := by
  -- Make the chosen representative `u` of `⟦h₂⟧` visible, then name it.
  rw [rightCosetRep_def]
  set u : GL (Fin 2) ℚ :=
    (((⟦⟨h₂, hh₂⟩⟧ : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹).out :
      Γ₂) : GL (Fin 2) ℚ) with hu
  -- `u` and `h₂` have the same class, so `δ (u⁻¹ h₂) δ⁻¹` lies in `Γ₁`.
  have hconj : (D.out : GL (Fin 2) ℚ) * (u⁻¹ * h₂) * (D.out : GL (Fin 2) ℚ)⁻¹ ∈ Γ₁ := by
    rw [hu]
    simpa using conj_mem_of_mk_eq ((D.out : GL (Fin 2) ℚ)⁻¹) (Quotient.out_eq _)
  -- Split off that factor on the left; what is left is the chosen representative.
  rw [show h₁ * (D.out : GL (Fin 2) ℚ) * h₂⁻¹ =
      (h₁ * ((D.out : GL (Fin 2) ℚ) * (u⁻¹ * h₂) * (D.out : GL (Fin 2) ℚ)⁻¹)⁻¹) *
        ((D.out : GL (Fin 2) ℚ) * u⁻¹) from by group,
    SlashAction.slash_mul, hf _ (mul_mem hh₁ (inv_mem hconj))]

/-- The `h₁ = 1` case of `slash_rightCosetRep_of_mem`: slashing by `δ h₂⁻¹` agrees with slashing
by the chosen representative of `h₂`'s class. This is the form the invariance proof consumes,
where the element being compared already arises as `δ τᵥ⁻¹ γ = δ (γ⁻¹ τᵥ)⁻¹`. -/
lemma slash_rightCosetRep_of_mem_right {h₂ : GL (Fin 2) ℚ} (hh₂ : h₂ ∈ Γ₂) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    f ∣[k] ((D.out : GL (Fin 2) ℚ) * h₂⁻¹) = f ∣[k] rightCosetRep D ⟦⟨h₂, hh₂⟩⟧ := by
  simpa using slash_rightCosetRep_of_mem k D (one_mem Γ₁) hh₂ f hf

end HeckeRing.GL2
