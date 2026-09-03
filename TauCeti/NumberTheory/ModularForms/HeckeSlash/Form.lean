/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Invariance

/-!
# The slash sum as an operator on slash-invariant forms

`Invariance.lean` proves that `heckeSlashSum k D f` is `Γ₂`-invariant when `f` is `Γ₁`-invariant.
This file packages the diagonal case of that into a map
`SlashInvariantForm (G.map (mapGL ℝ)) k → SlashInvariantForm (G.map (mapGL ℝ)) k`, which is the
point at which the double coset finally acts on *forms* rather than on raw functions `ℍ → ℂ`.

## The level

`G` is an arbitrary subgroup of `SL(2, ℤ)`; taking `G = Γ₁(N)` gives the level at which the
roadmap's Hecke operators live, and `G = ⊤` recovers level one. The two flanks of the double
coset are the *same* group `G.map (mapGL ℚ)`, which is what makes the hypothesis and the
conclusion of `heckeSlashSum_slash_invariant` the same condition; no transpose-stability is
needed anywhere, which is why the level is not confined to `SL₂(ℤ)`.

## Crossing from `ℚ` to `ℝ`

The two sides speak different languages, and reconciling them is what
`ModularForms/SlashActionRat.lean` is for. `SlashInvariantForm Γ k` is indexed by a subgroup of
`GL(2, ℝ)`, while the Hecke triples of `HeckeRing/GL2/` live in `GL(2, ℚ)`; both levels here are
images of the same `G ≤ SL(2, ℤ)`, so `Matrix.SpecialLinearGroup.map_mapGL` relates them
directly at `ℤ → ℚ → ℝ`. `ModularForm.slash_eq_of_mem_map_mapGL` and its `_real` companion are
the two directions, and they are the only bridging this file does.

## Main definitions

* `HeckeRing.GL2.heckeSlashEnd`: the double coset bundled as a `ℂ`-linear endomorphism of
  `SlashInvariantForm (G.map (mapGL ℝ)) k`. This is an intermediate step toward Layer 2(b), which
  asks for endomorphisms of `ModularForm`; holomorphy and the cusp conditions are added in
  `HeckeSlash/ModularForm.lean`.

## Main results

* `HeckeRing.GL2.coe_heckeSlashEnd`: the endomorphism is `heckeSlashSum` on underlying functions.

## Provenance

The statement corresponds to `heckeSlashInvariant` in the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck). AINTLIB's `glMap`
wrapper and its bridging helpers `glMap_mem_SL` and `mem_SL_exists_H` have no counterpart here:
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` is already the map, mathlib's
`Matrix.SpecialLinearGroup.map_mapGL` is already the identity relating the two images, and the
statement is at a general `G` rather than at `SL₂(ℤ)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {G : Subgroup SL(2, ℤ)} (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
  [Finite (DecompQuotient (G.map (mapGL ℚ)) (G.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]
  (hD : (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ)

/-- **The double coset acting on slash-invariant forms.** The underlying function is
`heckeSlashSum`, and its invariance is `heckeSlashSum_slash_invariant` transported across the
`G.map (mapGL ℚ)` ↔ `G.map (mapGL ℝ)` correspondence.

⚠ As in `Invariance.lean`, this is the sum over the representatives `heckeSlashSum` fixes. That
any other decomposition of the double coset into right cosets gives the same form is
`heckeSlashSum_coe_eq_sum_of_rightCosets` (`HeckeSlash/Independence.lean`), whose hypothesis is
exactly the slash-invariance carried here. -/
private noncomputable def heckeSlashInvariant (f : SlashInvariantForm (G.map (mapGL ℝ)) k) :
    SlashInvariantForm (G.map (mapGL ℝ)) k where
  toFun := heckeSlashSum k D f
  slash_action_eq' γ hγ := by
    refine ModularForm.slash_eq_of_mem_map_mapGL_real (fun δ hδ ↦ ?_) hγ
    exact heckeSlashSum_slash_invariant k D (⇑f)
      (fun _ hε ↦ ModularForm.slash_eq_of_mem_map_mapGL
        (fun γ' hγ' ↦ SlashInvariantFormClass.slash_action_eq f γ' hγ') hε) hδ

/-- **The double coset as a `ℂ`-linear endomorphism of `SlashInvariantForm (G.map (mapGL ℝ)) k`.**
Bundling it as a `Module.End ℂ` is what lets Hecke operators compose and later carry a ring
structure. Linearity is `heckeSlashSum_add`, which needs no hypothesis, together with
`heckeSlashSum_smul`, which needs each representative to have positive determinant: the flanking
group consists of determinant-one matrices (`ModularForm.map_mapGL_le_glpos`), so `hD` is all
that is left to ask.

⚠ This is an intermediate step, not the roadmap's Layer 2(b) target: that asks for endomorphisms
of `ModularForm (G.map (mapGL ℝ)) k`, which additionally requires holomorphy and the cusp
conditions to be preserved. The descent is `HeckeSlash/ModularForm.lean`. -/
noncomputable def heckeSlashEnd :
    Module.End ℂ (SlashInvariantForm (G.map (mapGL ℝ)) k) where
  toFun := heckeSlashInvariant k D
  map_add' f g := by ext τ; simp [heckeSlashInvariant, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [heckeSlashInvariant,
      heckeSlashSum_smul k D (det_rightCosetRep_pos D (ModularForm.map_mapGL_le_glpos G) hD)]

/-- The endomorphism is `heckeSlashSum` on underlying functions. This characterises it directly,
without exposing the bundling. -/
@[simp] lemma coe_heckeSlashEnd (f : SlashInvariantForm (G.map (mapGL ℝ)) k) :
    ⇑(heckeSlashEnd k D hD f) = heckeSlashSum k D f := (rfl)

end HeckeRing.GL2
