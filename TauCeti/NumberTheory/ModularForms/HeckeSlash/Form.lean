/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Invariance

/-!
# The slash sum as an operator on slash-invariant forms

`Invariance.lean` proves that `heckeSlashSum k D f` is `SL₂(ℤ)`-invariant when `f` is. This file
packages that into a map `SlashInvariantForm 𝒮ℒ k → SlashInvariantForm 𝒮ℒ k`, which is the point
at which the double coset finally acts on *forms* rather than on raw functions `ℍ → ℂ`.

## Crossing from `ℚ` to `ℝ`

The two sides speak different languages, and reconciling them is most of this file.
`SlashInvariantForm Γ k` is indexed by a subgroup of `GL(2, ℝ)`, and `𝒮ℒ` is the range of
`mapGL ℝ`; the invariance theorem is stated at `SLnZ 2`, the range of `mapGL ℚ`, under the
rational slash action. Both are ranges of `mapGL` out of the *same* `SL₂(ℤ)`, so mathlib's
`Matrix.SpecialLinearGroup.map_mapGL` — `(mapGL S g).map (algebraMap S T) = mapGL T g` for a
scalar tower — relates them directly at `ℤ → ℚ → ℝ`. Both directions of the bridge are corollaries
of it, and `ModularForm.rat_slash` turns each rational slash into the real one.

## Main definitions

* `HeckeRing.GL2.heckeSlashEnd`: the same map bundled as a `ℂ`-linear endomorphism. This is an
  intermediate step toward Layer 2(b), which asks for endomorphisms of `ModularForm` at level
  `Γ₁(N)`; the descent — holomorphy and the cusp conditions — is not formalised here.

## Main results

* `HeckeRing.GL2.coe_heckeSlashEnd`: the endomorphism is `heckeSlashSum` on functions.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): `glMap_mem_SL`,
`mem_SL_exists_H` and `heckeSlashInvariant`. AINTLIB's `glMap` wrapper and its `glMap_mapGL_eq`
have no counterpart here: `Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` is already the map, and
mathlib's `Matrix.SpecialLinearGroup.map_mapGL` is already the identity relating the two ranges.

These are the bridging helpers that earlier files in this chain deliberately avoided: carrying
slash-invariance rationally kept `Reindex.lean` and `Invariance.lean` free of them, and this is
the file that pays for that choice, once, where the `ℝ`-indexed `SlashInvariantForm` makes it
unavoidable.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The double coset acting on slash-invariant forms.** The underlying function is
`heckeSlashSum`, and its invariance is `heckeSlashSum_slash_invariant_of_mem_SLnZ` transported
across the `SLnZ 2` ↔ `𝒮ℒ` correspondence.

⚠ As in `Invariance.lean`, this is the sum over the representatives `heckeSlashSum` fixes; no
claim is made that different choices of representatives give the same form. -/
private noncomputable def heckeSlashInvariant (f : SlashInvariantForm 𝒮ℒ k) :
    SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlashSum k D f
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := ModularForm.exists_mem_SLnZ_of_mem_SL hγ
    rw [← ModularForm.rat_slash]
    exact heckeSlashSum_slash_invariant_of_mem_SLnZ k D f
      (fun _ h ↦ ModularForm.slash_eq_of_mem_SLnZ k f.slash_action_eq' h) hδ

/-- **The double coset as a `ℂ`-linear endomorphism of `SlashInvariantForm 𝒮ℒ k`.** Bundling it
as a `Module.End ℂ` is what lets Hecke operators compose and later carry a ring structure.
Linearity is `heckeSlashSum_add`, which needs no hypothesis, together with `heckeSlashSum_smul`,
which needs the two factors of each representative to have positive determinant. At this coset
that is `SLnZ_le_posDetInt` and `D.out.2`, since both flanking groups and the ambient submonoid
are `SL₂(ℤ)` and `posDetInt 2`.

⚠ This is an intermediate step, not the roadmap's Layer 2(b) target: that asks for endomorphisms
of `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`, which additionally requires holomorphy and the
cusp conditions to be preserved, and at level `Γ₁(N)` rather than `𝒮ℒ`. The descent is not
formalised here. -/
noncomputable def heckeSlashEnd : Module.End ℂ (SlashInvariantForm 𝒮ℒ k) where
  toFun := heckeSlashInvariant k D
  map_add' f g := by ext τ; simp [heckeSlashInvariant, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [heckeSlashInvariant,
      heckeSlashSum_smul k D
      (det_transposeRep_pos D (SLnZ_le_glpos 2) (posDetInt_le_glpos 2 D.out.2))]

/-- The endomorphism is `heckeSlashSum` on underlying functions. This characterises it directly,
without exposing the bundling. -/
@[simp] lemma coe_heckeSlashEnd (f : SlashInvariantForm 𝒮ℒ k) :
    ⇑(heckeSlashEnd k D f) = heckeSlashSum k D f := (rfl)

end HeckeRing.GL2
