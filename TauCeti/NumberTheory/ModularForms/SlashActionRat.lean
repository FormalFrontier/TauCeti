/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The weight-`k` slash action of `GL(2, ℚ)`

Mathlib defines the slash action of `GL(2, ℝ)` on `ℍ → ℂ` and specialises it to `SL(2, ℤ)`
through `monoidHomSlashAction`. The Hecke operators need the group in between: their coset
representatives are *rational* matrices of positive determinant — `Δ₀(N)` is a submonoid of
`GL(2, ℚ)` — and they are slashed against functions invariant under an integral congruence
subgroup.

This file supplies that action, by the same mechanism Mathlib uses for `SL(2, ℤ)`: transport
along the entrywise map `GL(2, ℚ) →* GL(2, ℝ)`. It is a `scoped instance`, so a module that does
not want `f ∣[k] g` to elaborate at rational `g` simply does not open the scope.

`f ∣[k] g` is the real slash at the mapped matrix *definitionally*, so every `GL(2, ℝ)` lemma
applies after rewriting with `rat_slash`; the point of the instance is that consumers need
not insert the coercion by hand.

## The `SLnZ 2` / `𝒮ℒ` bridge

`SlashInvariantForm` and friends are indexed by subgroups of `GL(2, ℝ)`, while the Hecke
development works at `SLnZ 2 ≤ GL(2, ℚ)` under the rational action defined here. Both `SLnZ 2`
and `𝒮ℒ` are ranges of `mapGL` out of the same `SL₂(ℤ)`, so mathlib's
`Matrix.SpecialLinearGroup.map_mapGL` relates them directly and the two membership directions are
corollaries of it. `slash_eq_of_mem_SLnZ` is the form consumers want: real invariance under `𝒮ℒ`
gives rational invariance under `SLnZ 2`.

The file also carries the rational forms of mathlib's two behaviour-at-`i∞` slash lemmas, in the
`UpperHalfPlane` namespace: they belong beside `rat_slash`, which is the bridge their proofs
cross, rather than in any module about particular matrices.

## Main results

* `ModularForm.rat_slash`: the rational action is the real one at the mapped matrix.
* `SlashInvariantFormClass.slash_eq_of_mem_SLnZ`: a form invariant under `𝒮ℒ` is fixed by the
  rational slash action of every element of `SLnZ 2`.
* `ModularForm.rat_slash_def_of_det_pos`, `ModularForm.rat_slash_apply_of_det_pos`: the expanded
  formula at positive determinant, free of the `σ` twist.
* `ModularForm.det_map_ratCast_pos`: positivity of the determinant survives the embedding.
* `ModularForm.rat_smul_slash_of_det_pos`: scalars pass through the slash of a
  positive-determinant rational matrix, with no `σ` twist.
* `ModularForm.map_ratCast_mem_SL`, `ModularForm.exists_mem_SLnZ_of_mem_SL`: the two directions
  of the `SLnZ 2` / `𝒮ℒ` correspondence.
* `ModularForm.rat_slash_mapGL`: the rational slash at `mapGL ℚ σ` is the real slash at
  `mapGL ℝ σ`, and `ModularForm.slash_eq_of_mem_map_mapGL`,
  `ModularForm.slash_eq_of_mem_map_mapGL_real`: the two directions of slash-invariance under
  the images of a subgroup `G ≤ SL₂(ℤ)` in `GL(2, ℚ)` and in `GL(2, ℝ)`, together with
  `ModularForm.map_mapGL_le_glpos`.
* `ModularForm.slash_eq_of_mem_SLnZ`: real slash-invariance under `𝒮ℒ` gives rational
  slash-invariance under `SLnZ 2`.
* `UpperHalfPlane.IsBoundedAtImInfty.rat_slash`, `UpperHalfPlane.IsZeroAtImInfty.rat_slash`: the
  rational forms of mathlib's `.slash` lemmas — boundedness and vanishing at `i∞` survive a
  rational slash whose matrix has vanishing `(1, 0)` entry.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): the
`SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ)` instance built by `monoidHomSlashAction`, and the
scalar-pull-through step inside its `heckeSlash_smul`. AINTLIB names the embedding `glMap`; that
is a one-use wrapper around Mathlib's `Matrix.GeneralLinearGroup.map`, so it is not ported and
the map is spelled out instead. The scalar lemma is stated here at the `SMul`/`IsScalarTower`
generality of Mathlib's `ModularForm.SL_smul_slash` rather than AINTLIB's `c : ℂ`.

The `SLnZ 2` / `𝒮ℒ` bridge corresponds to AINTLIB's `glMap_mem_SL` and `mem_SL_exists_H` (same
file). AINTLIB's `glMap_mapGL_eq` has no counterpart: mathlib's
`Matrix.SpecialLinearGroup.map_mapGL` already states it for an arbitrary scalar tower.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace ModularForm

/-- The weight-`k` slash action of `GL(2, ℚ)`, induced from `GL(2, ℝ)` along `ℚ ↪ ℝ`. Scoped,
so it is opted into rather than imposed. -/
noncomputable scoped instance ratSlashAction : SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ) :=
  monoidHomSlashAction (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- The rational slash action is the real one at the mapped matrix. Definitional, but named:
it is how every `GL(2, ℝ)` lemma is brought to bear on a rational slash.

The three lemmas here mirror Mathlib's integral trio exactly, including the absence of a `_def`
suffix on this one: `ModularForm.SL_slash` is the transport
(`Mathlib/NumberTheory/ModularForms/SlashActions.lean:155`), `ModularForm.SL_slash_def` the
expanded formula (:158) and `ModularForm.SL_slash_apply` the pointwise one (:162). `_def` marks
the *expanded* statement in this family, not the transport, so it belongs to
`rat_slash_def_of_det_pos` below. -/
lemma rat_slash (k : ℤ) (g : GL (Fin 2) ℚ) (f : ℍ → ℂ) :
    f ∣[k] g = f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) := (rfl)

/-- A rational matrix of positive determinant maps to a real one of positive determinant.
Stated with `Matrix.det`, the form `UpperHalfPlane.σ_eq_refl_of_det_pos` consumes. -/
lemma det_map_ratCast_pos {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    0 < ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using hg

/-- **The expanded formula for a positive-determinant rational slash**, with no `σ` twist:

`f ∣[k] g = fun τ ↦ f (ĝ • τ) * |det ĝ| ^ (k - 1) * denom ĝ τ ^ (-k)`,

where `ĝ` abbreviates `Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g`, the real image of `g`.
The distinction is not cosmetic: `g : GL (Fin 2) ℚ` does not act on `ℍ` at all, and `denom` is
likewise only defined at the real matrix, so every occurrence in the statement below is at `ĝ`.

Mathlib's `ModularForm.slash_def` carries `σ g` around the value of `f`, which is complex
conjugation on the negative-determinant branch. This is the analogue of
`ModularForm.SL_slash_def`, which drops the twist because `det = 1`; here positivity is the
hypothesis that does it. -/
lemma rat_slash_def_of_det_pos (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) :
    f ∣[k] g = fun τ ↦
      f ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • τ) *
        |((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).det : ℝ)| ^ (k - 1) *
          denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ ^ (-k) := by
  rw [rat_slash, _root_.ModularForm.slash_def_of_det_pos k (det_map_ratCast_pos hg)]

/-- The pointwise form of `rat_slash_def_of_det_pos`, matching
`ModularForm.SL_slash_apply`. -/
lemma rat_slash_apply_of_det_pos (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ =
      f ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • τ) *
        |((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).det : ℝ)| ^ (k - 1) *
          denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ ^ (-k) :=
  congrFun (rat_slash_def_of_det_pos k hg f) τ

/-- **Scalars pass through the slash of a positive-determinant rational matrix.** Mathlib's
`ModularForm.smul_slash` carries the twist `σ A c`, which is complex conjugation when the
determinant is negative; on the positive branch `σ` is the identity
(`UpperHalfPlane.σ_eq_refl_of_det_pos`) and the scalar simply commutes.

This is what makes a Hecke operator `ℂ`-linear: it is a sum of slashes by representatives of
positive determinant. The scalar generality matches `ModularForm.SL_smul_slash`, the same
statement for the integral action. -/
@[simp]
lemma rat_smul_slash_of_det_pos {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] (k : ℤ)
    {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k] g = c • f ∣[k] g := by
  rw [rat_slash, rat_slash]
  exact _root_.ModularForm.smul_slash_of_det_pos k (det_map_ratCast_pos hg) f c

/-- An element of `SL₂(ℤ) ≤ GL(2, ℚ)` maps into `𝒮ℒ`. -/
lemma map_ratCast_mem_SL {δ : GL (Fin 2) ℚ} (hδ : δ ∈ SLnZ 2) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) δ ∈ 𝒮ℒ := by
  obtain ⟨s, rfl⟩ := (mem_SLnZ_iff 2).mp hδ
  exact ⟨s, (map_mapGL (R := ℤ) (S := ℚ) (T := ℝ) s).symm⟩

/-- Every element of `𝒮ℒ` is the image of one of `SLnZ 2`. -/
lemma exists_mem_SLnZ_of_mem_SL {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) :
    ∃ δ ∈ SLnZ 2, Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) δ = γ := by
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hγ
  exact ⟨mapGL ℚ s, (mem_SLnZ_iff 2).mpr ⟨s, rfl⟩, map_mapGL (R := ℤ) (S := ℚ) (T := ℝ) s⟩

/-- Real slash-invariance under `𝒮ℒ` gives rational slash-invariance under `SLnZ 2`. -/
lemma slash_eq_of_mem_SLnZ (k : ℤ) {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    {δ : GL (Fin 2) ℚ}
    (hδ : δ ∈ SLnZ 2) : f ∣[k] δ = f := by
  rw [rat_slash]
  exact hf _ (map_ratCast_mem_SL hδ)

/-- **The `ℚ`/`ℝ` bridge for the slash by an integral matrix**: the rational action at
`mapGL ℚ σ` is the real action at `mapGL ℝ σ`. Both are ranges of `mapGL` out of the same
`SL(2, ℤ)`, and mathlib's `Matrix.SpecialLinearGroup.map_mapGL` relates them along `ℤ → ℚ → ℝ`.

This is the one lemma needed to state a hypothesis rationally and consume it at a level
`G.map (mapGL ℝ)`, or the other way about. -/
lemma rat_slash_mapGL (k : ℤ) (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    f ∣[k] (mapGL ℚ σ : GL (Fin 2) ℚ) = f ∣[k] (mapGL ℝ σ : GL (Fin 2) ℝ) := by
  rw [rat_slash, map_mapGL]

/-- Real slash-invariance under the image of `G ≤ SL₂(ℤ)` in `GL(2, ℝ)` — the way a level is
spelled for `SlashInvariantForm` — gives rational slash-invariance under its image in
`GL(2, ℚ)`, which is the way the Hecke triples of `HeckeRing/GL2/` are spelled.
`slash_eq_of_mem_SLnZ` is the case `G = ⊤`, written with the ranges `SLnZ 2` and `𝒮ℒ` that the
level-one development uses. -/
lemma slash_eq_of_mem_map_mapGL {k : ℤ} {G : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ G.map (mapGL ℝ), f ∣[k] γ = f) {δ : GL (Fin 2) ℚ}
    (hδ : δ ∈ G.map (mapGL ℚ)) : f ∣[k] δ = f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hδ
  rw [rat_slash_mapGL]
  exact hf _ (Subgroup.mem_map_of_mem _ hσ)

/-- The converse of `slash_eq_of_mem_map_mapGL`: rational slash-invariance under the image of
`G ≤ SL₂(ℤ)` in `GL(2, ℚ)` gives real slash-invariance under its image in `GL(2, ℝ)`. This is
the direction that discharges the `slash_action_eq'` field of a `SlashInvariantForm`. -/
lemma slash_eq_of_mem_map_mapGL_real {k : ℤ} {G : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hf : ∀ δ ∈ G.map (mapGL ℚ), f ∣[k] δ = f) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ G.map (mapGL ℝ)) : f ∣[k] γ = f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [← rat_slash_mapGL]
  exact hf _ (Subgroup.mem_map_of_mem _ hσ)

/-- The image of `G ≤ SL₂(ℤ)` in `GL(2, ℚ)` consists of matrices of determinant `1`, so it lies
in `GLPos`. This is the hypothesis `det_rightCosetRep_pos` asks of the flanking group. -/
lemma map_mapGL_le_glpos (G : Subgroup SL(2, ℤ)) :
    G.map (mapGL ℚ) ≤ Matrix.GLPos (Fin 2) ℚ := by
  rintro _ ⟨σ, -, rfl⟩
  exact SLnZ_le_glpos 2 ((mem_SLnZ_iff 2).mpr ⟨σ, rfl⟩)

end ModularForm

namespace UpperHalfPlane

/-- **The rational form of `IsBoundedAtImInfty.slash`.** Mathlib's lemma is stated for the real
slash; the matrix and its hypothesis are given here over `ℚ`, since
`Matrix.GeneralLinearGroup.map` acts entrywise and so carries `g 1 0 = 0` along
`algebraMap ℚ ℝ`. -/
lemma IsBoundedAtImInfty.rat_slash (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0) {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [ModularForm.rat_slash]
  exact hf.slash k (by simp [hg])

/-- **The rational form of `IsZeroAtImInfty.slash`.** -/
lemma IsZeroAtImInfty.rat_slash (k : ℤ) {g : GL (Fin 2) ℚ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0) {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [ModularForm.rat_slash]
  exact hf.slash k (by simp [hg])

end UpperHalfPlane

/-- A form invariant under `𝒮ℒ` is fixed by the rational slash action of every element of
`SLnZ 2`. -/
theorem _root_.SlashInvariantFormClass.slash_eq_of_mem_SLnZ {F : Type*} [FunLike F ℍ ℂ]
    {k : ℤ} [SlashInvariantFormClass F 𝒮ℒ k] (f : F) (γ : GL (Fin 2) ℚ)
    (hγ : γ ∈ SLnZ 2) : ⇑f ∣[k] γ = ⇑f := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp hγ
  have h_mem : mapGL ℝ σ ∈ 𝒮ℒ := MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  rw [ModularForm.rat_slash, map_mapGL]
  exact SlashInvariantFormClass.slash_action_eq f (mapGL ℝ σ) h_mem
