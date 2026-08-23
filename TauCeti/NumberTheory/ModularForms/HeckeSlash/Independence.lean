/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Reindex

/-!
# The slash sum of an invariant function depends only on the double coset

`heckeSlashSum k D f` is a sum over the *chosen* representatives `D.out` of the double coset and
`v.out` of its right cosets, and `HeckeSlash/Basic.lean` records that on a general `f : ℍ → ℂ`
the value moves with those choices. This file proves that for a `Γ₁`-invariant `f` it does not:
the sum is `∑ᵢ f ∣[k] aᵢ` for **any** family `(aᵢ)` of representatives of the right cosets of
`Γ₁ δ Γ₂`, whatever `δ` in the double coset and whatever representatives are used to name them.

That is what makes the endomorphisms of `HeckeSlash/ModularForm.lean` operators attached to the
double coset rather than to a presentation of it, and it is Shimura's definition (§3.4, (3.4.1)),
which fixes no representatives at all.

## What the choice-freeness rests on

Two families of representatives of the same right cosets differ, coset by coset, by a factor of
`Γ₁` on the **left**, and `f ∣[k] (γ₁ x) = (f ∣[k] γ₁) ∣[k] x = f ∣[k] x` for `γ₁ ∈ Γ₁` when `f`
is `Γ₁`-invariant: that is `slash_eq_of_rightCoset_eq`, and it is the only place invariance is
used. Everything else is a comparison of two enumerations of the same finite set of right
cosets: `DoubleCoset.doubleCoset_eq_iUnion_rightCosets` says the chosen representatives cover
the double coset and `DoubleCoset.op_mul_out_inv_smul_injective` says they do so without
repetition, which are exactly the two hypotheses demanded of the family `(aᵢ)`, so the two
enumerations are matched by a bijection and the sums agree term by term.

The hypotheses are stated with `MulOpposite.op x • (Γ₁ : Set _)` — Mathlib's spelling of the
right coset `Γ₁ x` — so that the two lemmas above are literally what a caller supplies. The
double coset `Γ₁ δ Γ₂` is named as `doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂`; that *set*
depends on no choice, since `DoubleCoset.doubleCoset_eq_of_mem` gives the same set for every
`δ` in it, and `heckeSlashSum_eq_sum_of_mem_doubleCoset` is the resulting statement that any
such `δ` may be used to form the sum.

## Main results

* `HeckeRing.GL2.slash_eq_of_rightCoset_eq`: slashing a `Γ₁`-invariant function by `x` depends
  only on the right coset `Γ₁ x`.
* `HeckeRing.GL2.heckeSlashSum_eq_sum_of_rightCosets`: **the choice-free description of the
  slash sum.** For `Γ₁`-invariant `f`, `heckeSlashSum k D f = ∑ᵢ f ∣[k] aᵢ` for any family
  `(aᵢ)` whose right cosets `Γ₁ aᵢ` are distinct and cover the double coset.
* `HeckeRing.GL2.heckeSlashSum_eq_sum_of_mem_doubleCoset`: the special case that fixes the
  choice of double-coset representative only: any `δ ∈ Γ₁ D.out Γ₂` gives the same sum.
* `HeckeRing.GL2.heckeSlashSum_coe_eq_sum_of_rightCosets`: the same description for a form of
  level `G.map (mapGL ℝ)`, whose slash-invariance discharges the hypothesis `hf`. It is what
  `HeckeSlash/ModularForm.lean` reads off the two exported endomorphisms with, in
  `coe_heckeSlashModularFormEnd_eq_sum` and `coe_heckeSlashCuspFormEnd_eq_sum`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: (3.4.1) defines `f ∣[Γ₁ α Γ₂]ₖ` as the sum over a decomposition `Γ₁ α Γ₂ = ⊔ᵥ Γ₁ aᵥ`,
  and observes that it is independent of the decomposition chosen.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- **Slashing a `Γ₁`-invariant function depends only on the right coset.** If `Γ₁ x = Γ₁ y`
then `f ∣[k] x = f ∣[k] y`, because `y = (y x⁻¹) x` with `y x⁻¹ ∈ Γ₁` and the slash by that
factor is trivial on `f`.

This is the whole role invariance plays in the choice-freeness below: everything else is a
comparison of two enumerations of the same set of cosets. -/
lemma slash_eq_of_rightCoset_eq {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) {x y : GL (Fin 2) ℚ}
    (h : MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op y • (Γ₁ : Set (GL (Fin 2) ℚ))) :
    f ∣[k] x = f ∣[k] y := by
  have hγ : y * x⁻¹ ∈ Γ₁ := (rightCoset_eq_iff Γ₁).mp h
  calc f ∣[k] x = (f ∣[k] (y * x⁻¹)) ∣[k] x := by rw [hf _ hγ]
    _ = f ∣[k] (y * x⁻¹ * x) := (SlashAction.slash_mul k (y * x⁻¹) x f).symm
    _ = f ∣[k] y := by rw [inv_mul_cancel_right]

variable [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- **The slash sum of a `Γ₁`-invariant function is the sum over any decomposition of the double
coset into right cosets.** If the right cosets `Γ₁ aᵢ` are pairwise distinct and cover
`Γ₁ D.out Γ₂`, then `heckeSlashSum k D f = ∑ᵢ f ∣[k] aᵢ`.

So the operator is attached to the double coset itself: the representatives `D.out` and `v.out`
that `heckeSlashSum` happens to pick are one such family (`doubleCoset_eq_iUnion_rightCosets` and
`op_mul_out_inv_smul_injective`), and every other family gives the same function.

Invariance of `f` under `Γ₁` is what the proof uses, once, through
`slash_eq_of_rightCoset_eq`; on a general `f` the statement is false, as `HeckeSlash/Basic.lean`
records. -/
theorem heckeSlashSum_eq_sum_of_rightCosets {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂ =
      ⋃ i, MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    heckeSlashSum k D f = ∑ i, f ∣[k] a i := by
  classical
  -- the enumeration the comparison of sums needs; `heckeSlashSum` fixes one of its own, and the
  -- two agree, no sum here depending on which is chosen
  let _ : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) := Fintype.ofFinite _
  -- Shimura's decomposition, written with the representatives `heckeSlashSum` uses.
  have hcover' : doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂ =
      ⋃ v, MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    simpa only [rightCosetRep_def] using
      doubleCoset_eq_iUnion_rightCosets Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)
  have hinj' : Function.Injective fun v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹ ↦
      MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    simpa only [rightCosetRep_def] using
      op_mul_out_inv_smul_injective Γ₁ Γ₂ (D.out : GL (Fin 2) ℚ)
  have hself : ∀ x : GL (Fin 2) ℚ, x ∈ MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) := fun x ↦
    (mem_rightCoset_iff x).mpr (by simp)
  -- Two right cosets of `Γ₁` that meet are equal, so each family's cosets occur in the other.
  have hmatch : ∀ x y : GL (Fin 2) ℚ, x ∈ MulOpposite.op y • (Γ₁ : Set (GL (Fin 2) ℚ)) →
      MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op y • (Γ₁ : Set (GL (Fin 2) ℚ)) := fun x y hxy ↦
    (rightCoset_eq_iff Γ₁).mpr (by simpa using inv_mem ((mem_rightCoset_iff y).mp hxy))
  have key : ∀ i, ∃ v, MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    intro i
    have hmem : a i ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂ := by
      rw [hcover]; exact Set.mem_iUnion_of_mem i (hself (a i))
    rw [hcover'] at hmem
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
    exact ⟨v, hmatch _ _ hv⟩
  have key' : ∀ v, ∃ i, MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    intro v
    have hmem : rightCosetRep D v ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂ := by
      rw [hcover']; exact Set.mem_iUnion_of_mem v (hself (rightCosetRep D v))
    rw [hcover] at hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact ⟨i, hmatch _ _ hi⟩
  -- The two enumerations are matched by `φ`, and matched cosets have equal slashes.
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹, ∀ i,
      MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op (rightCosetRep D (φ i)) • (Γ₁ : Set (GL (Fin 2) ℚ)) :=
    ⟨fun i ↦ (key i).choose, fun i ↦ (key i).choose_spec⟩
  -- Indices with the same image under `φ` name the same coset of the family `(aᵢ)`, which `hinj`
  -- then identifies; stated separately so that `hinj` is applied to this equality itself.
  have hcoset : ∀ i j, φ i = φ j → MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a j) • (Γ₁ : Set (GL (Fin 2) ℚ)) := fun i j hij ↦ by
    rw [hφ i, hφ j, hij]
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j hij ↦ hinj (hcoset i j hij), fun v ↦ ?_⟩
    obtain ⟨i, hi⟩ := key' v
    exact ⟨i, (hinj' (hi.trans (hφ i))).symm⟩
  rw [heckeSlashSum_def]
  exact (Fintype.sum_bijective φ hbij _ _ fun i ↦ slash_eq_of_rightCoset_eq k hf (hφ i)).symm

/-- **The slash sum may be formed from any representative of the double coset.** For `δ` in
`Γ₁ D.out Γ₂` and `Γ₁`-invariant `f`, summing `f ∣[k] (δ τᵥ⁻¹)` over `Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)` gives
`heckeSlashSum k D f` again — the representative `heckeSlashSum` picks is in no way
distinguished.

This is `heckeSlashSum_eq_sum_of_rightCosets` at the family Shimura's decomposition of
`Γ₁ δ Γ₂` provides, the double coset of `δ` being that of `D.out`
(`DoubleCoset.doubleCoset_eq_of_mem`). -/
theorem heckeSlashSum_eq_sum_of_mem_doubleCoset {δ : GL (Fin 2) ℚ}
    (hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂)
    [Fintype (DecompQuotient Γ₂ Γ₁ δ⁻¹)] (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    heckeSlashSum k D f =
      ∑ v : DecompQuotient Γ₂ Γ₁ δ⁻¹, f ∣[k] (δ * ((v.out : GL (Fin 2) ℚ))⁻¹) := by
  refine heckeSlashSum_eq_sum_of_rightCosets k D _ ?_
    (op_mul_out_inv_smul_injective Γ₁ Γ₂ δ) f hf
  rw [← doubleCoset_eq_of_mem hδ]
  exact doubleCoset_eq_iUnion_rightCosets Γ₁ Γ₂ δ

section Form

variable {G : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
  [SlashInvariantFormClass F (G.map (mapGL ℝ)) k]
  (D : HeckeCoset Δ (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
  [Finite (DecompQuotient (G.map (mapGL ℚ)) (G.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- **The slash sum of a form of level `G.map (mapGL ℝ)` is the sum over any decomposition of the
double coset into right cosets.** This is `heckeSlashSum_eq_sum_of_rightCosets` with the
hypothesis `hf` discharged: a form of that level is slash-invariant under `G.map (mapGL ℚ)` by
`ModularForm.slash_eq_of_mem_map_mapGL`, the `ℚ`/`ℝ` bridge.

`F` is any type of slash-invariant forms, so this covers `SlashInvariantForm`, `ModularForm` and
`CuspForm` at once; combined with the `coe_heckeSlash…End` lemmas it describes the endomorphisms
built from a double coset, at any level, without reference to the representatives they are
assembled from. -/
theorem heckeSlashSum_coe_eq_sum_of_rightCosets {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) (G.map (mapGL ℚ)) (G.map (mapGL ℚ)) =
      ⋃ i, MulOpposite.op (a i) • (G.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦
      MulOpposite.op (a i) • (G.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
    (f : F) : heckeSlashSum k D ⇑f = ∑ i, ⇑f ∣[k] a i :=
  heckeSlashSum_eq_sum_of_rightCosets k D a hcover hinj ⇑f fun _ hγ ↦
    ModularForm.slash_eq_of_mem_map_mapGL
      (fun γ' hγ' ↦ SlashInvariantFormClass.slash_action_eq f γ' hγ') hγ

end Form

end HeckeRing.GL2

end
