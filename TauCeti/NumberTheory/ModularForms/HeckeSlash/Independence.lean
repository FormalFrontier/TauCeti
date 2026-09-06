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

## Repetition, and where it comes from

`heckeSlashSum_eq_sum_of_rightCosets` asks its family to name each right coset exactly once. The
composite of two slash sums does not: `heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets`
(`HeckeSlash/Composition.lean`) presents that composite as a sum over *pairs* of representatives,
and the products `aᵢ bⱼ` landing in one double coset name each of its right cosets not once but a
fixed number of times — Shimura's multiplicity, by
`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity` and
`DoubleCoset.card_pairs_mem_rightCoset_congr`. So the last statement below trades injectivity for
that uniform repetition count and concludes a multiple of the slash sum, which is the form each
double coset contributes to the multiplicity-weighted composite `∑_D m(D₁, D₂; D) · T_D`.

## Main results

* `HeckeRing.GL2.slash_eq_of_rightCoset_eq`: slashing a `Γ₁`-invariant function by `x` depends
  only on the right coset `Γ₁ x`.
* `HeckeRing.GL2.heckeSlashSum_eq_sum_of_rightCosets`: **the choice-free description of the
  slash sum.** For `Γ₁`-invariant `f`, `heckeSlashSum k D f = ∑ᵢ f ∣[k] aᵢ` for any family
  `(aᵢ)` whose right cosets `Γ₁ aᵢ` are distinct and cover the double coset.
* `HeckeRing.GL2.heckeSlashSum_eq_sum_of_mem_doubleCoset`: the special case that fixes the
  choice of double-coset representative only: any `δ ∈ Γ₁ D.out Γ₂` gives the same sum.
* `HeckeRing.GL2.sum_slash_eq_nsmul_heckeSlashSum`: **the weighted collapse.** A family naming
  each right coset of the double coset exactly `m` times — repetitions allowed, covering not
  assumed — sums to `m • heckeSlashSum k D f`.
* `HeckeRing.GL2.sum_slash_coe_eq_nsmul_heckeSlashSum`: the weighted collapse for a form,
  whose slash-invariance discharges `hf`.
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

omit [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)] in
/-- **Two families of representatives of the same right cosets are matched by a bijection.**
If the cosets `Γ₁ aᵢ` are pairwise distinct and cover `Γ₁ D.out Γ₂`, then the index type `ι` is
matched with `DecompQuotient Γ₂ Γ₁ (D.out)⁻¹` — the index `heckeSlashSum` sums over — by a
bijection `φ` carrying each `Γ₁ aᵢ` to `Γ₁ (rightCosetRep D (φ i))`.

This is pure coset bookkeeping: no slash, no weight and no character appears, and it is what makes
a sum over one family equal to the sum over the other. Both the unweighted
`heckeSlashSum_eq_sum_of_rightCosets` below and the nebentypus-weighted
`twistedHeckeSlashSum_eq_sum_of_rightCosets` of `HeckeSlash/Nebentypus/Independence.lean` consume
it, and differ only in the per-summand lemma they then supply. -/
theorem exists_bijective_rightCosetRep_smul_eq {ι : Type*} (a : ι → GL (Fin 2) ℚ)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂ =
      ⋃ i, MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ))) :
    ∃ φ : ι → DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹, Function.Bijective φ ∧
      ∀ i, MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op (rightCosetRep D (φ i)) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
  classical
  -- Mathlib's own lemma; stated for a submonoid, so `Γ₁` is passed through `toSubmonoid`.
  have hself : ∀ x : GL (Fin 2) ℚ, x ∈ MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) := fun x ↦
    mem_own_rightCoset Γ₁.toSubmonoid x
  -- Each family's cosets occur in the other: every `aᵢ` lies in the double coset, and every
  -- chosen representative lies in some `Γ₁ aᵢ`, two right cosets that meet being equal.
  choose φ hφ using fun i ↦ exists_rightCosetRep_smul_eq D
    (hcover ▸ Set.mem_iUnion_of_mem i (hself (a i)))
  have key' : ∀ v, ∃ i, MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    intro v
    have hmem := rightCosetRep_mem_doubleCoset D v
    rw [hcover] at hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    exact ⟨i, (rightCoset_eq_iff Γ₁).mpr (by simpa using inv_mem ((mem_rightCoset_iff _).mp hi))⟩
  -- Indices with the same image under `φ` name the same coset of the family `(aᵢ)`, which `hinj`
  -- then identifies; stated separately so that `hinj` is applied to this equality itself.
  have hcoset : ∀ i j, φ i = φ j → MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
      MulOpposite.op (a j) • (Γ₁ : Set (GL (Fin 2) ℚ)) := fun i j hij ↦ by
    rw [hφ i, hφ j, hij]
  refine ⟨φ, ⟨fun i j hij ↦ hinj (hcoset i j hij), fun v ↦ ?_⟩, hφ⟩
  obtain ⟨i, hi⟩ := key' v
  exact ⟨i, (op_rightCosetRep_smul_injective D (hi.trans (hφ i))).symm⟩

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
  let _ : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) := Fintype.ofFinite _
  obtain ⟨φ, hbij, hφ⟩ := exists_bijective_rightCosetRep_smul_eq D a hcover hinj
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

/-- **A family naming each right coset the same number of times sums to a multiple of the slash
sum.** In place of the injectivity of `heckeSlashSum_eq_sum_of_rightCosets`, ask that every right
coset of the double coset be named by exactly `m` members of the family: then the sum over the
family is `m • heckeSlashSum k D f`.

Covering is not a hypothesis. A right coset named by no member forces `m = 0`, and then both
sides vanish; for `m ≠ 0` the family does cover, so nothing is lost by leaving it out and a user
holding only a set of products need not prove it.

This is the shape the composite of two slash sums arrives in. Grouping the products `aᵢ bⱼ` of
`heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets` by the double coset they lie in, the group
belonging to one double coset meets each of that coset's right cosets the same number of times
(`DoubleCoset.card_pairs_mem_rightCoset_congr`), and that common count is Shimura's multiplicity
(`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`) — so each group contributes
`m(D₁, D₂; D) • heckeSlashSum k D f`. -/
theorem sum_slash_eq_nsmul_heckeSlashSum {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ) (m : ℕ)
    (hmem : ∀ i, a i ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂)
    (hcard : ∀ x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂,
      Nat.card {i // MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))} = m)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    ∑ i, f ∣[k] a i = m • heckeSlashSum k D f := by
  classical
  let _ : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) := Fintype.ofFinite _
  choose g hg using fun i ↦ exists_rightCosetRep_smul_eq D (hmem i)
  rw [heckeSlashSum_def, Finset.smul_sum,
    ← Finset.sum_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_univ (g i)) fun i ↦ f ∣[k] a i]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- On the fibre of `v` every term is the slash by `v`'s representative, so the fibre
  -- contributes its cardinality times that one value.
  rw [Finset.sum_congr rfl fun i hi ↦
      slash_eq_of_rightCoset_eq k hf ((Finset.mem_filter.mp hi).2 ▸ hg i), Finset.sum_const]
  -- That cardinality is `m`: the fibre of `v` is the set of indices naming `v`'s right coset,
  -- since `g i` and `v` name the same coset exactly when they are equal.
  have hfib : (Finset.univ.filter fun i ↦ g i = v) =
      Finset.univ.filter fun i ↦ MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op (rightCosetRep D v) • (Γ₁ : Set (GL (Fin 2) ℚ)) :=
    Finset.filter_congr fun i _ ↦
      ⟨fun h ↦ h ▸ hg i, fun h ↦ op_rightCosetRep_smul_injective D ((hg i).symm.trans h)⟩
  have hm := hcard _ (rightCosetRep_mem_doubleCoset D v)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hm
  rw [hfib, hm]

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

/-- **The weighted collapse for a form of level `G.map (mapGL ℝ)`.** This is
`sum_slash_eq_nsmul_heckeSlashSum` with the hypothesis `hf` discharged, exactly as
`heckeSlashSum_coe_eq_sum_of_rightCosets` discharges it for the unweighted statement: a form of
that level is slash-invariant under `G.map (mapGL ℚ)` by `ModularForm.slash_eq_of_mem_map_mapGL`.

`F` is any type of slash-invariant forms, so this covers `SlashInvariantForm`, `ModularForm` and
`CuspForm` at once, and a consumer working on a character space need not rebuild the invariance
bridge. -/
theorem sum_slash_coe_eq_nsmul_heckeSlashSum {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) ℚ)
    (m : ℕ)
    (hmem : ∀ i, a i ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
    (hcard : ∀ x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (G.map (mapGL ℚ)) (G.map (mapGL ℚ)),
      Nat.card {i // MulOpposite.op (a i) • (G.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op x • (G.map (mapGL ℚ) : Set (GL (Fin 2) ℚ))} = m)
    (f : F) : ∑ i, ⇑f ∣[k] a i = m • heckeSlashSum k D ⇑f :=
  sum_slash_eq_nsmul_heckeSlashSum k D a m hmem hcard ⇑f fun _ hγ ↦
    ModularForm.slash_eq_of_mem_map_mapGL
      (fun γ' hγ' ↦ SlashInvariantFormClass.slash_action_eq f γ' hγ') hγ

end Form

end HeckeRing.GL2

end
