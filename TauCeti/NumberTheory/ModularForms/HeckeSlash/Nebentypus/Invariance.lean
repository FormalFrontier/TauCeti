/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Ring

/-!
# The twisted slash sum preserves the character space

`HeckeSlash/Nebentypus/Basic.lean` defines `twistedHeckeSlashSum`, weighting each summand of a
double-coset sum by `delta0NebentypusChar χ` of its own representative, and says twice over that
the point of the weighting is left unproved: the sum is meant to be well defined on, and to
preserve, the `χ`-invariant functions. `HeckeSlash/Nebentypus/Ring.lean` names that subspace,
`functionCharSpace`, and repeats the omission. This file supplies what both defer.

## Why the weights are exactly right

The whole proof rests on one observation. Write `χ' = delta0NebentypusChar N χ`, a monoid hom on
`Δ₀(N)`, and read the summands of the twisted sum as the *weighted slash* `χ' x • (f ∣[k] x)` at
`x ∈ Δ₀(N)`. For `f` in the character space and `γ ∈ Γ₀(N)` this quantity is unchanged when `x`
is multiplied on the left by `γ`: slashing by `γ` scales `f` by the nebentypus `χ (d_γ)`, while the
weight picks up `χ' γ`, and `Delta0UpperUnit_mapGL` says the two are mutually inverse. So the
weighted slash is a function of the right coset `Γ₀(N) x` alone — which is precisely the
representative-independence the unweighted `heckeSlashSum` lacks on a `χ`-eigenfunction, and the
reason the character has to enter as `χ'` rather than as `χ ∘ Gamma0Map`.

Granted that, the argument is Shimura's Proposition 3.37 unchanged, exactly as in
`HeckeSlash/Invariance.lean`: right multiplication by `γ` permutes the right cosets, the
permutation is `MulAction.toPerm` at `γ⁻¹`, and the only new bookkeeping is that a *right* factor
of `γ` scales the weight by `χ (d_γ)`, which comes back out of the sum as the eigenvalue the
conclusion asserts.

## Main results

* `HeckeRing.GL2.delta0NebentypusChar_smul_slash_mapGL_mul`: the weighted slash absorbs a left
  factor from `Γ₀(N)`.
* `HeckeRing.GL2.mul_inv_mem_Delta0`: the unnormalised representatives `δ h⁻¹` lie in `Δ₀(N)`.
* `HeckeRing.GL2.delta0NebentypusChar_smul_slash_eq_nebentypusWeight_smul_slash`: an unnormalised
  representative carries the same weighted slash as the chosen one.
* `HeckeRing.GL2.twistedHeckeSlashSum_mem_functionCharSpace`: **the twisted slash sum of a
  `χ`-invariant function is `χ`-invariant.**

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSlashGen_preserves_invariant` (line 457) is the theorem below, with
`twisted_weighted_slash_tRep_gen_of_mem` (line 319) and `delta0Nebentypus_left_weight` (line 391)
its per-summand and weight-transformation steps.

Only the statements are taken. The source reaches them through some 210 lines of
adjugate-and-correction plumbing — `gamma0Correction`, `gamma0_adjugate_decomp_eq`,
`gamma0TripleDelta`, `slash_GL_adjugate_triple_eq_correction_slash`,
`gamma0TripleDelta_left_eq_h_mul_deltaRep`, `twistedHeckeSlashGen_perm_summand` and their helpers
— which stands in for a substrate this repository already has in stronger form: the permutation
argument of `HeckeSlash/Invariance.lean` at an arbitrary Hecke triple, the per-summand step
`slash_rightCosetRep_of_mem` of `HeckeSlash/Reindex.lean`, and above all `Delta0UpperUnit` as a
`MonoidHom`, which makes the multiplicativity the source proves by hand (`delta0UpperUnit_mul`,
`delta0IntegralMatrix_mul`) free here. None of that plumbing is transcribed, and the source's
own `delta0Nebentypus_left_weight` is re-derived from that `MonoidHom` structure rather than
ported.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5 (Hecke operators with nebentypus), and §3.4, Proposition 3.37 for the permutation argument.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- **The weighted slash absorbs a left factor from `Γ₀(N)`.** For `f` in the character space,
`γ ∈ Γ₀(N)` and `x ∈ Δ₀(N)`, `χ' (γ x) • (f ∣[k] γ x) = χ' x • (f ∣[k] x)`, where
`χ' = delta0NebentypusChar N χ`.

This is the reason the twisting works: the weighted slash depends only on the right coset
`Γ₀(N) x`, so the summands of `twistedHeckeSlashSum` do not see the representative the definition
chooses, even though `f` is merely a `χ`-eigenfunction and not invariant. The two factors that
cancel are the eigenvalue `χ (d_γ)` the slash picks up and the weight `χ' γ`, which
`Delta0UpperUnit_mapGL` makes its inverse.

The product is taken as a separate variable `y` with `hxy` naming it, rather than written into the
statement, so that a caller which has the factorisation in hand does not have to rewrite inside the
`Δ₀(N)`-membership proof the character carries as data. -/
lemma delta0NebentypusChar_smul_slash_mapGL_mul (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ)
    (γ : ↥(Gamma0 N)) {x y : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) (hy : y ∈ Delta0 N)
    (hxy : y = (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) * x) :
    (delta0NebentypusChar N χ ⟨y, hy⟩ : ℂ) • (f ∣[k] y) =
      (delta0NebentypusChar N χ ⟨x, hx⟩ : ℂ) • (f ∣[k] x) := by
  subst hxy
  -- The weight of the product splits, and on `Γ₀(N)` the twisting character inverts `Gamma0Map`.
  have hweight : (delta0NebentypusChar N χ
      ⟨(mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) * x, hy⟩ : ℂ) =
      (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ)⁻¹ * (delta0NebentypusChar N χ ⟨x, hx⟩ : ℂ) := by
    rw [show (⟨(mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) * x, hy⟩ : Delta0 N) =
        ⟨_, mapGL_mem_Delta0 N γ⟩ * ⟨x, hx⟩ from rfl,
      map_mul, Units.val_mul, delta0NebentypusChar_mapGL, Units.val_inv_eq_inv_val]
  -- Slashing by `γ` scales `f` by the nebentypus, and the scalar passes back out through `x`:
  -- every element of `Δ₀(N)` is an integral matrix of positive determinant.
  rw [hweight, SlashAction.slash_mul, ModularForm.rat_slash_mapGL,
    (mem_functionCharSpace_iff k χ f).mp hf γ,
    ModularForm.rat_smul_slash_of_det_pos k (posDetInt_le_glpos 2 (Delta0_le_posDetInt N hx)) f _,
    smul_smul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

variable (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- The unnormalised representatives `δ h⁻¹`, for `h` anywhere in `Γ₀(N)`, lie in `Δ₀(N)`. This is
`rightCosetRep_mem_Delta0` with the chosen representative `τᵥ` replaced by an arbitrary `h`, which
is the generality the reindexing step below needs; that lemma is the case `h = τᵥ`. -/
lemma mul_inv_mem_Delta0 {h : GL (Fin 2) ℚ} (hh : h ∈ (Gamma0 N).map (mapGL ℚ)) :
    (D.out : GL (Fin 2) ℚ) * h⁻¹ ∈ Delta0 N :=
  mul_mem D.out.2 (Gamma0Image_le_Delta0 N (by
    rw [Subgroup.mem_toSubmonoid, Gamma0Image_def]
    exact inv_mem hh))

/-- **An unnormalised representative carries the same weighted slash as the chosen one.** If `h` in
`Γ₀(N)` has class `w`, then the weighted slash at `δ h⁻¹` is the `w`-th summand of
`twistedHeckeSlashSum`.

This is the twisted counterpart of `slash_rightCosetRep_of_mem_right` in `HeckeSlash/Reindex.lean`:
there the *unweighted* slash is unchanged because `f` is `Γ₀(N)`-invariant, here the weight supplies
exactly the character factor that invariance would otherwise have given. The two representatives
differ on the left by `δ (h⁻¹ τ_w) δ⁻¹`, which `conj_mem_of_mk_eq` puts in `Γ₀(N)`, so
`delta0NebentypusChar_smul_slash_mapGL_mul` applies.

The class is taken as a variable `w` named by `hcls`, rather than written as `⟦h⟧`, because that is
how the reindexing consumes it: there `w` arrives as `g⁻¹ • v` and `hcls` is
`MulAction.Quotient.mk_smul_out`. -/
lemma delta0NebentypusChar_smul_slash_eq_nebentypusWeight_smul_slash (f : ℍ → ℂ)
    (hf : f ∈ functionCharSpace k χ) {h : GL (Fin 2) ℚ} (hh : h ∈ (Gamma0 N).map (mapGL ℚ))
    {w : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹}
    (hcls : (⟦⟨h, hh⟩⟧ : DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹) = w) :
    (delta0NebentypusChar N χ ⟨(D.out : GL (Fin 2) ℚ) * h⁻¹, mul_inv_mem_Delta0 D hh⟩ : ℂ) •
        (f ∣[k] ((D.out : GL (Fin 2) ℚ) * h⁻¹)) =
      (nebentypusWeight χ D w : ℂ) • (f ∣[k] rightCosetRep D w) := by
  subst hcls
  rw [nebentypusWeight_def]
  -- `h` and the chosen `τ_w` have the same class, so `δ (h⁻¹ τ_w) δ⁻¹` lies in `Γ₀(N)`; name an
  -- integral witness for it, since the absorption lemma is stated at `mapGL ℚ`.
  have hX : (D.out : GL (Fin 2) ℚ) * (h⁻¹ *
      (((⟦⟨h, hh⟩⟧ : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (D.out : GL (Fin 2) ℚ)⁻¹).out : ↥((Gamma0 N).map (mapGL ℚ))) : GL (Fin 2) ℚ)) *
      (D.out : GL (Fin 2) ℚ)⁻¹ ∈ (Gamma0 N).map (mapGL ℚ) := by
    -- `simpa` is wrong here: it rewrites the `Subgroup.map` membership into an existential and
    -- then cannot match. Only `inv_inv` is needed, and the class must be pinned explicitly or the
    -- `Quotient.out_eq` argument is left as a metavariable.
    have hconj := conj_mem_of_mk_eq ((D.out : GL (Fin 2) ℚ)⁻¹)
      (Quotient.out_eq (⟦⟨h, hh⟩⟧ : DecompQuotient ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)).symm
    rwa [inv_inv] at hconj
  obtain ⟨σ, hσ, hσX⟩ := Subgroup.mem_map.mp hX
  refine delta0NebentypusChar_smul_slash_mapGL_mul k χ f hf ⟨σ, hσ⟩
    (rightCosetRep_mem_Delta0 D _) (mul_inv_mem_Delta0 D hh) ?_
  rw [rightCosetRep_def,
    show (mapGL ℚ ((⟨σ, hσ⟩ : ↥(Gamma0 N)) : SL(2, ℤ)) : GL (Fin 2) ℚ) = mapGL ℚ σ from rfl, hσX]
  group

variable [NeZero N]

/-- The enumeration `∑` needs, chosen exactly as in `HeckeSlash/Nebentypus/Basic.lean` so that the
two sums are the same term. -/
noncomputable local instance :
    Fintype (DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The twisted slash sum of a `χ`-invariant function is `χ`-invariant.** This is the pay-off of
the weighting, which `HeckeSlash/Nebentypus/Basic.lean` and `HeckeSlash/Nebentypus/Ring.lean` both
state and defer: `twistedHeckeSlashSum k χ D` maps `functionCharSpace k χ` into itself, so the
twisted operators live on the character space where the unweighted `heckeSlashSum` does not.

The proof is Shimura's Proposition 3.37 with the character carried through. Right multiplication by
`γ` permutes the right cosets — the permutation is `MulAction.toPerm` at `γ⁻¹`, exactly as in
`HeckeSlash/Invariance.lean` — and the one new step is that a right factor of `γ` multiplies a
summand's weight by `χ (d_γ)⁻¹`, so that eigenvalue comes back out of the sum and is what the
conclusion asserts. -/
theorem twistedHeckeSlashSum_mem_functionCharSpace (f : ℍ → ℂ)
    (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ D f ∈ functionCharSpace k χ := by
  -- Membership is the nebentypus relation, but `Submodule` membership does not present the `∀` to
  -- `intro` on its own.
  rw [mem_functionCharSpace_iff]
  intro γ
  -- `γ` is needed in two spellings: integral, to carry the character, and in the rational copy of
  -- `Γ₀(N)` the Hecke triple is built from, which is what acts on the coset index.
  have hmem : (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ (Gamma0 N).map (mapGL ℚ) :=
    Subgroup.mem_map.mpr ⟨_, γ.2, rfl⟩
  have hgΔ : (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) ∈ Delta0 N := mapGL_mem_Delta0 N γ
  -- Slashing the `v`-th weighted summand by `γ` gives `χ (d_γ)` times the summand at `γ⁻¹ • v`.
  have hperm (v : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹) :
      ((nebentypusWeight χ D v : ℂ) • (f ∣[k] rightCosetRep D v)) ∣[k]
          (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) =
        (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) •
          ((nebentypusWeight χ D ((⟨_, hmem⟩ : ↥((Gamma0 N).map (mapGL ℚ)))⁻¹ • v) : ℂ) •
            (f ∣[k] rightCosetRep D ((⟨_, hmem⟩ : ↥((Gamma0 N).map (mapGL ℚ)))⁻¹ • v))) := by
    have hh : ((mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)⁻¹ * (v.out : GL (Fin 2) ℚ)) ∈
        (Gamma0 N).map (mapGL ℚ) := mul_mem (inv_mem hmem) v.out.2
    -- `aᵥ γ = δ τᵥ⁻¹ γ = δ (γ⁻¹ τᵥ)⁻¹`: an unnormalised representative of the class `γ⁻¹ • v`.
    have hx : rightCosetRep D v * (mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) =
        (D.out : GL (Fin 2) ℚ) *
          ((mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)⁻¹ * (v.out : GL (Fin 2) ℚ))⁻¹ := by
      rw [rightCosetRep_def]
      group
    -- Its weight is `Wᵥ · χ (d_γ)⁻¹`, because the twisting character is multiplicative on `Δ₀(N)`
    -- and inverts the nebentypus on `Γ₀(N)`.
    have hw : (nebentypusWeight χ D v : ℂ) = (↑(χ ((Gamma0Map N).toHomUnits γ)) : ℂ) *
        (delta0NebentypusChar N χ ⟨(D.out : GL (Fin 2) ℚ) *
          ((mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)⁻¹ * (v.out : GL (Fin 2) ℚ))⁻¹,
          mul_inv_mem_Delta0 D hh⟩ : ℂ) := by
      rw [show (⟨(D.out : GL (Fin 2) ℚ) *
              ((mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ)⁻¹ * (v.out : GL (Fin 2) ℚ))⁻¹,
            mul_inv_mem_Delta0 D hh⟩ : Delta0 N) =
          ⟨rightCosetRep D v, rightCosetRep_mem_Delta0 D v⟩ * ⟨_, hgΔ⟩ from Subtype.ext hx.symm,
        map_mul, Units.val_mul, delta0NebentypusChar_mapGL, Units.val_inv_eq_inv_val,
        nebentypusWeight_def]
      field_simp
    rw [ModularForm.rat_smul_slash_of_det_pos k
        (posDetInt_le_glpos 2 (Delta0_le_posDetInt N hgΔ)) _ _,
      ← SlashAction.slash_mul, hx, hw, mul_smul]
    exact congrArg _ (delta0NebentypusChar_smul_slash_eq_nebentypusWeight_smul_slash k χ D f hf hh
      (MulAction.Quotient.mk_smul_out _ (⟨_, hmem⟩ : ↥((Gamma0 N).map (mapGL ℚ)))⁻¹ v))
  rw [← ModularForm.rat_slash_mapGL, twistedHeckeSlashSum_def, SlashAction.sum_slash,
    Finset.smul_sum]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨_, hmem⟩ : ↥((Gamma0 N).map (mapGL ℚ)))⁻¹) _ _
    fun v ↦ by simpa only [MulAction.toPerm_apply] using hperm v

end HeckeRing.GL2

end
