/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Cusps
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Invariance
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-!
# The upper-triangular Hecke operator on `M_k(Γ₁(N))` and `S_k(Γ₁(N))`

The four analytic inputs for `heckeSlashUpperTri` are in place — holomorphy
(`UpperTri/Holomorphic.lean`), boundedness and vanishing at every cusp (`UpperTri/Cusps.lean`),
the `q`-expansion (`UpperTri/QExpansion.lean`) — and `UpperTri/Invariance.lean` supplies the
missing algebraic one: at `p ∣ N` the sum preserves `Γ₁(N)`-invariance. This file assembles them
into the operator itself, a `ℂ`-linear endomorphism of `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`
and of `CuspForm ((Gamma1 N).map (mapGL ℝ)) k`, and records the two facts that make it usable:
it preserves each nebentypus space `M_k(N, χ)`, `S_k(N, χ)`, and on `q`-expansions it is
`aₘ ↦ a_{p m}`.

This is Layer 2(b) of the ModularForms roadmap at a level divisible by `p`. When `p` is prime,
the classical `Tₚ` for `p ∤ N` needs one further coset representative and is not built here;
at `p ∣ N` the classical `Tₚ` *is* this operator, which is why the corresponding prime Hecke
recurrence carries no `χ(p) p^{k-1}` term. Following Miyake, Diamond–Shurman and Shimura, no
separate `Uₚ` is introduced.

## Where the level enters

`HeckeSlash/ModularForm.lean` already descends the *general double-coset* sum to forms, but only
at level `𝒮ℒ`, where invariance is Shimura's Proposition 3.37 and no congruence condition is
involved. Neither file implies the other: that one has an arbitrary double coset and the full
modular group, this one has a fixed family of representatives and a congruence subgroup, and it
is the congruence condition `p ∣ N` that makes the upper-triangular representatives suffice.

The cusp conditions ask for `Subgroup.IsArithmetic` on the level, which `(Gamma1 N).map (mapGL ℝ)`
carries through `CongruenceSubgroup.instFiniteIndexGamma1` once `N ≠ 0`. Invariance is carried
rationally throughout `UpperTri/Invariance.lean`, so the one place the `ℚ`/`ℝ` bridge is needed
is `ModularForm.rat_slash_mapGL`, from `ModularForms/SlashActionRat.lean`.

## Main definitions

* `HeckeRing.GL2.heckeSlashUpperTriModularFormEnd`: the operator on `M_k(Γ₁(N))`, bundled as a
  `Module.End ℂ`.
* `HeckeRing.GL2.heckeSlashUpperTriCuspFormEnd`: the operator on `S_k(Γ₁(N))` — the statement
  that it preserves cuspidality.

## Main results

* `HeckeRing.GL2.coe_heckeSlashUpperTriModularFormEnd`,
  `HeckeRing.GL2.coe_heckeSlashUpperTriCuspFormEnd`: both are `heckeSlashUpperTri` on underlying
  functions.
* `HeckeRing.GL2.heckeSlashUpperTriModularFormEnd_mem_modFormCharSpace`,
  `HeckeRing.GL2.heckeSlashUpperTriCuspFormEnd_mem_cuspFormCharSpace`: **the operator preserves
  the nebentypus**.
* `HeckeRing.GL2.qExpansion_coeff_heckeSlashUpperTriModularFormEnd`,
  `HeckeRing.GL2.qExpansion_coeff_heckeSlashUpperTriCuspFormEnd`: the coefficient at `m` is the
  coefficient of the original form at `p m`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2–5.3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)

/-- Slash-invariance of a form at level `Γ₁(N)`, transported to the rational action — the
hypothesis `UpperTri/Invariance.lean` asks for. -/
private lemma rat_slash_eq_of_mem_Gamma1 {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma1 N) : (⇑f) ∣[k] (mapGL ℚ δ : GL (Fin 2) ℚ) = ⇑f := by
  rw [ModularForm.rat_slash_mapGL]
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hδ)

/-- The width of `∞` for `Γ₁(N)` is `1`, so all `q`-expansions below are taken at width `1`. -/
private lemma one_mem_strictPeriods_Gamma1 :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

variable [NeZero N]

/-- **The upper-triangular sum acting on modular forms of level `Γ₁(N)`**, for `p ∣ N`.
Invariance is `heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1`, holomorphy is
`mdifferentiable_heckeSlashUpperTri`, and boundedness at the cusps is
`isBoundedAt_heckeSlashUpperTri`. The public interface is the bundled
`heckeSlashUpperTriModularFormEnd`. -/
private noncomputable def heckeSlashUpperTriModularForm (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := heckeSlashUpperTri k p f
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
    let _ : NeZero p := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩
    rw [← ModularForm.rat_slash_mapGL]
    exact heckeSlashUpperTri_slash_mapGL_of_mem_Gamma1 k hpN hδ
      fun _ hε ↦ rat_slash_eq_of_mem_Gamma1 k f hε
  holo' := mdifferentiable_heckeSlashUpperTri k p (ModularFormClass.holo f)
  bdd_at_cusps' hc :=
    isBoundedAt_heckeSlashUpperTri k p (fun _ h ↦ ModularFormClass.bdd_at_cusps f h) hc

private lemma coe_heckeSlashUpperTriModularForm (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashUpperTriModularForm k hpN f) = heckeSlashUpperTri k p f := (rfl)

/-- **The upper-triangular sum acting on cusp forms of level `Γ₁(N)`** — the statement that the
action preserves cuspidality. Only the vanishing field is new: invariance and holomorphy come
from the underlying modular form, so neither is proved twice. -/
private noncomputable def heckeSlashUpperTriCuspForm (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  { heckeSlashUpperTriModularForm k hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) with
    zero_at_cusps' := fun {c} hc ↦ by
      -- Reduce the cusp-form structure literal to its bundled modular-form field.
      change c.IsZeroAt
        (⇑(heckeSlashUpperTriModularForm k hpN (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))) k
      rw [coe_heckeSlashUpperTriModularForm]
      exact isZeroAt_heckeSlashUpperTri k p (fun _ h ↦ CuspFormClass.zero_at_cusps f h) hc }

private lemma coe_heckeSlashUpperTriCuspForm (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashUpperTriCuspForm k hpN f) = heckeSlashUpperTri k p f := (rfl)

/-- **The upper-triangular Hecke operator on `M_k(Γ₁(N))`**, for `p ∣ N`, as a `ℂ`-linear
endomorphism. Bundling is what lets Hecke operators compose and later carry a ring structure. -/
noncomputable def heckeSlashUpperTriModularFormEnd (hpN : p ∣ N) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeSlashUpperTriModularForm k hpN
  map_add' f g := by
    ext τ; simp [coe_heckeSlashUpperTriModularForm, heckeSlashUpperTri_add]
  map_smul' c f := by
    ext τ; simp [coe_heckeSlashUpperTriModularForm, heckeSlashUpperTri_smul]

/-- **The upper-triangular Hecke operator on `S_k(Γ₁(N))`**, for `p ∣ N`. -/
noncomputable def heckeSlashUpperTriCuspFormEnd (hpN : p ∣ N) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeSlashUpperTriCuspForm k hpN
  map_add' f g := by
    ext τ; simp [coe_heckeSlashUpperTriCuspForm, heckeSlashUpperTri_add]
  map_smul' c f := by
    ext τ; simp [coe_heckeSlashUpperTriCuspForm, heckeSlashUpperTri_smul]

/-- The operator is `heckeSlashUpperTri` on underlying functions. -/
@[simp] lemma coe_heckeSlashUpperTriModularFormEnd (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashUpperTriModularFormEnd k hpN f) = heckeSlashUpperTri k p f := (rfl)

/-- The operator is `heckeSlashUpperTri` on underlying functions. -/
@[simp] lemma coe_heckeSlashUpperTriCuspFormEnd (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashUpperTriCuspFormEnd k hpN f) = heckeSlashUpperTri k p f := (rfl)

/-- **The operator preserves the nebentypus**: it maps `M_k(N, χ)` into itself. Not an
assumption but a theorem: the factorisation of `UpperTri/Invariance.lean` replaces a `Γ₀(N)`
matrix by one with the same lower-right entry modulo `N`, so the character value is unchanged. -/
theorem heckeSlashUpperTriModularFormEnd_mem_modFormCharSpace (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeSlashUpperTriModularFormEnd k hpN f ∈ modFormCharSpace k χ := by
  let _ : NeZero p := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩
  rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [coe_heckeSlashUpperTriModularFormEnd, ← ModularForm.rat_slash_mapGL]
  exact heckeSlashUpperTri_slash_mapGL_of_nebentypus k hpN χ g
    fun δ ↦ by rw [ModularForm.rat_slash_mapGL]; exact hf δ

/-- **The operator preserves the nebentypus on cusp forms**: it maps `S_k(N, χ)` into itself. -/
theorem heckeSlashUpperTriCuspFormEnd_mem_cuspFormCharSpace (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeSlashUpperTriCuspFormEnd k hpN f ∈ cuspFormCharSpace k χ := by
  let _ : NeZero p := ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))⟩
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [coe_heckeSlashUpperTriCuspFormEnd, ← ModularForm.rat_slash_mapGL]
  exact heckeSlashUpperTri_slash_mapGL_of_nebentypus k hpN χ g
    fun δ ↦ by rw [ModularForm.rat_slash_mapGL]; exact hf δ

/-- **The `q`-expansion recurrence**: the coefficient at `m` is `a_{p m}(f)` for `p ∣ N`.
When `p` is prime, this is the Diamond–Shurman recurrence
`aₘ(Tₚ f) = a_{m p}(f) + χ(p) p^{k-1} a_{m/p}(f)` in the case that makes the second term vanish,
`χ(p) = 0`. -/
theorem qExpansion_coeff_heckeSlashUpperTriModularFormEnd (hpN : p ∣ N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashUpperTriModularFormEnd k hpN f)).coeff m
      = (qExpansion 1 f).coeff (p * m) := by
  rw [coe_heckeSlashUpperTriModularFormEnd]
  exact qExpansion_coeff_heckeSlashUpperTri' k p one_mem_strictPeriods_Gamma1
    (Nat.pos_of_ne_zero fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))) f m

/-- **The `q`-expansion recurrence on cusp forms**: the coefficient at `m` is `a_{p m}(f)` for
`p ∣ N`. -/
theorem qExpansion_coeff_heckeSlashUpperTriCuspFormEnd (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeSlashUpperTriCuspFormEnd k hpN f)).coeff m
      = (qExpansion 1 f).coeff (p * m) := by
  rw [coe_heckeSlashUpperTriCuspFormEnd]
  exact qExpansion_coeff_heckeSlashUpperTri' k p one_mem_strictPeriods_Gamma1
    (Nat.pos_of_ne_zero fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hpN))) f m

end HeckeRing.GL2

end
