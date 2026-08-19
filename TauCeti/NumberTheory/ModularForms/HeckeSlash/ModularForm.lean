/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Cusps
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Form
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Holomorphic

/-!
# The slash sum descends to modular forms and to cusp forms

`Form.lean` bundles the double coset as an endomorphism of
`SlashInvariantForm (G.map (mapGL ℝ)) k`, and flags that this is *not* the roadmap's Layer 2(b)
target because holomorphy and the cusp conditions are not yet carried along. This file supplies
exactly that: the two remaining structure fields.

Invariance comes from `heckeSlashEnd`, holomorphy from `mdifferentiable_heckeSlashSum`, and
boundedness at the cusps from `isBoundedAt_heckeSlashSum`. Because `heckeSlashEnd` is not
`@[expose]`, a structure field's `.toFun` does not reduce to the coercion by itself, so each
such field names the coercion form with `change`, then rewrites by `coe_heckeSlashEnd`.
The cusp-form case is then *derived* from the modular-form one, adding only `zero_at_cusps'`,
so neither invariance nor holomorphy is proved twice.

Both maps are also bundled as `Module.End ℂ`, which is the form Hecke operators are consumed in:
bundling is what lets them compose and later carry a ring structure.

## The level, and what it has to satisfy

`G` is any subgroup of `SL(2, ℤ)` whose image `G.map (mapGL ℝ)` is arithmetic — the hypothesis
the two cusp lemmas need, and one `(Gamma1 N).map (mapGL ℝ)` carries through
`CongruenceSubgroup.instFiniteIndexGamma1` once `N ≠ 0`. **This is the roadmap's Layer 2(b)
statement**: at `G = Γ₁(N)` and `Δ = Δ₀(N)` the endomorphisms below are the Hecke operators of a
double coset acting on `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`, for an arbitrary double coset of the
Hecke triple, with no divisibility condition relating the level and the determinant. The
`q`-expansion recurrences that identify particular cosets with the classical `Tₙ` are separate
statements and are not proved here.

## Main definitions

* `HeckeRing.GL2.heckeSlashModularFormEnd`: the operator on `ModularForm (G.map (mapGL ℝ)) k`.
* `HeckeRing.GL2.heckeSlashCuspFormEnd`: the operator on `CuspForm (G.map (mapGL ℝ)) k` — the
  statement that the action preserves cuspidality.

## Main results

* `HeckeRing.GL2.coe_heckeSlashModularFormEnd`, `HeckeRing.GL2.coe_heckeSlashCuspFormEnd`: both
  are `heckeSlashSum` on underlying functions.

## Provenance

The shape corresponds to `heckeSlashModularForm`, `heckeSlashCuspForm` and their bundlings in the
AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck). No code is
transcribed, and the level is a general `G` rather than `SL₂(ℤ)`. AINTLIB's
`CuspForm.toModularForm'` is not ported: mathlib already supplies the coercion, as the `CoeTC`
instance of `ModularFormClass` (`Mathlib/NumberTheory/ModularForms/Basic.lean`).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {G : Subgroup SL(2, ℤ)} (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
  [Finite (DecompQuotient (G.map (mapGL ℚ)) (G.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]
  [(G.map (mapGL ℝ)).IsArithmetic]
  (hD : (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ)

/-- **The double coset acting on modular forms.** Invariance is `heckeSlashEnd`, holomorphy is
`mdifferentiable_heckeSlashSum`, and boundedness at the cusps is `isBoundedAt_heckeSlashSum`.
The public interface is the bundled `heckeSlashModularFormEnd`. -/
private noncomputable def heckeSlashModularForm (f : ModularForm (G.map (mapGL ℝ)) k) :
    ModularForm (G.map (mapGL ℝ)) k where
  toSlashInvariantForm := heckeSlashEnd k D hD f.toSlashInvariantForm
  holo' := by
    rw [coe_heckeSlashEnd]; exact mdifferentiable_heckeSlashSum k D f.holo'
  -- `heckeSlashEnd` is unexposed, so the field's `.toFun` does not reduce to the coercion on
  -- its own; `change` names the coercion form, after which `coe_heckeSlashEnd` applies.
  bdd_at_cusps' := fun {c} hc ↦ by
    change c.IsBoundedAt (⇑(heckeSlashEnd k D hD f.toSlashInvariantForm)) k
    rw [coe_heckeSlashEnd]
    exact isBoundedAt_heckeSlashSum k D (fun _ h ↦ f.bdd_at_cusps' h) hc

private lemma coe_heckeSlashModularForm (f : ModularForm (G.map (mapGL ℝ)) k) :
    ⇑(heckeSlashModularForm k D hD f) = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D hD f.toSlashInvariantForm

/-- **The double coset acting on cusp forms** — the action preserves cuspidality. Only the
vanishing field is new: invariance and holomorphy come from `heckeSlashModularForm` at the
underlying modular form, so neither is proved twice. -/
private noncomputable def heckeSlashCuspForm (f : CuspForm (G.map (mapGL ℝ)) k) :
    CuspForm (G.map (mapGL ℝ)) k :=
  { heckeSlashModularForm k D hD (f : ModularForm (G.map (mapGL ℝ)) k) with
    zero_at_cusps' := fun {c} hc ↦ by
      change c.IsZeroAt
        (⇑(heckeSlashModularForm k D hD (f : ModularForm (G.map (mapGL ℝ)) k))) k
      rw [coe_heckeSlashModularForm]
      exact isZeroAt_heckeSlashSum k D (fun _ h ↦ f.zero_at_cusps' h) hc }

private lemma coe_heckeSlashCuspForm (f : CuspForm (G.map (mapGL ℝ)) k) :
    ⇑(heckeSlashCuspForm k D hD f) = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D hD (f : ModularForm (G.map (mapGL ℝ)) k)

/-- **The double coset as a `ℂ`-linear endomorphism of `ModularForm (G.map (mapGL ℝ)) k`.** This
is the form Hecke operators are consumed in: bundling is what lets them compose and later carry a
ring structure. At `G = Γ₁(N)` this is the roadmap's Layer 2(b) operator. -/
noncomputable def heckeSlashModularFormEnd :
    Module.End ℂ (ModularForm (G.map (mapGL ℝ)) k) where
  toFun := heckeSlashModularForm k D hD
  map_add' f g := by ext τ; simp [coe_heckeSlashModularForm, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [coe_heckeSlashModularForm,
      heckeSlashSum_smul k D (det_rightCosetRep_pos D (ModularForm.map_mapGL_le_glpos G) hD)]

/-- **The double coset as a `ℂ`-linear endomorphism of `CuspForm (G.map (mapGL ℝ)) k`** — the
action preserves cuspidality. -/
noncomputable def heckeSlashCuspFormEnd :
    Module.End ℂ (CuspForm (G.map (mapGL ℝ)) k) where
  toFun := heckeSlashCuspForm k D hD
  map_add' f g := by ext τ; simp [coe_heckeSlashCuspForm, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [coe_heckeSlashCuspForm,
      heckeSlashSum_smul k D (det_rightCosetRep_pos D (ModularForm.map_mapGL_le_glpos G) hD)]

/-- The endomorphism is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashModularFormEnd (f : ModularForm (G.map (mapGL ℝ)) k) :
    ⇑(heckeSlashModularFormEnd k D hD f) = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D hD f

/-- The endomorphism is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashCuspFormEnd (f : CuspForm (G.map (mapGL ℝ)) k) :
    ⇑(heckeSlashCuspFormEnd k D hD f) = heckeSlashSum k D f :=
  coe_heckeSlashCuspForm k D hD f

end HeckeRing.GL2

end
