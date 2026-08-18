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

`Form.lean` bundles the double coset as an endomorphism of `SlashInvariantForm 𝒮ℒ k`, and flags
that this is *not* the roadmap's Layer 2(b) target because holomorphy and the cusp conditions are
not yet carried along. This file supplies exactly that: the two remaining structure fields.

Invariance comes from `heckeSlashEnd`, holomorphy from `mdifferentiable_heckeSlashSum`, and
boundedness at the cusps from `isBoundedAt_heckeSlashSum`. Because `heckeSlashEnd` is not
`@[expose]`, a structure field's `.toFun` does not reduce to the coercion by itself, so each
such field names the coercion form with `change`, then rewrites by `coe_heckeSlashEnd`.
The cusp-form case is then *derived* from the modular-form one, adding only
`zero_at_cusps'`, so neither invariance nor holomorphy is proved twice.

Both maps are also bundled as `Module.End ℂ`, which is the form Hecke operators are consumed in:
bundling is what lets them compose and later carry a ring structure.

The level here is `𝒮ℒ`, which carries mathlib's `Subgroup.IsArithmetic` instance — the hypothesis
the two cusp lemmas need. Descending further to `Γ₁(N)` is a separate step.

## Main definitions

* `HeckeRing.GL2.heckeSlashModularFormEnd`: the double coset as a `ℂ`-linear endomorphism of
  `ModularForm 𝒮ℒ k`.
* `HeckeRing.GL2.heckeSlashCuspFormEnd`: the same on `CuspForm 𝒮ℒ k`, which is the statement that
  **the action preserves cuspidality**.

The unbundled constructors behind them are private; the bundled operators are the interface,
since composition is what the Hecke ring will consume.

## Main results

* `HeckeRing.GL2.coe_heckeSlashModularFormEnd`, `coe_heckeSlashCuspFormEnd`: both endomorphisms
  are `heckeSlashSum` on underlying functions.

## Provenance

Shape ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), lines 102-105:
`heckeT_p_cusp`, which assembles a `CuspForm` as `{ heckeT_p … with zero_at_cusps' := … }`. The
assembly is the same; the operator differs, since this repository's `heckeSlashSum` is the general
double-coset sum rather than `T_p`, and the level is `𝒮ℒ` rather than `Γ₁(N)`. AINTLIB's
`CuspForm.toModularForm'` (line 51) is not ported: mathlib already supplies the coercion, as the
`CoeTC` instance of `ModularFormClass` (`Mathlib/NumberTheory/ModularForms/Basic.lean`).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- **The double coset acting on modular forms.** Invariance is `heckeSlashEnd`, holomorphy is
`mdifferentiable_heckeSlashSum`, and boundedness at the cusps is `isBoundedAt_heckeSlashSum`.
The public interface is the bundled `heckeSlashModularFormEnd`. -/
private noncomputable def heckeSlashModularForm (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashEnd k D f.toSlashInvariantForm
  holo' := by
    rw [coe_heckeSlashEnd]; exact mdifferentiable_heckeSlashSum k D f.holo'
  -- `heckeSlashEnd` is unexposed, so the field's `.toFun` does not reduce to the coercion on
  -- its own; `change` names the coercion form, after which `coe_heckeSlashEnd` applies.
  bdd_at_cusps' := fun {c} hc ↦ by
    change c.IsBoundedAt (⇑(heckeSlashEnd k D f.toSlashInvariantForm)) k
    rw [coe_heckeSlashEnd]
    exact isBoundedAt_heckeSlashSum k D (fun _ h ↦ f.bdd_at_cusps' h) hc

private lemma coe_heckeSlashModularForm (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeSlashModularForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashEnd k D f.toSlashInvariantForm

/-- **The double coset acting on cusp forms** — the action preserves cuspidality. Only the
vanishing field is new: invariance and holomorphy come from `heckeSlashModularForm` at the
underlying modular form, so neither is proved twice. -/
private noncomputable def heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k :=
  { heckeSlashModularForm k D (f : ModularForm 𝒮ℒ k) with
    zero_at_cusps' := fun {c} hc ↦ by
      change c.IsZeroAt (⇑(heckeSlashModularForm k D (f : ModularForm 𝒮ℒ k))) k
      rw [coe_heckeSlashModularForm]
      exact isZeroAt_heckeSlashSum k D (fun _ h ↦ f.zero_at_cusps' h) hc }

private lemma coe_heckeSlashCuspForm (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeSlashCuspForm k D f) = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D (f : ModularForm 𝒮ℒ k)

/-- **The double coset as a `ℂ`-linear endomorphism of `ModularForm 𝒮ℒ k`.** This is the form
Hecke operators are consumed in: bundling is what lets them compose and later carry a ring
structure. -/
noncomputable def heckeSlashModularFormEnd : Module.End ℂ (ModularForm 𝒮ℒ k) where
  toFun := heckeSlashModularForm k D
  map_add' f g := by ext τ; simp [coe_heckeSlashModularForm, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [coe_heckeSlashModularForm,
      heckeSlashSum_smul k D
      (det_transposeRep_pos D (SLnZ_le_glpos 2) (posDetInt_le_glpos 2 D.out.2))]

/-- **The double coset as a `ℂ`-linear endomorphism of `CuspForm 𝒮ℒ k`** — the action preserves
cuspidality. -/
noncomputable def heckeSlashCuspFormEnd : Module.End ℂ (CuspForm 𝒮ℒ k) where
  toFun := heckeSlashCuspForm k D
  map_add' f g := by ext τ; simp [coe_heckeSlashCuspForm, heckeSlashSum_add]
  map_smul' c f := by
    ext τ
    simp [coe_heckeSlashCuspForm,
      heckeSlashSum_smul k D
      (det_transposeRep_pos D (SLnZ_le_glpos 2) (posDetInt_le_glpos 2 D.out.2))]

/-- The endomorphism is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashModularFormEnd (f : ModularForm 𝒮ℒ k) :
    ⇑(heckeSlashModularFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashModularForm k D f

/-- The endomorphism is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashCuspFormEnd (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeSlashCuspFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashCuspForm k D f

end HeckeRing.GL2

end
