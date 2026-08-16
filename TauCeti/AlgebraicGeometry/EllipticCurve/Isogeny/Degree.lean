/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Algebra.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
import Mathlib.NumberTheory.FunctionField
-- witnesses inside the proofs below; it appears in no statement here.
import TauCeti.FieldTheory.IntermediateField.FieldRange

/-!
# The degree of an isogeny

The degree of an isogeny `φ : W₁ → W₂` of affine Weierstrass curves over a field `F` is the
dimension of `W₁.FunctionField` over the image of the function-field pullback `φ.fieldPullback`
— the pulled-back copy of `W₂.FunctionField`, which that pullback embeds isomorphically. No
properness, smoothness or separability input is involved: the degree is field theory.

That reading is only honest once the extension is known to be finite, since `Module.finrank`
of an infinite extension reads `0`. Finiteness holds for every isogeny, and this file proves
it: the pullback of the affine coordinate is transcendental over `F`
(`TauCeti.Isogeny.transcendental_pullback_X`), so the pulled-back function field already
contains a transcendental element `t`, and `F(W₁)` is finite over `F(t)` because it is finite
over the rational function field. Positivity of the degree follows at once, and degree one reads
as an isomorphism on function fields.

Multiplicativity under composition is the `finrank` tower formula, applied to
`F(W₃) → F(W₂) → F(W₁)`. The pulled-back copies of `F(W₂)` and `F(W₃)` are subfields of
`F(W₁)`, so the tower is stated through `TauCeti.Isogeny.degree_eq_finrank`, which reads a
degree off any algebra structure whose structure map is the pullback.

## Main definitions

* `TauCeti.Isogeny.degree`: the degree of an isogeny, with `TauCeti.Isogeny.degree_def` the
  equation lemma the module boundary makes necessary.

## Main results

* `TauCeti.Isogeny.finiteDimensional`: **automatic finiteness** — the extension a degree
  measures is finite, the inseparable case included.
* `TauCeti.Isogeny.degree_eq_finrank`: the degree read off an arbitrary algebra structure
  induced by the pullback.
* `TauCeti.Isogeny.finiteDimensional_functionField`: the function-field extension is finite, for
  any algebra structure whose structure map is the pullback.
* `TauCeti.Isogeny.degree_pos`: an isogeny has positive degree.
* `TauCeti.Isogeny.degree_eq_one_iff`: degree one means the function-field pullback is onto;
  `TauCeti.Isogeny.degree_id` is the identity's case, and is the `@[simp]` normal form of a
  degree.
* `TauCeti.Isogeny.degree_comp`: **the tower formula** `deg (ψ ∘ φ) = deg ψ * deg φ`.

These are the `Isogeny.finiteDimensional` and `degree_pos` seeds of
`TauCetiRoadmap/EllipticCurves/Suggested.lean` together with the degree multiplicativity named
in `README.md` §Layer 1. The mathematics is Silverman, *The Arithmetic of Elliptic Curves*,
II.2.4(a) and II.2.4(c) — where finiteness of the extension is exactly what makes a nonconstant
map of curves finite.

`degree` is the coordinate-ring form of D. Angdinata's function-field definition, as the
`Isogeny` structure itself is, and `finiteDimensional` is ⚠ mathlib-track material: it is proved
in that shared upstream development, in its function-field form, ahead of the mathlib PRs
(`TauCetiRoadmap/EllipticCurves/README.md` §Provenance). It is built here until those land; the
proofs below are written against the coordinate-ring form rather than ported.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

open IntermediateField Polynomial

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

/-- **The degree of an isogeny**: the dimension of the source function field `W₁.FunctionField`
over the image of `fieldPullback` — the pulled-back copy of the target's function field
`W₂.FunctionField`, which `fieldPullback` embeds isomorphically.

This is Silverman, *The Arithmetic of Elliptic Curves*, II.2.4(a). The extension is finite
(`finiteDimensional` below), so the dimension is honest and positive. -/
noncomputable def degree (φ : Isogeny W₁ W₂) : ℕ :=
  Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField

/-- The defining formula for `degree`. The definition's body is not exposed across the module
boundary, so this is how downstream modules compute with it.

Not `@[simp]`: `degree_id` is the simp-normal form of a degree, and this lemma rewrites its
left-hand side, so tagging both fails `simpNF`. -/
theorem degree_def (φ : Isogeny W₁ W₂) :
    φ.degree = Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField := (rfl)

-- `RatFunc` is opened for the duration of this declaration alone: the algebra structure of
-- `W₁.FunctionField` over the rational function field is a scoped instance upstream, because it
-- is a diamond when the two coincide.
open scoped RatFunc in
/-- **An isogeny has finite degree** (Silverman II.2.4(a)): the extension of `W₁.FunctionField`
over the pulled-back copy of `W₂.FunctionField` is finite, with no separability hypothesis —
purely inseparable isogenies such as Frobenius are covered.

The pulled-back copy contains the pullback `t` of the target's affine coordinate, transcendental
over `F` by `transcendental_pullback_X`, and `W₁.FunctionField` is finite over `F(t)`, because it
is a function field over `F`: finite over the rational function field, by
`WeierstrassCurve.Affine.finiteDimensional_functionField`. Enlarging the base field from `F(t)`
to the whole pulled-back copy keeps it finite. This is where the isogeny hypotheses are spent — a
merely arbitrary subfield of `W₁.FunctionField` need not sit under a finite extension. -/
instance finiteDimensional (φ : Isogeny W₁ W₂) :
    FiniteDimensional φ.fieldPullback.fieldRange W₁.FunctionField := by
  set t := φ.pullback (algebraMap F[X] W₂.CoordinateRing X) with ht_def
  have hle : F⟮t⟯ ≤ φ.fieldPullback.fieldRange :=
    adjoin_simple_le_iff.2
      ⟨algebraMap W₂.CoordinateRing W₂.FunctionField (algebraMap F[X] W₂.CoordinateRing X), by
        simp [ht_def]⟩
  have : FiniteDimensional F⟮t⟯ W₁.FunctionField :=
    FunctionField.finiteDimensional_of_adjoin_transcendental φ.transcendental_pullback_X
  let _ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower F⟮t⟯ φ.fieldPullback.fieldRange W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IntermediateField.coe_inclusion hle z).symm
  exact Module.Finite.of_restrictScalars_finite F⟮t⟯ _ _

/-- **The degree read off any algebra structure induced by the pullback.** The function-field
pullback identifies `W₂.FunctionField` with the subfield of `W₁.FunctionField` that `degree`
measures against, so the two dimensions agree. Stated for an arbitrary algebra structure whose
structure map is the pullback, rather than for one fixed choice: registering such a structure
globally would create a diamond, since different isogenies induce different ones. -/
theorem degree_eq_finrank (φ : Isogeny W₁ W₂) [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.degree = Module.finrank W₂.FunctionField W₁.FunctionField :=
  φ.degree_def.trans (AlgHom.finrank_fieldRange φ.fieldPullback h)


/-- **The degree of an isogeny is positive.** The extension is finite and the source function
field is nontrivial. -/
theorem degree_pos (φ : Isogeny W₁ W₂) : 0 < φ.degree := by
  rw [degree_def]
  exact Module.finrank_pos

/-- **An isogeny's function-field extension is finite.**

`Isogeny.finiteDimensional` gives this over `φ.fieldPullback.fieldRange`; this is the same fact for
any algebra structure whose structure map is the pullback, which is the form consumers hold. It
takes the same hypothesis as `degree_eq_finrank`, and needs nothing beyond it: every isogeny has
positive degree, and the degree *is* the relevant `finrank`. -/
theorem finiteDimensional_functionField (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    FiniteDimensional W₂.FunctionField W₁.FunctionField :=
  FiniteDimensional.of_finrank_pos (φ.degree_eq_finrank h ▸ φ.degree_pos)

/-- The degree of an isogeny is nonzero, the `≠` form of `degree_pos`. -/
@[simp]
theorem degree_ne_zero (φ : Isogeny W₁ W₂) : φ.degree ≠ 0 :=
  φ.degree_pos.ne'

/-- **Degree one means an isomorphism of function fields.** The degree measures
`W₁.FunctionField` over the image of `fieldPullback`, so it is one exactly when that image is
everything. -/
theorem degree_eq_one_iff (φ : Isogeny W₁ W₂) :
    φ.degree = 1 ↔ Function.Surjective φ.fieldPullback := by
  rw [degree_def, IntermediateField.finrank_eq_one_iff_eq_top, AlgHom.fieldRange_eq_top]

/-- The identity isogeny has degree one: its function-field pullback is the identity, so the
extension it measures is trivial. -/
@[simp]
theorem degree_id (W : WeierstrassCurve.Affine F) : (id W).degree = 1 :=
  (degree_eq_one_iff _).2 <| by rw [id_fieldPullback]; exact Function.surjective_id

/-- **The degree is multiplicative under composition** (Silverman II.2.4(c)): the tower formula
for `F(W₃) ⊆ F(W₂) ⊆ F(W₁)`, the inclusions being the pullbacks. -/
@[simp]
theorem degree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).degree = ψ.degree * φ.degree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have htower : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, comp_fieldPullback]
  have hφ : ∀ z, algebraMap _ _ z = φ.fieldPullback z :=
    φ.fieldPullback.algebraMap_toAlgebra_apply
  have hψ : ∀ z, algebraMap _ _ z = ψ.fieldPullback z :=
    ψ.fieldPullback.algebraMap_toAlgebra_apply
  have hc : ∀ z, algebraMap _ _ z = (ψ.comp φ).fieldPullback z :=
    (ψ.comp φ).fieldPullback.algebraMap_toAlgebra_apply
  rw [φ.degree_eq_finrank hφ, ψ.degree_eq_finrank hψ, (ψ.comp φ).degree_eq_finrank hc]
  exact (Module.finrank_mul_finrank W₃.FunctionField W₂.FunctionField W₁.FunctionField).symm

end Isogeny

end TauCeti
