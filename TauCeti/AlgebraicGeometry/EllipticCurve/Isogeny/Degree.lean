/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
import Mathlib.NumberTheory.FunctionField

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
over the rational function field. Positivity of the degree follows at once, and so does the
converse reading of degree one: an isogeny of degree one is an isomorphism on function fields.

Multiplicativity under composition is the `finrank` tower formula, applied to
`F(W₃) → F(W₂) → F(W₁)`. The pulled-back copies of `F(W₂)` and `F(W₃)` are subfields of
`F(W₁)`, so the tower is stated through `TauCeti.Isogeny.degree_eq_finrank`, which reads a
degree off any algebra structure whose structure map is the pullback.

## Main definitions

* `TauCeti.Isogeny.degree`: the degree of an isogeny, with `TauCeti.Isogeny.degree_def` the
  equation lemma the module boundary makes necessary.

## Main results

* `TauCeti.Isogeny.exists_transcendental_mem_fieldRange`: the pulled-back function field is not
  contained in the constants.
* `TauCeti.Isogeny.finiteDimensional`: **automatic finiteness** — the extension a degree
  measures is finite, the inseparable case included.
* `TauCeti.Isogeny.degree_eq_finrank`: the degree read off an arbitrary algebra structure
  induced by the pullback.
* `TauCeti.Isogeny.degree_pos`: an isogeny has positive degree; `TauCeti.Isogeny.degree_id`
  computes the identity's, and is the `@[simp]` normal form of a degree.
* `TauCeti.Isogeny.degree_comp`: **the tower formula** `deg (ψ ∘ φ) = deg ψ * deg φ`.
* `TauCeti.Isogeny.degree_eq_one_iff`: degree one means the function-field pullback is onto.

These are the `Isogeny.finiteDimensional` and `degree_pos` seeds of
`TauCetiRoadmap/EllipticCurves/Suggested.lean` together with the degree multiplicativity named
in `README.md` §Layer 1; the proofs are original. The mathematics is Silverman, *The Arithmetic
of Elliptic Curves*, II.2.4(a) and II.2.4(c) — where finiteness of the extension is exactly what
makes a nonconstant map of curves finite.

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

/-- **The pulled-back function field contains a transcendental element**: the pullback of the
affine coordinate `x` of the target, which `transcendental_pullback_X` places outside the
constants. This is the input to finiteness, and it is where the isogeny hypotheses are spent —
a merely arbitrary subfield of `W₁.FunctionField` need not sit under a finite extension. -/
theorem exists_transcendental_mem_fieldRange (φ : Isogeny W₁ W₂) :
    ∃ t ∈ φ.fieldPullback.fieldRange, Transcendental F t :=
  ⟨φ.pullback (algebraMap F[X] W₂.CoordinateRing X),
    ⟨algebraMap W₂.CoordinateRing W₂.FunctionField (algebraMap F[X] W₂.CoordinateRing X), by
      simp⟩,
    φ.transcendental_pullback_X⟩

open scoped RatFunc in
/-- **An isogeny has finite degree** (Silverman II.2.4(a)): the extension of `W₁.FunctionField`
over the pulled-back copy of `W₂.FunctionField` is finite, with no separability hypothesis —
purely inseparable isogenies such as Frobenius are covered.

The pulled-back copy contains an element `t` transcendental over `F`, and `W₁.FunctionField` is
finite over `F(t)`, because it is a function field over `F`: finite over the rational function
field, by `WeierstrassCurve.Affine.finiteDimensional_functionField`. Enlarging the base field
from `F(t)` to the whole pulled-back copy keeps it finite.

`RatFunc` is opened for the duration of this declaration alone: the algebra structure of
`W₁.FunctionField` over the rational function field is a scoped instance upstream, because it
is a diamond when the two coincide. -/
instance finiteDimensional (φ : Isogeny W₁ W₂) :
    FiniteDimensional φ.fieldPullback.fieldRange W₁.FunctionField := by
  obtain ⟨t, htmem, ht⟩ := φ.exists_transcendental_mem_fieldRange
  have hle : F⟮t⟯ ≤ φ.fieldPullback.fieldRange := adjoin_simple_le_iff.2 htmem
  have : FiniteDimensional F⟮t⟯ W₁.FunctionField :=
    FunctionField.finiteDimensional_of_adjoin_transcendental ht
  let _ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower F⟮t⟯ φ.fieldPullback.fieldRange W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Module.Finite.of_restrictScalars_finite F⟮t⟯ _ _

/-- **The degree read off any algebra structure induced by the pullback.** The function-field
pullback identifies `W₂.FunctionField` with the subfield of `W₁.FunctionField` that `degree`
measures against, so the two dimensions agree. Stated for an arbitrary algebra structure whose
structure map is the pullback, rather than for one fixed choice: registering such a structure
globally would create a diamond, since different isogenies induce different ones. -/
theorem degree_eq_finrank (φ : Isogeny W₁ W₂) [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.degree = Module.finrank W₂.FunctionField W₁.FunctionField := by
  have hsquare : (algebraMap φ.fieldPullback.fieldRange W₁.FunctionField).comp
      φ.fieldPullback.equivFieldRange.toRingEquiv.toRingHom =
      (RingEquiv.refl W₁.FunctionField).toRingHom.comp
        (algebraMap W₂.FunctionField W₁.FunctionField) := by
    ext z
    exact (AlgHom.equivFieldRange_apply_coe φ.fieldPullback z).trans (h z).symm
  exact (Algebra.finrank_eq_of_equiv_equiv φ.fieldPullback.equivFieldRange.toRingEquiv
    (RingEquiv.refl W₁.FunctionField) hsquare).symm

/-- **The degree of an isogeny is positive.** The extension is finite and the source function
field is nontrivial. -/
theorem degree_pos (φ : Isogeny W₁ W₂) : 0 < φ.degree :=
  Module.finrank_pos

/-- The degree of an isogeny is nonzero, the `≠` form of `degree_pos`. -/
@[simp]
theorem degree_ne_zero (φ : Isogeny W₁ W₂) : φ.degree ≠ 0 :=
  φ.degree_pos.ne'

/-- The identity isogeny has degree one: its function-field pullback is the identity, so the
extension it measures is trivial. -/
@[simp]
theorem degree_id (W : WeierstrassCurve.Affine F) : (id W).degree = 1 := by
  have hrange : (id W).fieldPullback.fieldRange = ⊤ := by
    rw [id_fieldPullback]
    exact AlgHom.fieldRange_eq_top.mpr Function.surjective_id
  rw [degree_def, hrange]
  exact IntermediateField.finrank_top

/-- **The degree is multiplicative under composition** (Silverman II.2.4(c)): the tower formula
for `F(W₃) ⊆ F(W₂) ⊆ F(W₁)`, the inclusions being the pullbacks. -/
theorem degree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).degree = ψ.degree * φ.degree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have htower : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      change (ψ.comp φ).fieldPullback z = φ.fieldPullback (ψ.fieldPullback z)
      rw [comp_fieldPullback]
      rfl
  rw [φ.degree_eq_finrank fun _ ↦ rfl, ψ.degree_eq_finrank fun _ ↦ rfl,
    (ψ.comp φ).degree_eq_finrank fun _ ↦ rfl]
  exact (Module.finrank_mul_finrank W₃.FunctionField W₂.FunctionField W₁.FunctionField).symm

/-- **Degree one means an isomorphism of function fields.** The degree measures
`W₁.FunctionField` over the image of `fieldPullback`, so it is one exactly when that image is
everything — the finiteness of the extension being what rules out the degenerate reading of
`finrank`. -/
theorem degree_eq_one_iff (φ : Isogeny W₁ W₂) :
    φ.degree = 1 ↔ Function.Surjective φ.fieldPullback := by
  rw [← AlgHom.fieldRange_eq_top]
  refine ⟨fun h ↦ IntermediateField.eq_of_le_of_finrank_eq' le_top ?_, fun h ↦ ?_⟩
  · rw [IntermediateField.finrank_top, ← degree_def, h]
  · rw [degree_def, h]
    exact IntermediateField.finrank_top

end Isogeny

end TauCeti
