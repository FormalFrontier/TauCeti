/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Algebra.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower
-- witnesses inside the proofs below; it appears in no statement here.
import TauCeti.FieldTheory.IntermediateField.FieldRange

/-!
# Separable and inseparable degrees of an isogeny

`TauCeti.Isogeny.degree` is the dimension of `W₁.FunctionField` over the image of `fieldPullback`.
That extension is finite, so it splits the degree into a separable and an inseparable part, and
this file names those two parts and records that they multiply to the degree.

## Main definitions

* `TauCeti.Isogeny.separableDegree`: the separable degree of the function-field extension.
* `TauCeti.Isogeny.inseparableDegree`: its inseparable degree.

## Main results

* `TauCeti.Isogeny.separableDegree_eq_finSepDegree` and
  `TauCeti.Isogeny.inseparableDegree_eq_finInsepDegree`: the two degrees read off an arbitrary
  algebra structure induced by the pullback, rather than over the field range — the separable
  analogues of `degree_eq_finrank`, and how a caller relates these numbers to
  `W₂.FunctionField`.
* `TauCeti.Isogeny.separableDegree_mul_inseparableDegree`: the two multiply to `degree`.
* `TauCeti.Isogeny.separableDegree_pos` and `TauCeti.Isogeny.inseparableDegree_pos`: both are
  positive, so neither factor is degenerate.
* `TauCeti.Isogeny.separableDegree_id` and `TauCeti.Isogeny.inseparableDegree_id`: both are `1`
  for the identity isogeny.
* `TauCeti.Isogeny.separableDegree_comp` and `TauCeti.Isogeny.inseparableDegree_comp`: both are
  multiplicative under composition, matching `degree_comp`.
* `TauCeti.Isogeny.separableDegree_eq_degree_of_isSeparable` and
  `TauCeti.Isogeny.inseparableDegree_eq_one_of_isSeparable`: a separable isogeny carries its
  whole degree in the separable part.
* `TauCeti.Isogeny.separableDegree_eq_one_of_isPurelyInseparable` and
  `TauCeti.Isogeny.inseparableDegree_eq_degree_of_isPurelyInseparable`: the purely inseparable
  case. No declaration consumes these yet; they are the shape the roadmap's Frobenius milestone
  ("`π_q`, purely inseparable of degree `q`") will need.
* `TauCeti.Isogeny.separableDegree_eq_one_iff_isPurelyInseparable` and
  `TauCeti.Isogeny.inseparableDegree_eq_one_iff_isSeparable`:
  the biconditional forms, for a consumer holding a computed degree rather than an assumed class.

## Design

There is deliberately no `Isogeny.IsSeparable` predicate. Separability of `φ` is
`Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField` — an existing Mathlib class
applied to the extension `degree` already measures — and a wrapper around it would add a second
name for one notion without adding a fact. The same holds for pure inseparability, which is
`IsPurelyInseparable` on the same extension. What is *not* already sayable is the pair of numbers,
so that is what this file adds.

This follows Layer 1 of `TauCetiRoadmap/EllipticCurves/README.md`, which fixes the convention:

> **Degree and separability are field theory.** `deg φ` is `Module.finrank` of `W₁.FunctionField`
> over the fraction field of the pulled-back coordinate ring […]; the separable and inseparable
> degrees, and separability of `φ`, are those of the field extension — Mathlib's existing
> `FieldTheory`, not a flatness theory of morphisms.

Both definitions are unconditional: no separability hypothesis, so purely inseparable isogenies
such as Frobenius are covered, matching `Isogeny.finiteDimensional`.

Multiplicativity under composition is `separableDegree_comp` and `inseparableDegree_comp`, matching
`degree_comp`. Both run the tower `F(W₃) ⊆ F(W₂) ⊆ F(W₁)` against their own Mathlib tower law,
through the transports off `AlgHom.fieldRange` beside `finrank_fieldRange`. The two are not quite
symmetric: the separable law's algebraicity side condition is on the upper extension and the
inseparable law's is on the lower one, so they call `finiteDimensional_of_fieldRange` on `φ` and on
`ψ` respectively.

## Provenance

⚠ *mathlib-track*. `TauCetiRoadmap/EllipticCurves/README.md` tags the Layer-1 first-theory bullet
— which lists "the separable and inseparable degrees" — as "proven in the shared upstream
development, consumed and deduplicated when its PRs land". Those degrees are proved in
D. Angdinata's shared upstream isogeny development in its function-field form, ahead of the
Mathlib PRs; they are built here in the coordinate-ring form this repository's `Isogeny` uses,
until those land. The same note appears in `Degree.lean`, `Basic.lean` and `FunctionField.lean`.

The arithmetic content is Mathlib's — `Field.finSepDegree_mul_finInsepDegree` and the tower laws;
this file transports it to isogenies along `degree_def`. No AINTLIB material is used: that
source's isogeny development carries separability as a hypothesis rather than measuring it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The separable degree of an isogeny**: the separable degree of `W₁.FunctionField` over the
pulled-back copy of the target's function field. -/
noncomputable def separableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField

/-- **The inseparable degree of an isogeny**, of the same extension. -/
noncomputable def inseparableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField

/-- The defining formula for `separableDegree`. The definition's body is not exposed across the
module boundary, so this is how downstream modules compute with it. -/
theorem separableDegree_def (φ : Isogeny W₁ W₂) :
    φ.separableDegree = Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField := (rfl)

/-- The defining formula for `inseparableDegree`. -/
theorem inseparableDegree_def (φ : Isogeny W₁ W₂) :
    φ.inseparableDegree = Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField := (rfl)

/-- **The separable degree read off any algebra structure induced by the pullback**, the
separable analogue of `degree_eq_finrank`. Stated for an arbitrary structure whose map is
`fieldPullback`, since registering one globally would be a diamond. -/
theorem separableDegree_eq_finSepDegree (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.separableDegree = Field.finSepDegree W₂.FunctionField W₁.FunctionField :=
  (φ.separableDegree_def).trans (TauCeti.AlgHom.finSepDegree_fieldRange φ.fieldPullback h)

/-- **The inseparable degree read off any algebra structure induced by the pullback.** -/
theorem inseparableDegree_eq_finInsepDegree (φ : Isogeny W₁ W₂)
    [Algebra W₂.FunctionField W₁.FunctionField]
    (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z) :
    φ.inseparableDegree = Field.finInsepDegree W₂.FunctionField W₁.FunctionField :=
  (φ.inseparableDegree_def).trans (TauCeti.AlgHom.finInsepDegree_fieldRange φ.fieldPullback h)

/-- **The degree factors as separable times inseparable.** This is the field-theoretic
factorisation transported to isogenies; it is what makes "the inseparable part is a Frobenius
power" a statement about `inseparableDegree`. -/
@[simp]
theorem separableDegree_mul_inseparableDegree (φ : Isogeny W₁ W₂) :
    φ.separableDegree * φ.inseparableDegree = φ.degree :=
  (Field.finSepDegree_mul_finInsepDegree _ _).trans φ.degree_def.symm

/-- **Every isogeny has a strictly positive separable degree** — in particular never zero, so this
factor of `separableDegree_mul_inseparableDegree` can be cancelled against `degree`. It is
frequently `1`, which is nondegenerate: by
`separableDegree_eq_one_iff_isPurelyInseparable` it characterises the *purely inseparable*
case. Separability is characterised by inseparable degree `1`. -/
theorem separableDegree_pos (φ : Isogeny W₁ W₂) : 0 < φ.separableDegree := by
  simpa [separableDegree_def] using
    NeZero.pos (Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField)

/-- **Every isogeny has a strictly positive inseparable degree**, likewise never zero, so either
factor of `separableDegree_mul_inseparableDegree` may be cancelled against `degree`. -/
theorem inseparableDegree_pos (φ : Isogeny W₁ W₂) : 0 < φ.inseparableDegree := by
  simpa [inseparableDegree_def] using
    NeZero.pos (Field.finInsepDegree φ.fieldPullback.fieldRange W₁.FunctionField)

/-- The separable degree of an isogeny is nonzero. -/
@[simp]
theorem separableDegree_ne_zero (φ : Isogeny W₁ W₂) : φ.separableDegree ≠ 0 :=
  φ.separableDegree_pos.ne'

/-- The inseparable degree of an isogeny is nonzero. -/
@[simp]
theorem inseparableDegree_ne_zero (φ : Isogeny W₁ W₂) : φ.inseparableDegree ≠ 0 :=
  φ.inseparableDegree_pos.ne'

/-- **The identity isogeny has separable degree one.** -/
@[simp]
theorem separableDegree_id (W : WeierstrassCurve.Affine F) : (id W).separableDegree = 1 := by
  have h : (id W).separableDegree * (id W).inseparableDegree = 1 :=
    ((id W).separableDegree_mul_inseparableDegree.trans (degree_id W))
  exact Nat.eq_one_of_mul_eq_one_right h

/-- **The identity isogeny has inseparable degree one.** -/
@[simp]
theorem inseparableDegree_id (W : WeierstrassCurve.Affine F) : (id W).inseparableDegree = 1 := by
  have h : (id W).separableDegree * (id W).inseparableDegree = 1 :=
    ((id W).separableDegree_mul_inseparableDegree.trans (degree_id W))
  exact Nat.eq_one_of_mul_eq_one_left h

/-- **A separable isogeny has separable degree equal to its degree.** -/
@[simp]
theorem separableDegree_eq_degree_of_isSeparable (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.separableDegree = φ.degree := by
  rw [separableDegree_def, degree_def, Field.finSepDegree_eq_finrank_of_isSeparable]

/-- **A separable isogeny has inseparable degree one.** -/
@[simp]
theorem inseparableDegree_eq_one_of_isSeparable (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.inseparableDegree = 1 := by
  rw [inseparableDegree_def, Algebra.IsSeparable.finInsepDegree_eq]

/-- **A purely inseparable isogeny has separable degree one.** -/
@[simp]
theorem separableDegree_eq_one_of_isPurelyInseparable (φ : Isogeny W₁ W₂)
    [IsPurelyInseparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.separableDegree = 1 := by
  rw [separableDegree_def, IsPurelyInseparable.finSepDegree_eq_one]

/-- **A purely inseparable isogeny carries its whole degree in the inseparable part.** -/
@[simp]
theorem inseparableDegree_eq_degree_of_isPurelyInseparable (φ : Isogeny W₁ W₂)
    [IsPurelyInseparable φ.fieldPullback.fieldRange W₁.FunctionField] :
    φ.inseparableDegree = φ.degree := by
  rw [inseparableDegree_def, degree_def, IsPurelyInseparable.finInsepDegree_eq]

/-- **A separable degree of `1` characterises pure inseparability**, not merely follows from it.

The `@[simp]` lemmas above eliminate an assumed instance; this is the way back, for a consumer
holding a computed degree and wanting the class. Both directions matter once `[n]` and Frobenius
are in play, where the degree is what gets calculated. -/
theorem separableDegree_eq_one_iff_isPurelyInseparable (φ : Isogeny W₁ W₂) :
    φ.separableDegree = 1 ↔
      IsPurelyInseparable φ.fieldPullback.fieldRange W₁.FunctionField :=
  φ.separableDegree_def ▸ (isPurelyInseparable_iff_finSepDegree_eq_one _ _).symm

/-- **An inseparable degree of `1` characterises separability**, the companion of
`separableDegree_eq_one_iff_isPurelyInseparable`. -/
theorem inseparableDegree_eq_one_iff_isSeparable (φ : Isogeny W₁ W₂) :
    φ.inseparableDegree = 1 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField :=
  φ.inseparableDegree_def ▸ (isSeparable_iff_finInsepDegree_eq_one _ _).symm

variable {W₃ : WeierstrassCurve.Affine F}

/-- **The separable degree is multiplicative under composition**, by the tower formula for
`F(W₃) ⊆ F(W₂) ⊆ F(W₁)`, exactly as `degree_comp`. -/
@[simp]
theorem separableDegree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).separableDegree = ψ.separableDegree * φ.separableDegree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, comp_fieldPullback]
  have hφ : ∀ z, algebraMap _ _ z = φ.fieldPullback z :=
    φ.fieldPullback.algebraMap_toAlgebra_apply
  have hψ : ∀ z, algebraMap _ _ z = ψ.fieldPullback z :=
    ψ.fieldPullback.algebraMap_toAlgebra_apply
  have hc : ∀ z, algebraMap _ _ z = (ψ.comp φ).fieldPullback z :=
    (ψ.comp φ).fieldPullback.algebraMap_toAlgebra_apply
  -- discharges the tower law's `[Algebra.IsAlgebraic E K]` side condition
  have _ := TauCeti.AlgHom.finiteDimensional_of_fieldRange φ.fieldPullback hφ
  rw [(ψ.comp φ).separableDegree_eq_finSepDegree hc, ψ.separableDegree_eq_finSepDegree hψ,
    φ.separableDegree_eq_finSepDegree hφ]
  exact (Field.finSepDegree_mul_finSepDegree_of_isAlgebraic W₃.FunctionField W₂.FunctionField
    W₁.FunctionField).symm

/-- **The inseparable degree is multiplicative under composition**, by the inseparable tower
formula for `F(W₃) ⊆ F(W₂) ⊆ F(W₁)` — the inseparable counterpart of `separableDegree_comp`, and
the second factor of `degree_comp`. -/
@[simp]
theorem inseparableDegree_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).inseparableDegree = ψ.inseparableDegree * φ.inseparableDegree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := ψ.fieldPullback.toRingHom.toAlgebra
  let _ := (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
  have : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      simp [RingHom.algebraMap_toAlgebra, comp_fieldPullback]
  have hφ : ∀ z, algebraMap _ _ z = φ.fieldPullback z :=
    φ.fieldPullback.algebraMap_toAlgebra_apply
  have hψ : ∀ z, algebraMap _ _ z = ψ.fieldPullback z :=
    ψ.fieldPullback.algebraMap_toAlgebra_apply
  have hc : ∀ z, algebraMap _ _ z = (ψ.comp φ).fieldPullback z :=
    (ψ.comp φ).fieldPullback.algebraMap_toAlgebra_apply
  -- the inseparable tower law needs `[Algebra.IsAlgebraic F E]`, the *lower* extension — so the
  -- finiteness required here is `ψ`'s, unlike `separableDegree_comp`, which needs `φ`'s
  have _ := TauCeti.AlgHom.finiteDimensional_of_fieldRange ψ.fieldPullback hψ
  rw [(ψ.comp φ).inseparableDegree_eq_finInsepDegree hc,
    ψ.inseparableDegree_eq_finInsepDegree hψ, φ.inseparableDegree_eq_finInsepDegree hφ]
  exact (Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic W₃.FunctionField
    W₂.FunctionField W₁.FunctionField).symm

end Isogeny

end TauCeti
