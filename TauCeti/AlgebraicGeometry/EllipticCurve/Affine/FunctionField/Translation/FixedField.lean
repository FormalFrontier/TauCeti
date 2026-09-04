/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
-- Proof-only: the Galois correspondence for a finite group of automorphisms, with no finiteness
-- hypothesis on the ambient extension.
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The fixed field of a finite group of translations

The point group of an elliptic curve `W` over `F` acts faithfully on the function field `F(W)` by
the pullbacks `τ_P^*` of the translations `τ_P : Q ↦ Q + P`. This file develops the Galois theory
of that action: a subgroup `Φ` of points gives a group `translationSubgroup` of `F`-algebra
automorphisms of `F(W)`, isomorphic to `Φ`, and the functions it fixes form the intermediate field
`translationFixedField`.

For a **finite** `Φ` the extension `F(W) / F(W) ^ Φ` is Galois of degree `#Φ`, and the
correspondence is exact: every automorphism of `F(W)` fixing `F(W) ^ Φ` is a translation by a
point of `Φ`, so `Φ` is recovered from its fixed field and distinct finite subgroups have distinct
fixed fields. Read in the other direction, an intermediate field of finite degree is fixed by only
finitely many translations, at most its degree; a subgroup of points whose fixed field has finite
degree is therefore finite, of exactly that order.

This is the field-theoretic half of the construction of the dual isogeny. That construction reads
a separable isogeny `φ : W₁ → W₂` of degree `n` after base change to a separable closure `Fˢᵉᵖ`,
over which its kernel is a subgroup `Φ` of `n` points of `W₁(Fˢᵉᵖ)`: there `Fˢᵉᵖ(W₁)` is Galois
over the pulled-back copy `φ^*Fˢᵉᵖ(W₂)` with `Φ` acting by translations, and identifying
`φ^*Fˢᵉᵖ(W₂)` as the fixed field of `Φ` is what factors `[n]` through `φ`. Over a base field that
is not separably closed the kernel of `φ` need not be `F`-rational, so the subgroup of points of
`W(F)` used below is in general smaller than that geometric kernel. The degree count and the
correspondence below are what such an identification is read off from; they are stated for an
arbitrary finite subgroup of points, no isogeny being needed to state or prove them.

## Main definitions

* `WeierstrassCurve.Affine.translationSubgroup`: the group of automorphisms `τ_P^*` of `F(W)` for
  `P` in a subgroup `Φ` of the point group.
* `WeierstrassCurve.Affine.translationFixedField`: the intermediate field of functions fixed by
  translation by every point of `Φ`.
* `WeierstrassCurve.Affine.translationFixingSubgroup`: the points whose translation fixes a given
  intermediate field pointwise.

## Main results

* `WeierstrassCurve.Affine.translationMulEquiv`: the translations by `Φ` are a copy of `Φ`.
* `WeierstrassCurve.Affine.finrank_translationFixedField` and
  `WeierstrassCurve.Affine.isGalois_translationFixedField`: for a finite `Φ` the function field is
  Galois of degree `#Φ` over the fixed field.
* `WeierstrassCurve.Affine.fixingSubgroup_translationFixedField`: the automorphisms fixing that
  field are exactly the translations by points of `Φ`, whence
  `WeierstrassCurve.Affine.translationFixingSubgroup_translationFixedField` and
  `WeierstrassCurve.Affine.eq_of_translationFixedField_eq`.
* `WeierstrassCurve.Affine.card_translationFixingSubgroup_le` and
  `WeierstrassCurve.Affine.finite_of_finiteDimensional_translationFixedField`: a degree bounds the
  translations that fix it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : _root_.WeierstrassCurve.Affine F)
  [W.IsElliptic] (Φ Ψ : AddSubgroup (W⁄F).toAffine.Point)

/-- **The group of translations by a subgroup of points**, as a subgroup of the `F`-algebra
automorphisms of the function field: the image of `Φ` under the translation action. -/
noncomputable def translationSubgroup : Subgroup (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  Φ.toSubgroup.map (translationHom W)

/-- **An automorphism lies in `translationSubgroup` exactly when it is a translation by a point of
`Φ`.** -/
@[simp]
theorem mem_translationSubgroup_iff {σ : W.FunctionField ≃ₐ[F] W.FunctionField} :
    σ ∈ translationSubgroup W Φ ↔ ∃ P ∈ Φ, translation W P = σ := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨Multiplicative.toAdd P, hP, (translationHom_apply W P).symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨Multiplicative.ofAdd P, hP, translationHom_apply W (Multiplicative.ofAdd P)⟩

/-- Translation by a point of `Φ` lies in the group of translations by `Φ`. -/
theorem translation_mem_translationSubgroup {P : (W⁄F).toAffine.Point} (hP : P ∈ Φ) :
    translation W P ∈ translationSubgroup W Φ :=
  (mem_translationSubgroup_iff W Φ).mpr ⟨P, hP, rfl⟩

/-- A larger subgroup of points translates by a larger group of automorphisms. -/
theorem translationSubgroup_mono : Monotone (translationSubgroup W) := fun _ _ h _ hσ ↦ by
  obtain ⟨P, hP, rfl⟩ := (mem_translationSubgroup_iff W _).mp hσ
  exact translation_mem_translationSubgroup W _ (h hP)

/-- **Translation identifies a subgroup of points with its group of translations.** The action is
faithful, so `Φ` maps isomorphically onto its image; the point group is written multiplicatively
because the automorphism group is. -/
noncomputable def translationMulEquiv : Multiplicative Φ ≃* translationSubgroup W Φ :=
  Φ.toSubgroup.equivMapOfInjective (translationHom W) (translationHom_injective W)

/-- The isomorphism of a subgroup of points with its translations is translation. -/
@[simp]
theorem translationMulEquiv_apply (P : Multiplicative Φ) :
    (translationMulEquiv W Φ P : W.FunctionField ≃ₐ[F] W.FunctionField) =
      translation W ((Multiplicative.toAdd P : Φ) : (W⁄F).toAffine.Point) :=
  (Subgroup.coe_equivMapOfInjective_apply _ _ _ _).trans (translationHom_apply W _)

instance finite_translationSubgroup [Finite Φ] : Finite (translationSubgroup W Φ) :=
  .of_equiv _ (translationMulEquiv W Φ).toEquiv

/-- A subgroup of points has as many translations as it has points. -/
theorem card_translationSubgroup : Nat.card (translationSubgroup W Φ) = Nat.card Φ :=
  (Nat.card_congr (translationMulEquiv W Φ).toEquiv).symm

/-- **The fixed field of a group of translations**: the functions unmoved by translation by every
point of `Φ`. -/
noncomputable def translationFixedField : IntermediateField F W.FunctionField :=
  IntermediateField.fixedField (translationSubgroup W Φ)

/-- **A function lies in the fixed field exactly when no translation by a point of `Φ` moves
it.** -/
@[simp]
theorem mem_translationFixedField_iff {z : W.FunctionField} :
    z ∈ translationFixedField W Φ ↔ ∀ P ∈ Φ, translation W P z = z := by
  rw [translationFixedField, IntermediateField.mem_fixedField_iff]
  exact ⟨fun h P hP ↦ h _ (translation_mem_translationSubgroup W Φ hP),
    fun h σ hσ ↦ by obtain ⟨P, hP, rfl⟩ := (mem_translationSubgroup_iff W Φ).mp hσ; exact h P hP⟩

/-- A larger subgroup of points fixes a smaller field. -/
theorem translationFixedField_antitone : Antitone (translationFixedField W) := fun _ _ h _ hz ↦
  (mem_translationFixedField_iff W _).mpr fun P hP ↦
    (mem_translationFixedField_iff W _).mp hz P (h hP)

instance finiteDimensional_translationFixedField [Finite Φ] :
    FiniteDimensional (translationFixedField W Φ) W.FunctionField :=
  inferInstanceAs (FiniteDimensional
    (FixedPoints.subfield (translationSubgroup W Φ) W.FunctionField) W.FunctionField)

/-- **The function field is Galois over the fixed field of a finite group of translations.** -/
instance isGalois_translationFixedField [Finite Φ] :
    IsGalois (translationFixedField W Φ) W.FunctionField :=
  IsGalois.of_fixed_field W.FunctionField (translationSubgroup W Φ)

/-- **The function field has degree `#Φ` over the fixed field of a finite subgroup `Φ` of
points.** -/
theorem finrank_translationFixedField [Finite Φ] :
    Module.finrank (translationFixedField W Φ) W.FunctionField = Nat.card Φ := by
  have : Fintype (translationSubgroup W Φ) := Fintype.ofFinite _
  rw [← card_translationSubgroup W Φ, Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card (translationSubgroup W Φ) W.FunctionField

/-- **Every automorphism of the function field fixing the fixed field of a finite subgroup of
points is a translation by a point of that subgroup.** This is the surjectivity half of the Galois
correspondence for the translation action: it is what recognises the extension cut out by `Φ` as
having no automorphisms beyond the translations. -/
theorem fixingSubgroup_translationFixedField [Finite Φ] :
    (translationFixedField W Φ).fixingSubgroup = translationSubgroup W Φ :=
  IntermediateField.fixingSubgroup_fixedField_of_finite (translationSubgroup W Φ)

/-- **The points whose translation fixes an intermediate field pointwise.** -/
noncomputable def translationFixingSubgroup (L : IntermediateField F W.FunctionField) :
    AddSubgroup (W⁄F).toAffine.Point :=
  Subgroup.toAddSubgroup' (L.fixingSubgroup.comap (translationHom W))

/-- **A point fixes an intermediate field exactly when its translation moves no function of that
field.** -/
@[simp]
theorem mem_translationFixingSubgroup_iff {L : IntermediateField F W.FunctionField}
    {P : (W⁄F).toAffine.Point} :
    P ∈ translationFixingSubgroup W L ↔ ∀ z ∈ L, translation W P z = z := by
  rw [translationFixingSubgroup, Subgroup.mem_toAddSubgroup', Subgroup.mem_comap,
    translationHom_apply, IntermediateField.mem_fixingSubgroup_iff]
  rfl

/-- A larger field is fixed by fewer points. -/
theorem translationFixingSubgroup_antitone : Antitone (translationFixingSubgroup W) :=
  fun _ _ h _ hP ↦ (mem_translationFixingSubgroup_iff W).mpr fun z hz ↦
    (mem_translationFixingSubgroup_iff W).mp hP z (h hz)

/-- **The two constructions are adjoint**: a subgroup of points fixes an intermediate field
exactly when that field consists of functions fixed by the subgroup. -/
theorem le_translationFixingSubgroup_iff_le_translationFixedField
    (L : IntermediateField F W.FunctionField) :
    Φ ≤ translationFixingSubgroup W L ↔ L ≤ translationFixedField W Φ :=
  ⟨fun h z hz ↦ (mem_translationFixedField_iff W Φ).mpr fun _P hP ↦
      (mem_translationFixingSubgroup_iff W).mp (h hP) z hz,
    fun h P hP ↦ (mem_translationFixingSubgroup_iff W).mpr fun _z hz ↦
      (mem_translationFixedField_iff W Φ).mp (h hz) P hP⟩

/-- A field is fixed by the translations that fix it. -/
theorem le_translationFixedField_translationFixingSubgroup
    (L : IntermediateField F W.FunctionField) :
    L ≤ translationFixedField W (translationFixingSubgroup W L) :=
  (le_translationFixingSubgroup_iff_le_translationFixedField W _ L).mp le_rfl

/-- **A finite subgroup of points is recovered from its fixed field.** Together with
`WeierstrassCurve.Affine.le_translationFixedField_translationFixingSubgroup` this is the Galois
correspondence for the translation action, in the direction the finite subgroups control. -/
theorem translationFixingSubgroup_translationFixedField [Finite Φ] :
    translationFixingSubgroup W (translationFixedField W Φ) = Φ := by
  ext P
  rw [mem_translationFixingSubgroup_iff,
    ← IntermediateField.mem_fixingSubgroup_iff (translationFixedField W Φ) (translation W P),
    fixingSubgroup_translationFixedField, mem_translationSubgroup_iff]
  exact ⟨fun ⟨Q, hQ, hQP⟩ ↦ translation_injective W hQP ▸ hQ, fun hP ↦ ⟨P, hP, rfl⟩⟩

/-- Translation, as a map from the points fixing an intermediate field to its fixing subgroup. -/
private noncomputable def toFixingSubgroup (L : IntermediateField F W.FunctionField)
    (P : translationFixingSubgroup W L) : L.fixingSubgroup :=
  ⟨translation W (P : (W⁄F).toAffine.Point), (IntermediateField.mem_fixingSubgroup_iff L _).mpr
    ((mem_translationFixingSubgroup_iff W).mp P.2)⟩

private theorem toFixingSubgroup_injective (L : IntermediateField F W.FunctionField) :
    Function.Injective (toFixingSubgroup W L) := fun _ _ h ↦
  Subtype.ext (translation_injective W (by simpa only [toFixingSubgroup, Subtype.mk.injEq] using h))

instance finite_translationFixingSubgroup (L : IntermediateField F W.FunctionField)
    [FiniteDimensional L W.FunctionField] : Finite (translationFixingSubgroup W L) :=
  .of_injective _ (toFixingSubgroup_injective W L)

/-- **An intermediate field of finite degree is fixed by at most that many translations.** For the
fixed field of a finite subgroup of points the bound is attained, by
`WeierstrassCurve.Affine.finrank_translationFixedField`. -/
theorem card_translationFixingSubgroup_le (L : IntermediateField F W.FunctionField)
    [FiniteDimensional L W.FunctionField] :
    Nat.card (translationFixingSubgroup W L) ≤ Module.finrank L W.FunctionField :=
  (Nat.card_le_card_of_injective _ (toFixingSubgroup_injective W L)).trans
    (IntermediateField.card_fixingSubgroup_le L)

/-- **A subgroup of points whose fixed field has finite degree is itself finite.** Its order is
then that degree, by `WeierstrassCurve.Affine.finrank_translationFixedField`: a subgroup of
translations is no larger than the extension it cuts out. -/
theorem finite_of_finiteDimensional_translationFixedField
    [FiniteDimensional (translationFixedField W Φ) W.FunctionField] : Finite Φ :=
  letI : FiniteDimensional (IntermediateField.fixedField (translationSubgroup W Φ))
      W.FunctionField := by
    rw [← translationFixedField]
    infer_instance
  have : Finite (translationSubgroup W Φ) :=
    IntermediateField.finite_of_finiteDimensional_fixedField (translationSubgroup W Φ)
  .of_equiv _ (translationMulEquiv W Φ).symm.toEquiv

/-- **Distinct finite subgroups of points have distinct fixed fields.** Only `Φ` need be assumed
finite: a subgroup with the same fixed field as a finite one is finite by
`WeierstrassCurve.Affine.finite_of_finiteDimensional_translationFixedField`. -/
theorem eq_of_translationFixedField_eq [Finite Φ]
    (h : translationFixedField W Φ = translationFixedField W Ψ) : Φ = Ψ := by
  have : FiniteDimensional (translationFixedField W Ψ) W.FunctionField := by
    rw [← h]; infer_instance
  have : Finite Ψ := finite_of_finiteDimensional_translationFixedField W Ψ
  rw [← translationFixingSubgroup_translationFixedField W Φ, h,
    translationFixingSubgroup_translationFixedField W Ψ]

end WeierstrassCurve.Affine
