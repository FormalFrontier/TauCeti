/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint

/-!
# The translation action of the point group on the function field

For a point `P` of an elliptic curve `W` over a field `F`, the translation `τ_P : Q ↦ Q + P` is an
automorphism of the curve — of the curve, not of the elliptic curve: it does not fix the point at
infinity unless `P = O`, so it is not an isogeny. What it does induce is an `F`-algebra
automorphism `τ_P^*` of the function field `F(W)`, and `P ↦ τ_P^*` is a faithful action of the
point group on `F(W)`. This file constructs that action.

The construction runs through the generic point `g` of
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/GenericPoint.lean`. Translating a
function by `P` is evaluating it at `g + P`, so the pullback of `τ_P` on the affine coordinate ring
is `CoordinateRing.evalAlgHom` at the coordinates of the translate `g + P_{F(W)}`, and the
composition law is the associativity of the point group: applying `τ_Q^*` to a coordinate of
`g + P` moves the generic point to `g + Q`, hence the pair to `g + P + Q`.

Two facts make the construction go through, and both come down to the transcendence of the
coordinate function `x`. First, `g + P` is never the point at infinity, since otherwise `g` would
be a constant point. Second, its `x`-coordinate is again transcendental: were it algebraic, the
Weierstrass equation — monic of degree `2` in `y` — would make its `y`-coordinate algebraic too, so
`g + P` would be a point over the relative algebraic closure of `F` in `F(W)`, and subtracting the
constant point `P` would put `g` there as well. Transcendence is what makes the evaluation map
injective (`CoordinateRing.algHom_injective`) and so extendable to the fraction field.

## Main definitions

* `WeierstrassCurve.Affine.translatedGenericPoint`: the translate `g + P` of the generic point.
* `WeierstrassCurve.Affine.translation`: the automorphism `τ_P^*` of the function field.
* `WeierstrassCurve.Affine.translationHom`: the action, as a monoid homomorphism out of
  `Multiplicative (W⁄F).Point`.

## Main results

* `WeierstrassCurve.Affine.translation_zero` and
  `WeierstrassCurve.Affine.translation_add`: the action laws, `τ_O^* = 1` and
  `τ_{P + Q}^* = τ_P^* ≫ τ_Q^*`.
* `WeierstrassCurve.Affine.translation_eq_one_iff` and
  `WeierstrassCurve.Affine.translation_injective` and
  `WeierstrassCurve.Affine.translationHom_injective`: the action is faithful.
* `WeierstrassCurve.Affine.translation_apply_genericX_some` and
  `WeierstrassCurve.Affine.translation_apply_genericY_some`: for an affine `P` the two
  coordinate functions are moved by the Weierstrass addition formulas, which is what identifies
  this automorphism with the pullback of `τ_P`.

`[DecidableEq F]` is Mathlib's hypothesis for the group law on `Affine.Point`, and it is inherited
here; the function field gets its own instance from it, so the points of `W⁄F(W)` are available
with no further assumption.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5**, third milestone: "function-field
pullbacks of the translations `τ_P`, with the action and composition laws". Layer 1's dual-isogeny
milestone consumes them — "`Kˢᵉᵖ(W₁)/φ^*Kˢᵉᵖ(W₂)` **is** Galois with group `ker φ(Kˢᵉᵖ)` acting by
translations" — and so does the place-free fibre count of Layer 1, where "translation moves the
kernel fibre onto one".

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.

## Provenance

Not a port: none of the pinned sources builds the translation action. The pullback is manufactured
from Mathlib's `Affine.Point` group law rather than from the addition formulas directly, so the
composition law is the associativity Mathlib already proved.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : _root_.WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- The translate of the generic point of `W` by a point `P`. -/
noncomputable def translatedGenericPoint (P : (W⁄F).toAffine.Point) :
    (W⁄W.FunctionField).toAffine.Point :=
  genericPoint W + Point.baseChange (W' := W) F W.FunctionField P

/-- The translated generic point is the generic point plus the base change of `P`. -/
theorem translatedGenericPoint_def (P : (W⁄F).toAffine.Point) :
    translatedGenericPoint W P =
      genericPoint W + Point.baseChange (W' := W) F W.FunctionField P := (rfl)

@[simp]
theorem translatedGenericPoint_zero : translatedGenericPoint W 0 = genericPoint W := by
  rw [translatedGenericPoint_def, map_zero, add_zero]

/-- **A translate of the generic point is never the point at infinity**: the coordinate `x` is
transcendental, so the generic point is not the negative of a constant point. -/
theorem translatedGenericPoint_ne_zero (P : (W⁄F).toAffine.Point) :
    translatedGenericPoint W P ≠ 0 := by
  intro h
  have hneg : genericPoint W = -Point.baseChange (W' := W) F W.FunctionField P := by
    rw [eq_neg_iff_add_eq_zero]
    exact h
  have hx : genericX W = algebraMap F W.FunctionField (Point.xCoord P) := by
    rw [← xCoord_genericPoint, hneg, Point.xCoord_neg, Point.xCoord_map, Algebra.ofId_apply]
  exact transcendental_genericX W (hx ▸ isAlgebraic_algebraMap _)

/-- **The `x`-coordinate of a translate of the generic point is transcendental.** Were it
algebraic, so would be the `y`-coordinate — the Weierstrass equation is monic of degree `2` in
`y` — so the translate would come from the relative algebraic closure of `F` in the function
field; subtracting the constant point `P` would put the generic point there too, making the
coordinate function `x` algebraic. -/
private theorem transcendental_xCoord_translatedGenericPoint (P : (W⁄F).toAffine.Point) :
    Transcendental F (Point.xCoord (translatedGenericPoint W P)) := by
  set 𝔽 := algebraicClosure F W.FunctionField
  intro halg
  set Q := translatedGenericPoint W P with hQdef
  have hQ : Q ≠ 0 := translatedGenericPoint_ne_zero W P
  set u := Point.xCoord Q
  set v := Point.yCoord Q
  have hns : (W⁄W.FunctionField).toAffine.Nonsingular u v := Point.nonsingular_coords hQ
  have hu : u ∈ 𝔽 := halg.isIntegral
  have hv : v ∈ 𝔽 :=
    TauCeti.WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x W hns.left hu
  -- the point therefore descends to the algebraic closure, and so does the generic point
  have hnsE : (W⁄𝔽).toAffine.Nonsingular (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ :=
    (_root_.WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
      (f := 𝔽.val) 𝔽.val.injective _ _).1 hns
  have hQmap : Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE) = Q := by
    rw [Point.map_some]
    exact Point.some_coords hQ
  have hgeneric : genericPoint W =
      Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE -
        Point.baseChange (W' := W) F 𝔽 P) := by
    have hbc : Point.map 𝔽.val (Point.baseChange (W' := W) F 𝔽 P) =
        Point.baseChange (W' := W) F W.FunctionField P :=
      Point.map_baseChange (W' := W) 𝔽.val P
    rw [map_sub, hQmap, hbc, hQdef, translatedGenericPoint_def]
    exact (add_sub_cancel_right _ _).symm
  have : IsIntegral F (genericX W) := by
    rw [← xCoord_genericPoint, hgeneric, Point.xCoord_map]
    exact (Algebra.IsIntegral.isIntegral (R := F) _).map 𝔽.val
  exact transcendental_genericX W this.isAlgebraic

/-- The pullback of the translation by `P` on the affine coordinate ring: evaluation at the
translate of the generic point. -/
private noncomputable def translationAlgHom (P : (W⁄F).toAffine.Point) :
    W.CoordinateRing →ₐ[F] W.FunctionField :=
  CoordinateRing.evalAlgHom (Point.nonsingular_coords (translatedGenericPoint_ne_zero W P)).left

private theorem translationAlgHom_mk_C_X (P : (W⁄F).toAffine.Point) :
    translationAlgHom W P (CoordinateRing.mk W (C X)) =
      Point.xCoord (translatedGenericPoint W P) :=
  CoordinateRing.evalAlgHom_of_X _

private theorem translationAlgHom_mk_Y (P : (W⁄F).toAffine.Point) :
    translationAlgHom W P (CoordinateRing.mk W Y) =
      Point.yCoord (translatedGenericPoint W P) :=
  CoordinateRing.evalAlgHom_root _

private theorem translationAlgHom_injective (P : (W⁄F).toAffine.Point) :
    Function.Injective (translationAlgHom W P) :=
  CoordinateRing.algHom_injective _ <| by
    rw [translationAlgHom_mk_C_X]
    exact transcendental_xCoord_translatedGenericPoint W P

/-- The pullback of the translation by `P` on the function field. -/
private noncomputable def translationAux (P : (W⁄F).toAffine.Point) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationAlgHom_injective W P)

private theorem translationAux_algebraMap (P : (W⁄F).toAffine.Point) (z : W.CoordinateRing) :
    translationAux W P (algebraMap W.CoordinateRing W.FunctionField z) =
      translationAlgHom W P z := by
  simp [translationAux, IsFractionRing.liftAlgHom_apply]

private theorem translationAux_genericX (P : (W⁄F).toAffine.Point) :
    translationAux W P (genericX W) = Point.xCoord (translatedGenericPoint W P) := by
  rw [genericX_def, translationAux_algebraMap, translationAlgHom_mk_C_X]

private theorem translationAux_genericY (P : (W⁄F).toAffine.Point) :
    translationAux W P (genericY W) = Point.yCoord (translatedGenericPoint W P) := by
  rw [genericY_def, translationAux_algebraMap, translationAlgHom_mk_Y]

/-- **The translation pullback moves the generic point to its translate.** -/
private theorem map_genericPoint (P : (W⁄F).toAffine.Point) :
    Point.map (translationAux W P) (genericPoint W) = translatedGenericPoint W P := by
  apply Point.eq_of_coords
  · rw [genericPoint_eq_some, Point.map_some]
    exact Point.some_ne_zero _
  · exact translatedGenericPoint_ne_zero W P
  · rw [Point.xCoord_map, xCoord_genericPoint]
    exact translationAux_genericX W P
  · rw [Point.yCoord_map, yCoord_genericPoint]
    exact translationAux_genericY W P

/-- **The translation pullback by `Q` carries the translate by `P` to the translate by `P + Q`.**
This is the group law of the points, transported to the function field. -/
private theorem map_translatedGenericPointAux (P Q : (W⁄F).toAffine.Point) :
    Point.map (translationAux W Q) (translatedGenericPoint W P) =
      translatedGenericPoint W (P + Q) := by
  have hbase : Point.map (translationAux W Q)
      (Point.baseChange (W' := W) F W.FunctionField P) =
        Point.baseChange (W' := W) F W.FunctionField P :=
    Point.map_baseChange (W' := W) (translationAux W Q) P
  rw [translatedGenericPoint_def, map_add, hbase, map_genericPoint,
    translatedGenericPoint_def, translatedGenericPoint_def, map_add, add_right_comm]
  exact add_assoc _ _ _

/-- **Composition of translation pullbacks**, on the coordinate ring. -/
private theorem comp_translationAlgHom (P Q : (W⁄F).toAffine.Point) :
    (translationAux W Q).comp (translationAlgHom W P) = translationAlgHom W (P + Q) := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [← AdjoinRoot.mk_C, AlgHom.comp_apply, translationAlgHom_mk_C_X,
      translationAlgHom_mk_C_X,
      ← Point.xCoord_map (W := W) (translationAux W Q), map_translatedGenericPointAux]
  · rw [← AdjoinRoot.mk_X, AlgHom.comp_apply, translationAlgHom_mk_Y,
      translationAlgHom_mk_Y,
      ← Point.yCoord_map (W := W) (translationAux W Q), map_translatedGenericPointAux]

/-- **Composition of translation pullbacks**, on the function field. -/
private theorem comp_translationAux (P Q : (W⁄F).toAffine.Point) :
    (translationAux W Q).comp (translationAux W P) = translationAux W (P + Q) := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.CoordinateRing)
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply]
  -- `IsLocalization.algHom_ext` restricts along `Algebra.algHom F W.CoordinateRing
  -- W.FunctionField`; its application to `z` is definitionally the displayed `algebraMap`.
  change translationAux W Q
      (translationAux W P (algebraMap W.CoordinateRing W.FunctionField z)) =
    translationAux W (P + Q) (algebraMap W.CoordinateRing W.FunctionField z)
  have h : translationAux W Q
      (translationAux W P (algebraMap W.CoordinateRing W.FunctionField z)) =
      translationAlgHom W (P + Q) z := by
    rw [translationAux_algebraMap, ← AlgHom.comp_apply, comp_translationAlgHom]
  simpa [translationAux_algebraMap] using h

/-- The translation by the point at infinity is the identity, on the coordinate ring. -/
private theorem translationAlgHom_zero :
    translationAlgHom W 0 = IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [← AdjoinRoot.mk_C, translationAlgHom_mk_C_X, translatedGenericPoint_zero,
      xCoord_genericPoint, IsScalarTower.toAlgHom_apply, genericX_def]
  · rw [← AdjoinRoot.mk_X, translationAlgHom_mk_Y, translatedGenericPoint_zero,
      yCoord_genericPoint, IsScalarTower.toAlgHom_apply, genericY_def]

private theorem translationAux_zero : translationAux W 0 = AlgHom.id F W.FunctionField := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.CoordinateRing)
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply]
  -- As above, unfold the canonical restriction from `IsLocalization.algHom_ext`; this also
  -- unfolds the application of `AlgHom.id` on the right to the underlying element.
  change translationAux W 0 (algebraMap W.CoordinateRing W.FunctionField z) =
    algebraMap W.CoordinateRing W.FunctionField z
  have h : translationAux W 0 (algebraMap W.CoordinateRing W.FunctionField z) =
      algebraMap W.CoordinateRing W.FunctionField z := by
    rw [translationAux_algebraMap, translationAlgHom_zero, IsScalarTower.toAlgHom_apply]
  simpa using h

/-- **The translation of the function field by a point `P`.** It is the pullback of the
translation `τ_P : Q ↦ Q + P` of the curve: on the affine coordinate ring it is evaluation at the
translate of the generic point by `P`, and its inverse is the translation by `-P`. -/
noncomputable def translation (P : (W⁄F).toAffine.Point) :
    W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (translationAux W P) (translationAux W (-P))
    (by rw [comp_translationAux, neg_add_cancel, translationAux_zero])
    (by rw [comp_translationAux, add_neg_cancel, translationAux_zero])

/-- **Translation of a regular function is evaluation at the translated generic point.** -/
@[simp]
theorem translation_apply_mk (P : (W⁄F).toAffine.Point) (p : F[X][Y]) :
    translation W P
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)) =
      (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (Point.xCoord (translatedGenericPoint W P))
        (Point.yCoord (translatedGenericPoint W P)) :=
  (translationAux_algebraMap W P _).trans (CoordinateRing.evalAlgHom_mk _ p)

/-- **Translation carries the generic point to the translated generic point.** -/
theorem map_translation_genericPoint (P : (W⁄F).toAffine.Point) :
    Point.map (translation W P).toAlgHom (genericPoint W) = translatedGenericPoint W P :=
  map_genericPoint W P

/-- **Translation by `Q` carries the translate by `P` to the translate by `P + Q`.** -/
theorem map_translation_translatedGenericPoint (P Q : (W⁄F).toAffine.Point) :
    Point.map (translation W Q).toAlgHom (translatedGenericPoint W P) =
      translatedGenericPoint W (P + Q) :=
  map_translatedGenericPointAux W P Q

/-- **The translation by the point at infinity is the identity.** -/
@[simp]
theorem translation_zero : translation W 0 = 1 :=
  AlgEquiv.ext fun z ↦ AlgHom.congr_fun (translationAux_zero W) z

/-- **The composition law of the translations.** Translating by `P` and then by `Q` is
translating by `P + Q`; on function fields the pullbacks compose in that same order, the point
group being commutative. -/
theorem translation_add (P Q : (W⁄F).toAffine.Point) :
    translation W (P + Q) = (translation W P).trans (translation W Q) :=
  AlgEquiv.ext fun z ↦ (AlgHom.congr_fun (comp_translationAux W P Q) z).symm

/-- **The translation action of the point group on the function field.** -/
noncomputable def translationHom :
    Multiplicative (W⁄F).toAffine.Point →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun P := translation W (Multiplicative.toAdd P)
  map_one' := translation_zero W
  map_mul' P Q := by
    exact (congrArg (translation W)
      (add_comm (Multiplicative.toAdd P) (Multiplicative.toAdd Q))).trans
      (translation_add W (Multiplicative.toAdd Q) (Multiplicative.toAdd P))

@[simp]
theorem translationHom_apply (P : Multiplicative (W⁄F).toAffine.Point) :
    translationHom W P = translation W (Multiplicative.toAdd P) := (rfl)

/-- **The translation moves the coordinate `x` to the `x`-coordinate of the translate of the
generic point**: this is what makes `translation` the pullback of `τ_P`. -/
@[simp]
theorem translation_apply_genericX (P : (W⁄F).toAffine.Point) :
    translation W P (genericX W) = Point.xCoord (translatedGenericPoint W P) :=
  translationAux_genericX W P

/-- **The translation moves the coordinate `y` to the `y`-coordinate of the translate of the
generic point.** -/
@[simp]
theorem translation_apply_genericY (P : (W⁄F).toAffine.Point) :
    translation W P (genericY W) = Point.yCoord (translatedGenericPoint W P) :=
  translationAux_genericY W P

/-- **The translation action is faithful**: only the point at infinity acts trivially. Both
coordinates of the translate of the generic point being unmoved makes the translate the generic
point itself. -/
@[simp]
theorem translation_eq_one_iff {P : (W⁄F).toAffine.Point} : translation W P = 1 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ translation_zero W⟩
  have hx : Point.xCoord (translatedGenericPoint W P) = Point.xCoord (genericPoint W) := by
    rw [← translation_apply_genericX, h, AlgEquiv.one_apply, xCoord_genericPoint]
  have hy : Point.yCoord (translatedGenericPoint W P) = Point.yCoord (genericPoint W) := by
    rw [← translation_apply_genericY, h, AlgEquiv.one_apply, yCoord_genericPoint]
  have hpt : translatedGenericPoint W P = genericPoint W :=
    Point.eq_of_coords (translatedGenericPoint_ne_zero W P)
      (by rw [genericPoint_eq_some]; exact Point.some_ne_zero _) hx hy
  rw [translatedGenericPoint_def, add_eq_left] at hpt
  exact Point.map_injective (W' := W) _
    (hpt.trans (map_zero (Point.baseChange (W' := W) F W.FunctionField)).symm)

/-- **Distinct points induce distinct translations of the function field**: the action of the
point group is faithful, `translation W P = translation W Q` forcing `P = Q`. -/
theorem translation_injective : Function.Injective (translation W) := fun P Q h ↦ by
  have hPQ : translation W (P - Q) = 1 := by
    rw [sub_eq_add_neg, translation_add, h, ← translation_add, add_neg_cancel, translation_zero]
  rwa [translation_eq_one_iff, sub_eq_zero] at hPQ

/-- **The translation action homomorphism is injective**: the packaged action is faithful. -/
theorem translationHom_injective : Function.Injective (translationHom W) := fun P Q h ↦ by
  apply Multiplicative.toAdd.injective
  apply translation_injective W
  simpa only [translationHom_apply] using h

omit [DecidableEq F] [W.IsElliptic] in
/-- The generic point and a base-changed affine point are never in the degenerate case of the
addition formulas: their `x`-coordinates already differ. -/
private theorem not_genericX_eq_and_genericY_eq_negY (x₁ y₁ : F) :
    ¬(genericX W = algebraMap F W.FunctionField x₁ ∧
      genericY W = (W⁄W.FunctionField).toAffine.negY (algebraMap F W.FunctionField x₁)
        (algebraMap F W.FunctionField y₁)) := fun hc ↦ genericX_ne_algebraMap W x₁ hc.1

/-- **The translation of the coordinate `x` by an affine point**, read off the addition
formulas: the generic point and a constant point are never in the degenerate case, the coordinate
`x` taking no constant value. -/
theorem translation_apply_genericX_some {x₁ y₁ : F}
    (h : (W⁄F).toAffine.Nonsingular x₁ y₁) :
    translation W (.some x₁ y₁ h) (genericX W) =
      (W⁄W.FunctionField).toAffine.addX (genericX W) (algebraMap F W.FunctionField x₁)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x₁)
          (genericY W) (algebraMap F W.FunctionField y₁)) := by
  rw [translation_apply_genericX, translatedGenericPoint_def, Point.map_some, genericPoint_eq_some]
  simp only [Algebra.ofId_apply]
  rw [_root_.WeierstrassCurve.Affine.Point.add_some
    (not_genericX_eq_and_genericY_eq_negY W x₁ y₁), Point.xCoord_some]

/-- **The translation of the coordinate `y` by an affine point**, read off the addition
formulas. -/
theorem translation_apply_genericY_some {x₁ y₁ : F}
    (h : (W⁄F).toAffine.Nonsingular x₁ y₁) :
    translation W (.some x₁ y₁ h) (genericY W) =
      (W⁄W.FunctionField).toAffine.addY (genericX W) (algebraMap F W.FunctionField x₁)
        (genericY W)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x₁)
          (genericY W) (algebraMap F W.FunctionField y₁)) := by
  rw [translation_apply_genericY, translatedGenericPoint_def, Point.map_some, genericPoint_eq_some]
  simp only [Algebra.ofId_apply]
  rw [_root_.WeierstrassCurve.Affine.Point.add_some
    (not_genericX_eq_and_genericY_eq_negY W x₁ y₁), Point.yCoord_some]

end WeierstrassCurve.Affine

end
