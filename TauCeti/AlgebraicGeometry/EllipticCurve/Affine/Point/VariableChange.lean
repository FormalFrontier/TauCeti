/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange

/-!
# The isomorphism of point groups induced by a change of variables

Mathlib's affine `Point` API has `WeierstrassCurve.Affine.Point.map`, the group homomorphism
induced by a map of the base field for a *fixed* curve, but nothing for the isomorphism between
the point groups of two *different* curves related by an admissible change of variables. This file
supplies it: for `C : VariableChange F` over a field, `(x, y) ↦ (u²x + r, u³y + u²sx + t)` is a
group isomorphism `(C • W).Point ≃+ W.Point`.

## Main definitions

* `WeierstrassCurve.Affine.Point.equivVariableChange`: the group isomorphism
  `(C • W).Point ≃+ W.Point`, whose inverse is the map induced by `C⁻¹` rather than an inverse
  extracted from bijectivity. Everything here is computable given `[DecidableEq F]`.
* `WeierstrassCurve.Affine.Point.equivVariableChange_some`: what it does to a point given by
  coordinates, `@[simp]`. The underlying homomorphism is `(equivVariableChange W C).toAddMonoidHom`
  — there is no separate `→+` in the public interface, since it would be the same map.

Transport of the point group along an equality of curves — needed to use a `C • W = W'` fact on
points — is Mathlib's `AddEquiv.cast`, instantiated at `fun V ↦ V.toAffine.Point`; this file adds
no wrapper for it.

## Implementation notes

The route is the group-law formulae, and those are a separate topic: what the change of variables
does to `negY`, `addX`, `negAddY`, `addY`, `slope`, `Equation` and `Nonsingular` is
`Affine/Formula/VariableChange.lean`, imported here. Nothing in that file mentions `Point`, and
nothing here restates it — the split follows Mathlib's own, which puts the formulae in
`Affine/Formula.lean` and the point type in `Affine/Point.lean`. In particular
`variableChange_equation` and `variableChange_nonsingular` are what let the map carry points to
points, and `variableChange_slope`, `variableChange_addX` and `variableChange_addY` are what make
it additive.

`mapVariableChangeFun`, its equation lemmas and injectivity, `variableChange_negY_ne` and
`mapVariableChange` are all `private`: they are how the
isomorphism is built, not part of what it offers. The public surface is `equivVariableChange` with
its two coordinate lemmas `equivVariableChange_some` and `equivVariableChange_symm_some`, both
`@[simp]`, so a consumer never needs to unfold anything. Anyone wanting the bare homomorphism
takes `(equivVariableChange W C).toAddMonoidHom`.

That is also why the section is a plain `public section` rather than `@[expose]`. Exposing the
whole file would publish every proof body to make three `rfl`s go through, and it is incompatible
with the helpers being private — a public declaration may not refer to a private one, so the
exposed body of `mapVariableChange` would fail to elaborate with
`Unknown identifier 'mapVariableChangeFun'`. Routing the two public coordinate lemmas through the
private equation lemma removes the need for exposure entirely.

This is a prerequisite for `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5's point isomorphism
for the quadratic twist: that statement is about the point groups of `E` and its twist, which
become isomorphic over `L` by a change of variables, and it cannot even be stated without the
isomorphism defined here.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Michael Stoll, Claude`. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. This is the case split of the
addition formula, transported; it is what lets `add_some` be applied on both sides at once. -/
private lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  rintro ⟨hX, hY⟩
  have hx : x₁ = x₂ := (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, (C.u.isUnit.pow 3).mul_left_cancel (by linear_combination hY)⟩

namespace Point

/-- The underlying map `(C • W).Point → W.Point` of the change of variables, sending `0` to `0` and
`(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
private def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] private lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

private lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

private lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    simp only [some.injEq]
    exact ⟨hx,
      mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx)⟩

variable [DecidableEq F] [W.IsElliptic]

/-! From here on `[W.IsElliptic]` is unavoidable: Mathlib puts the `AddCommGroup` structure on
`Point` under that hypothesis (`Affine/Point.lean`, the section opened by
`variable [Nontrivial R] [W'.IsElliptic]`), so without it `(C • W).Point` is not an additive group
and the statements below do not even typecheck. The underlying map and its injectivity hold for an
arbitrary Weierstrass curve over a field, and the transformation laws they rest on for an
arbitrary Weierstrass curve over a commutative ring. -/

/-- What Mathlib's `AddEquiv.cast` — transport of the point group along an equality of Weierstrass
curves — does to a point given by coordinates. The equiv itself is `AddEquiv.cast` and is not
restated here; only its value needs a name, since Mathlib states `cast` through `Equiv.cast` and
so gives no equation for it. Public because the quadratic-twist point isomorphism rewrites with
it as well; within this file it is used only by `equivVariableChange_symm_some`. -/
-- not `@[simp]`: Mathlib's `AddEquiv.cast_apply` is itself a simp lemma and rewrites this
-- left-hand side to the raw `cast` first, so `simpNF` reports the statement is not in
-- simp-normal form and the lemma could never fire. It is used by `rw`, which is syntactic.
lemma cast_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point) h (some x y hns)
      = some x y (h ▸ hns) := by
  subst h; rfl

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of
variables, as scaffolding: its `map_add'` is what `equivVariableChange` is built from. Private,
since `(equivVariableChange W C).toAddMonoidHom` is the same homomorphism and is the canonical
way to ask for it. -/
private def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, with inverse coming from `C⁻¹`. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹
        (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · have hz : (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm) 0 = 0 := _root_.map_zero _
      rw [← zero_def, hz, mapVariableChangeFun_zero, mapVariableChangeFun_zero]
    · rw [cast_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      simp only [some.injEq]
      refine ⟨?_, ?_⟩ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

/-- **What the isomorphism does to a point given by coordinates.** Its inverse is
`equivVariableChange_symm_some`. The coerced homomorphism `(equivVariableChange W C).toAddMonoidHom`
is characterised by this same equation. -/
@[simp] lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) :=
  mapVariableChangeFun_some W C h

/-- The inverse of `equivVariableChange` on the nose: it *is* the map induced by `C⁻¹`, transported
along `C⁻¹ • (C • W) = W`. Stated separately so the public coordinate lemma below is proved by
rewriting rather than by `change`: the equivalence's `invFun` is a structure field, and without
this step a proof of the coordinate law would silently depend on how that record is written. -/
private lemma equivVariableChange_symm_apply (P : W.toAffine.Point) :
    (equivVariableChange W C).symm P
      = mapVariableChangeFun (C • W) C⁻¹
          (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
            (inv_smul_smul C W).symm P) := rfl

/-- **What the inverse isomorphism does to a point given by coordinates.** It is the map induced by
`C⁻¹`, so the coordinates are those of `C⁻¹` — this is the sense in which the inverse "comes from
`C⁻¹`" rather than from bijectivity. -/
@[simp] lemma equivVariableChange_symm_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (equivVariableChange W C).symm (.some x y h)
      = .some (((C⁻¹).u : F) ^ 2 * x + (C⁻¹).r)
          (((C⁻¹).u : F) ^ 3 * y + ((C⁻¹).u : F) ^ 2 * (C⁻¹).s * x + (C⁻¹).t)
          ((variableChange_nonsingular (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  rw [equivVariableChange_symm_apply, cast_some, mapVariableChangeFun_some]

end Point

end WeierstrassCurve.Affine

end
