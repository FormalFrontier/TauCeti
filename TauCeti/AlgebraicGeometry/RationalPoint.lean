/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ResidueDegree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
# Rational points of a scheme over a base

A `k`-rational point of a scheme `X` over a field `k` is a morphism `Spec k ⟶ X` over `Spec k`,
that is, a *section* of the structure morphism `f : X ⟶ Spec k`. This file records what such a
section gives at the level of points, residue fields, and divisor degrees. Everything is stated
for a section `s` of an arbitrary morphism of schemes `f : X ⟶ S`, the hypothesis being
`s ≫ f = 𝟙 S`; the `k`-rational case is the special case `S = Spec k`.

## Main results

* `residueDegree_eq_one_of_section`: the residue degree of `f` at a point in the image of a
  section is `1`. Over `S = Spec k` this is the statement `[κ(x₀) : k] = 1` at a `k`-rational
  point `x₀`, and it is the reason a rational point is the right normalization datum.
* `residueFieldIsoOfSection`: consequently the residue field of `X` at such a point *is* the
  residue field of the base, `κ(y) ≅ κ(s y)`, with inverse the residue-field map of `s`.
* `residueDegree_comp_of_section`: residue degrees over a further base are computed on the base,
  `[κ(s y) : κ(g y)] = [κ(y) : κ(g y)]` for `g : S ⟶ Z`.
* `relativeDegree_ofPoint_of_section`: the prime divisor at a codimension-one rational point has
  relative degree `1`, and `relativeDegree_sub_zsmul_ofPoint_of_section`: consequently every
  divisor becomes degree zero after subtracting its own degree times that point.

The last item is the geometric source of the weight-one base point hypothesis that the Layer A
degree theory runs on. There the weight of a point of a curve over `k` is its residue degree
`[κ(x) : k]` (`SchemeWeilDivisor.relativeDegree`), and both the class-group splitting
`OrderSystem.classGroupAddEquivPicZeroProdInt` and the Abel-Jacobi class
`OrderSystem.weightedAbelJacobiClass` require a base point of weight one. So this file records
precisely why a `k`-rational point supplies that hypothesis, instead of it having to be assumed.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, "Standing hypotheses" ("A chosen
`k`-rational point `x₀`. ... the `k`-point *rigidifies/normalizes* the Picard functor and supplies
the Abel-Jacobi morphism") and Layer A ("Degree", `Σ_x [κ(x):k]·ord_x`). Base change of rational
points is left to a subsequent file, since it is a statement about pullbacks in an arbitrary
category rather than about schemes.

No external mathematics is vendored; the proofs reuse Mathlib's `Scheme.Hom.residueFieldMap`,
`Scheme.residueFieldCongr` and `Scheme.Hom.residueDegree` API together with Tau Ceti's
`residueDegree_comp`, `residueDegree_eq_one_iff` and `SchemeWeilDivisor.relativeDegree`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-! ### Points in the image of a section -/

/-- On underlying points, a section of `f` is a right inverse of `f`. -/
lemma leftInverse_of_section (hs : s ≫ f = 𝟙 S) : Function.LeftInverse f s := fun y ↦ by
  have h : (s ≫ f).base y = (𝟙 S : S ⟶ S).base y := by rw [hs]
  simpa using h

/-- A section of `f` is a one-sided inverse of `f` at every point of the base. -/
lemma apply_section (hs : s ≫ f = 𝟙 S) (y : S) : f (s y) = y :=
  leftInverse_of_section hs y

/-- Distinct points of the base have distinct images under a section. -/
lemma injective_of_section (hs : s ≫ f = 𝟙 S) : Function.Injective s :=
  (leftInverse_of_section hs).injective

/-- A morphism admitting a section is surjective on points. -/
lemma surjective_of_section (hs : s ≫ f = 𝟙 S) : Function.Surjective f :=
  (leftInverse_of_section hs).surjective

/-- Sections compose along a tower: if `s` is a section of `f : X ⟶ S` and `t` is a section of
`g : S ⟶ Z`, then `t ≫ s` is a section of `f ≫ g`. Over fields this says that a `k`-rational
point of `X` and an `L`-rational point of `Spec k` compose to an `L`-rational point of `X`. -/
lemma comp_eq_id_of_section_of_section {g : S ⟶ Z} {t : Z ⟶ S} (hs : s ≫ f = 𝟙 S)
    (ht : t ≫ g = 𝟙 Z) :
    (t ≫ s) ≫ f ≫ g = 𝟙 Z := by
  rw [Category.assoc, ← Category.assoc s f g, hs, Category.id_comp, ht]

/-! ### Residue degrees at a section -/

/-- The two residue degrees attached to a section multiply to one: the residue-field extensions
`κ(y) → κ(s y) → κ(y)` compose to the identity of `κ(y)`. -/
private lemma residueDegree_mul_residueDegree_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) * s.residueDegree y = 1 := by
  rw [← residueDegree_comp s f y, hs, Scheme.Hom.residueDegree_id]

/-- The residue degree of `f` at a point in the image of a section is one.

For `S = Spec k` this says that a `k`-rational point `x₀` of `X` has residue field `κ(x₀)` of
degree one over `k`. -/
theorem residueDegree_eq_one_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) = 1 :=
  Nat.dvd_one.mp ⟨_, (residueDegree_mul_residueDegree_of_section hs y).symm⟩

/-- A section has residue degree one at every point of the base. -/
theorem residueDegree_section_eq_one (hs : s ≫ f = 𝟙 S) (y : S) :
    s.residueDegree y = 1 := by
  have h := residueDegree_mul_residueDegree_of_section hs y
  rwa [residueDegree_eq_one_of_section hs y, Nat.one_mul] at h

/-- Residue degrees over a further base are computed on the base: at a point in the image of a
section of `f : X ⟶ S`, the residue degree of `f ≫ g` agrees with that of `g : S ⟶ Z`. -/
theorem residueDegree_comp_of_section (hs : s ≫ f = 𝟙 S) (g : S ⟶ Z) (y : S) :
    (f ≫ g).residueDegree (s y) = g.residueDegree y := by
  rw [residueDegree_comp, residueDegree_eq_one_of_section hs, Nat.mul_one, apply_section hs]

/-! ### Residue fields at a section -/

/-- The residue-field map of `f` at a point in the image of a section is bijective. -/
theorem bijective_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (f.residueFieldMap (s y)) :=
  (residueDegree_eq_one_iff f (s y)).mp (residueDegree_eq_one_of_section hs y)

/-- The residue-field map of a section is bijective at every point of the base. -/
theorem bijective_residueFieldMap_section (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (s.residueFieldMap y) :=
  (residueDegree_eq_one_iff s y).mp (residueDegree_section_eq_one hs y)

/-- The residue-field map of `f` at a point in the image of a section is an isomorphism. -/
lemma isIso_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (f.residueFieldMap (s y)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_residueFieldMap_of_section hs y)

/-- The residue-field map of a section is an isomorphism at every point of the base. -/
lemma isIso_residueFieldMap_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (s.residueFieldMap y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_residueFieldMap_section hs y)

/-- The residue-field map of `f` at a point in the image of a section, followed by the
residue-field map of the section, is the identity of `κ(y)`. -/
lemma residueFieldMap_comp_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    (S.residueFieldCongr (apply_section hs y).symm).hom ≫
        f.residueFieldMap (s y) ≫ s.residueFieldMap y = 𝟙 (S.residueField y) := by
  rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hs y]
  simp [Scheme.residueFieldCongr]

/-- The residue field of `X` at a point in the image of a section is the residue field of the
base at the corresponding point of the base. The inverse is the residue-field map of the
section. -/
@[expose, simps]
noncomputable def residueFieldIsoOfSection (hs : s ≫ f = 𝟙 S) (y : S) :
    S.residueField y ≅ X.residueField (s y) where
  hom := (S.residueFieldCongr (apply_section hs y).symm).hom ≫ f.residueFieldMap (s y)
  inv := s.residueFieldMap y
  hom_inv_id := by
    rw [Category.assoc, residueFieldMap_comp_residueFieldMap_of_section hs y]
  inv_hom_id := by
    haveI := isIso_residueFieldMap_section hs y
    rw [← cancel_mono (s.residueFieldMap y)]
    simp only [Category.assoc, Category.id_comp]
    rw [residueFieldMap_comp_residueFieldMap_of_section hs y, Category.comp_id]

/-! ### Prime divisors at a rational point -/

/-- A prime divisor whose generic point is a rational point has relative degree one.

This is the geometric origin of the weight-one base point hypothesis of the Layer A degree
theory: the weight of a codimension-one point `x` of a curve over `k` is its residue degree
`[κ(x) : k]`, and at a `k`-rational point that weight is one. -/
theorem relativeDegree_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) :
    SchemeWeilDivisor.relativeDegree f (WeilDivisor.ofPoint x₀) = 1 := by
  rw [SchemeWeilDivisor.relativeDegree_ofPoint, hx₀, residueDegree_eq_one_of_section hs,
    Nat.cast_one]

/-- A multiple of the prime divisor at a rational point has that multiple as relative degree:
`deg (d · x₀) = d`. -/
theorem relativeDegree_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (d : ℤ) :
    SchemeWeilDivisor.relativeDegree f (d • WeilDivisor.ofPoint x₀) = d := by
  rw [map_zsmul, relativeDegree_ofPoint_of_section hs hx₀, smul_eq_mul, mul_one]

/-- Correcting a divisor by a multiple of a rational point kills its relative degree:
`deg (D - (deg D) · x₀) = 0`.

This is the normalization `D ↦ D - d·x₀` of the Abel map: over a base point of relative degree
one every divisor becomes degree zero after subtracting its own degree times that point, which is
what makes the degree-zero part of the divisor class group accessible from arbitrary divisors. -/
theorem relativeDegree_sub_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (D : SchemeWeilDivisor X) :
    SchemeWeilDivisor.relativeDegree f
        (D - SchemeWeilDivisor.relativeDegree f D • WeilDivisor.ofPoint x₀) = 0 := by
  rw [map_sub, relativeDegree_zsmul_ofPoint_of_section hs hx₀, sub_self]

end AlgebraicGeometry

end TauCeti
