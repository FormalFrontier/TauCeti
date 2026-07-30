/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Rational points of a scheme over a base

A `k`-rational point of a scheme `X` over a field `k` is a morphism `Spec k ⟶ X` over `Spec k`,
that is, a *section* of the structure morphism `f : X ⟶ Spec k`. This file records what such a
section gives at the level of points and residue fields. Everything is stated for a section `s`
of an arbitrary morphism of schemes `f : X ⟶ S`, the hypothesis being `s ≫ f = 𝟙 S`; the
`k`-rational case is the special case `S = Spec k`.

## Main results

* `residueDegree_eq_one_of_section`: the residue degree of `f` at a point in the image of a
  section is `1`. Over `S = Spec k` this is the statement `[κ(x₀) : k] = 1` at a `k`-rational
  point `x₀`, and it is the reason a rational point is the right normalization datum.
* `residueFieldIsoOfSection`: consequently the residue field of `X` at such a point *is* the
  residue field of the base, `κ(y) ≅ κ(s y)`, with inverse the residue-field map of `s`.
* `residueDegree_comp_of_section`: residue degrees over a further base are computed on the base,
  `[κ(s y) : κ(g y)] = [κ(y) : κ(g y)]` for `g : S ⟶ Z`.

The divisor-level consequences live in `TauCeti.AlgebraicGeometry.RationalPoint.Degree`, which
keeps the results here independent of Weil divisor theory. They are the geometric source of the
weight-one base point hypothesis that the Layer A degree theory runs on: the weight of a point of
a curve over `k` there is its residue degree `[κ(x) : k]`, and both the class-group splitting
`OrderSystem.classGroupAddEquivPicZeroProdInt` and the Abel-Jacobi class
`OrderSystem.weightedAbelJacobiClass` require a base point of weight one.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, "Standing hypotheses" ("A chosen
`k`-rational point `x₀`. ... the `k`-point *rigidifies/normalizes* the Picard functor and supplies
the Abel-Jacobi morphism"). Base change of rational points is left to a subsequent file, since it
is a statement about pullbacks in an arbitrary category rather than about schemes.

No external mathematics is vendored; the proofs reuse Mathlib's `Scheme.Hom.residueFieldMap`,
`Scheme.residueFieldCongr` and `Scheme.Hom.residueDegree` API together with Tau Ceti's
`residueDegree_comp` and `residueDegree_eq_one_iff`.
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
@[simp]
lemma apply_section (hs : s ≫ f = 𝟙 S) (y : S) : f (s y) = y :=
  leftInverse_of_section hs y

/-- Distinct points of the base have distinct images under a section. -/
lemma section_injective (hs : s ≫ f = 𝟙 S) : Function.Injective s :=
  (leftInverse_of_section hs).injective

/-- A morphism admitting a section is surjective on points. -/
lemma base_surjective_of_section (hs : s ≫ f = 𝟙 S) : Function.Surjective f :=
  (leftInverse_of_section hs).surjective

/-! ### Residue degrees at a section -/

/-- The two residue degrees attached to a section multiply to one: the residue-field extensions
`κ(y) → κ(s y) → κ(y)` compose to the identity of `κ(y)`. -/
private lemma residueDegree_mul_residueDegree_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) * s.residueDegree y = 1 := by
  rw [← residueDegree_comp s f y, hs, Scheme.Hom.residueDegree_id]

/-- The residue degree of `f` at a point in the image of a section is one.

For `S = Spec k` this says that a `k`-rational point `x₀` of `X` has residue field `κ(x₀)` of
degree one over `k`. -/
@[simp]
theorem residueDegree_eq_one_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    f.residueDegree (s y) = 1 :=
  Nat.dvd_one.mp ⟨_, (residueDegree_mul_residueDegree_of_section hs y).symm⟩

-- `apply_section` and `residueDegree_eq_one_of_section` above are the normal-form lemmas of this
-- file and carry `@[simp]`; their consequences are deliberately *not* annotated. `simpNF` rejects
-- `@[simp]` on `residueDegree_section_eq_one` outright, since its `f` cannot be inferred from the
-- left-hand side so the lemma would never apply, and reports the other consequences as already
-- provable by `simp` from the two lemmas above — `simp [hs]` reaches them with no annotation.

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
theorem residueFieldMap_bijective_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (f.residueFieldMap (s y)) :=
  (residueDegree_eq_one_iff f (s y)).mp (residueDegree_eq_one_of_section hs y)

/-- The residue-field map of a section is bijective at every point of the base. -/
theorem residueFieldMap_section_bijective (hs : s ≫ f = 𝟙 S) (y : S) :
    Function.Bijective (s.residueFieldMap y) :=
  (residueDegree_eq_one_iff s y).mp (residueDegree_section_eq_one hs y)

/-- The residue-field map of `f` at a point in the image of a section is an isomorphism. -/
lemma isIso_residueFieldMap_of_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (f.residueFieldMap (s y)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (residueFieldMap_bijective_of_section hs y)

/-- The residue-field map of a section is an isomorphism at every point of the base. -/
lemma isIso_residueFieldMap_section (hs : s ≫ f = 𝟙 S) (y : S) :
    IsIso (s.residueFieldMap y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (residueFieldMap_section_bijective hs y)

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

-- The isomorphism is intentionally not `@[expose]`, so downstream modules cannot unfold it; the
-- two lemmas below are its public characterization, and their `(rfl)` proofs keep consumers from
-- having to rely on the definitional unfolding.

/-- The forward map of `residueFieldIsoOfSection` is the residue-field map of `f`, transported
along `f (s y) = y`. -/
@[simp]
lemma residueFieldIsoOfSection_hom (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).hom =
      (S.residueFieldCongr (apply_section hs y).symm).hom ≫ f.residueFieldMap (s y) :=
  (rfl)

/-- The inverse of `residueFieldIsoOfSection` is the residue-field map of the section. -/
@[simp]
lemma residueFieldIsoOfSection_inv (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).inv = s.residueFieldMap y :=
  (rfl)

end AlgebraicGeometry

end TauCeti
