/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `residueFieldRingEquivOfSection`: over a base `Spec K` with `K` a field, the residue field at a
  `K`-rational point *is* `K`, through the evaluation map that Mathlib attaches to any `K`-point,
  `X.descResidueField (Scheme.stalkClosedPointTo s)`. The section hypothesis makes that map
  bijective (`descResidueField_bijective_of_section`), which is what lets a `K`-rational point
  transport `K`-structures to the fibre data at the point.

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
`Scheme.residueFieldCongr` and `Scheme.Hom.residueDegree` API, `CategoryTheory.asIso` and
`CategoryTheory.Iso.inv_ext` for the isomorphism, Mathlib's `Scheme.descResidueField`,
`Scheme.stalkClosedPointTo` and `Scheme.residue_descResidueField` for the rational-point
evaluation map, and Tau Ceti's `residueDegree_comp` and `residueDegree_eq_one_iff`.
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
lemma section_apply (hs : s ≫ f = 𝟙 S) (y : S) : f (s y) = y :=
  leftInverse_of_section hs y

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

-- `section_apply` and `residueDegree_eq_one_of_section` above are the normal-form lemmas of this
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
  rw [residueDegree_comp, residueDegree_eq_one_of_section hs, Nat.mul_one, section_apply hs]

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
    (S.residueFieldCongr (section_apply hs y).symm).hom ≫
        f.residueFieldMap (s y) ≫ s.residueFieldMap y = 𝟙 (S.residueField y) := by
  rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hs y]
  simp only [Scheme.residueFieldMap_id]
  change (S.residueFieldCongr (section_apply hs y).symm).hom ≫
      (S.residueFieldCongr (section_apply hs y)).hom = 𝟙 _
  simp

/-- The residue field of `X` at a point in the image of a section is the residue field of the
base at the corresponding point of the base. The inverse is the residue-field map of the
section. -/
noncomputable def residueFieldIsoOfSection (hs : s ≫ f = 𝟙 S) (y : S) :
    S.residueField y ≅ X.residueField (s y) :=
  haveI := isIso_residueFieldMap_of_section hs y
  asIso ((S.residueFieldCongr (section_apply hs y).symm).hom ≫ f.residueFieldMap (s y))

-- The isomorphism is intentionally not `@[expose]`, so downstream modules cannot unfold it; the
-- two lemmas below are its public characterization, which keeps consumers from having to rely on
-- the definitional unfolding.

/-- The forward map of `residueFieldIsoOfSection` is the residue-field map of `f`, transported
along `f (s y) = y`. -/
@[simp]
lemma residueFieldIsoOfSection_hom (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).hom =
      (S.residueFieldCongr (section_apply hs y).symm).hom ≫ f.residueFieldMap (s y) :=
  (rfl)

/-- The inverse of `residueFieldIsoOfSection` is the residue-field map of the section. -/
@[simp]
lemma residueFieldIsoOfSection_inv (hs : s ≫ f = 𝟙 S) (y : S) :
    (residueFieldIsoOfSection hs y).inv = s.residueFieldMap y :=
  Iso.inv_ext <| by
    rw [residueFieldIsoOfSection_hom, Category.assoc,
      residueFieldMap_comp_residueFieldMap_of_section hs y]

/-! ### The residue field at a rational point

Over a base `Spec K` with `K` a field, the residue field at a rational point is not merely
isomorphic to the residue field of the base: it *is* the ground field `K`, through the canonical
evaluation map that Mathlib attaches to any `K`-point of `X`, namely
`X.descResidueField (Scheme.stalkClosedPointTo s)`. -/

section OverField

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {s : Spec (.of K) ⟶ X}

/-- A section of `f : X ⟶ Spec K` maps the stalk at its image point onto `K`: the induced map
`𝒪_{X, s 0} ⟶ K` of Mathlib's `Scheme.stalkClosedPointTo` is surjective, because composing it
with the stalk map of `f` gives the corresponding map for the identity of `Spec K`, which is an
isomorphism. -/
lemma stalkClosedPointTo_surjective_of_section (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    Function.Surjective (Scheme.stalkClosedPointTo s) := by
  -- The hypothesis is used through a universally quantified morphism, since the *type* of
  -- `Scheme.stalkClosedPointTo t` depends on `t`; substituting `t := 𝟙 _` avoids a transport.
  have key : ∀ t : Spec (.of K) ⟶ Spec (.of K), t = 𝟙 (Spec (.of K)) →
      Function.Surjective (Scheme.stalkClosedPointTo t) := by
    rintro t rfl
    have H : ∀ x : (Spec (.of K) : Scheme.{u}),
        IsIso (Scheme.Hom.stalkMap (𝟙 (Spec (.of K))) x) := fun _ ↦ inferInstance
    have : IsIso (Scheme.stalkClosedPointTo (𝟙 (Spec (.of K)))) := by
      rw [Scheme.stalkClosedPointTo]
      have := H (IsLocalRing.closedPoint K)
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2
  intro a
  obtain ⟨b, hb⟩ := key _ hs a
  -- The last step is `ConcreteCategory.comp_apply`, which is definitional; it cannot be applied
  -- as a rewrite here, because the point `s (closedPoint K)` inhabits `↥(Spec (.of K))` only up
  -- to unfolding `Spec`, so the rewritten term is not type-correct at reducible transparency.
  exact ⟨Scheme.Hom.stalkMap f _ b, by rw [← hb, Scheme.stalkClosedPointTo_comp]; rfl⟩

/-- The canonical evaluation map `κ(s 0) ⟶ K` at a `K`-rational point is bijective: it is
injective as a map of fields, and surjective because the stalk already surjects onto `K`. -/
lemma descResidueField_bijective_of_section (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    Function.Bijective (X.descResidueField (Scheme.stalkClosedPointTo s)) := by
  refine ⟨(X.descResidueField (Scheme.stalkClosedPointTo s)).hom.injective, fun k ↦ ?_⟩
  obtain ⟨a, ha⟩ := stalkClosedPointTo_surjective_of_section hs k
  refine ⟨X.residue _ a, ?_⟩
  rw [← ha, ← ConcreteCategory.comp_apply, Scheme.residue_descResidueField]

/-- The residue field of `X` at a `K`-rational point is canonically the ground field `K`, through
the evaluation map of the point. -/
noncomputable def residueFieldRingEquivOfSection (hs : s ≫ f = 𝟙 (Spec (.of K))) :
    IsLocalRing.ResidueField (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) ≃+* K :=
  RingEquiv.ofBijective (X.descResidueField (Scheme.stalkClosedPointTo s)).hom
    (descResidueField_bijective_of_section hs)

/-- `residueFieldRingEquivOfSection` is the evaluation map of the rational point. -/
@[simp]
lemma residueFieldRingEquivOfSection_apply (hs : s ≫ f = 𝟙 (Spec (.of K)))
    (z : IsLocalRing.ResidueField (X.presheaf.stalk (s (IsLocalRing.closedPoint K)))) :
    residueFieldRingEquivOfSection hs z =
      X.descResidueField (Scheme.stalkClosedPointTo s) z :=
  (rfl)

end OverField

end AlgebraicGeometry

end TauCeti
