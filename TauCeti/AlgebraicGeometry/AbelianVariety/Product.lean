/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# Products of abelian varieties

This file constructs the product of two abelian varieties over a field. Its underlying scheme is
the fibre product over the base field, equipped with the componentwise group law. The projections
and pairing operation exhibit this construction as the categorical binary product in
`AbelianVariety K`.

Finite products are part of the basic abelian-variety API required in Layer E of
`TauCetiRoadmap/JacobianChallenge/README.md`. In particular, the theorem of the cube and the
duality and polarization theory in that layer use powers of an abelian variety. No external
formalization is vendored; the construction reuses Mathlib's cartesian monoidal structures on
`Over (Spec K)` and on internal commutative groups.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

private lemma isProper_tensor (A B : AbelianVariety K) :
    IsProper (A.toOver ⊗ B.toOver).hom := by
  rw [Over.tensorObj_hom]
  exact MorphismProperty.comp_mem @IsProper _ _
    (inferInstanceAs (IsProper (pullback.fst A.toOver.hom B.toOver.hom)))
    (inferInstanceAs (IsProper A.toOver.hom))

private lemma geometricallyIntegral_tensor (A B : AbelianVariety K) :
    GeometricallyIntegral (A.toOver ⊗ B.toOver).hom := by
  rw [geometricallyIntegral_iff]
  intro L _ x Z fst snd h
  rw [Over.tensorObj_hom] at h
  let e :=
    ((h.isoIsPullback _ _ (.of_hasPullback _ _)) ≪≫
      (pullbackRightPullbackFstIso A.toOver.hom x
        (pullback.fst A.toOver.hom B.toOver.hom)).symm).symm
  exact IsIntegral.of_isIso e.hom

/-- The product of two abelian varieties over `K`. Its underlying scheme is their fibre product
over `Spec K`, and its group law is componentwise. -/
def prod (A B : AbelianVariety K) : AbelianVariety K :=
  letI := isProper_tensor A B
  letI := geometricallyIntegral_tensor A B
  ofGeometricallyIntegral (A.toOver ⊗ B.toOver)

/-- The group scheme underlying a product is the fibre product group scheme. -/
@[simp]
lemma prod_toOver (A B : AbelianVariety K) : (prod A B).toOver = A.toOver ⊗ B.toOver := by
  letI := isProper_tensor A B
  letI := geometricallyIntegral_tensor A B
  exact ofGeometricallyIntegral_toOver _

/-- The scheme underlying a product is the fibre product of the two underlying schemes over
`Spec K`. -/
@[simp]
lemma prod_toScheme (A B : AbelianVariety K) :
    (prod A B).toScheme = pullback A.toOver.hom B.toOver.hom := by
  rw [toScheme, prod_toOver, Over.tensorObj_left]

/-- The unit section of a product is the componentwise unit section. -/
@[simp]
lemma prod_one (A B : AbelianVariety K) :
    η[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      η[A.toOver ⊗ B.toOver] := by
  letI := isProper_tensor A B
  letI := geometricallyIntegral_tensor A B
  unfold prod
  exact ofGeometricallyIntegral_one _

/-- The multiplication on a product is componentwise multiplication. -/
@[simp]
lemma prod_mul (A B : AbelianVariety K) :
    μ[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      (eqToHom (prod_toOver A B) ⊗ₘ eqToHom (prod_toOver A B)) ≫
        μ[A.toOver ⊗ B.toOver] := by
  letI := isProper_tensor A B
  letI := geometricallyIntegral_tensor A B
  unfold prod
  exact ofGeometricallyIntegral_mul _

/-- Inversion on a product is componentwise inversion. -/
@[simp]
lemma prod_inv (A B : AbelianVariety K) :
    ι[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      eqToHom (prod_toOver A B) ≫ ι[A.toOver ⊗ B.toOver] := by
  letI := isProper_tensor A B
  letI := geometricallyIntegral_tensor A B
  unfold prod
  exact ofGeometricallyIntegral_inv _

namespace prod

/-- The first projection from a product of abelian varieties. -/
def fst (A B : AbelianVariety K) : prod A B ⟶ A := by
  refine Hom.mk'
    (eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver) ?_ ?_
  · rw [← Category.assoc, prod_one]
    simp
  · rw [← Category.assoc, prod_mul]
    simp

/-- The second projection from a product of abelian varieties. -/
def snd (A B : AbelianVariety K) : prod A B ⟶ B := by
  refine Hom.mk'
    (eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver) ?_ ?_
  · rw [← Category.assoc, prod_one]
    simp
  · rw [← Category.assoc, prod_mul]
    simp

/-- Pair two homomorphisms with a common source to obtain a homomorphism into a product. -/
def lift {A B C : AbelianVariety K} (f : C ⟶ A) (g : C ⟶ B) :
    C ⟶ prod A B := by
  refine Hom.mk'
    (CartesianMonoidalCategory.lift (Hom.toOverHom f) (Hom.toOverHom g) ≫
      eqToHom (prod_toOver A B).symm) ?_ ?_
  · simp [← cancel_mono (eqToHom (prod_toOver A B))]
  · simp [← cancel_mono (eqToHom (prod_toOver A B))]

/-- The morphism over `Spec K` underlying the first projection is the pullback projection. -/
@[simp]
lemma toOverHom_fst (A B : AbelianVariety K) :
    Hom.toOverHom (fst A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver :=
  by simp [fst]

/-- The morphism over `Spec K` underlying the second projection is the pullback projection. -/
@[simp]
lemma toOverHom_snd (A B : AbelianVariety K) :
    Hom.toOverHom (snd A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver :=
  by simp [snd]

/-- The morphism over `Spec K` underlying a pairing is the corresponding pullback lift. -/
@[simp]
lemma toOverHom_lift {A B C : AbelianVariety K} (f : C ⟶ A) (g : C ⟶ B) :
    Hom.toOverHom (lift f g) =
      CartesianMonoidalCategory.lift (Hom.toOverHom f) (Hom.toOverHom g) ≫
        eqToHom (prod_toOver A B).symm :=
  by simp [lift]

/-- The first projection of a pairing is its first component. -/
@[simp]
lemma lift_fst {A B C : AbelianVariety K} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ fst A B = f := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_lift, toOverHom_fst]
  simp only [← Category.assoc]
  simp

/-- The second projection of a pairing is its second component. -/
@[simp]
lemma lift_snd {A B C : AbelianVariety K} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ snd A B = g := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_lift, toOverHom_snd]
  simp only [← Category.assoc]
  simp

/-- Homomorphisms into a product are determined by their two projections. -/
@[ext]
lemma hom_ext {A B C : AbelianVariety K} {f g : C ⟶ prod A B} (hfst : f ≫ fst A B = g ≫ fst A B)
    (hsnd : f ≫ snd A B = g ≫ snd A B) : f = g := by
  apply Hom.toOverHom_injective
  rw [← cancel_mono (eqToHom (prod_toOver A B))]
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg Hom.toOverHom hfst
    simpa only [Hom.toOverHom_comp, toOverHom_fst, ← Category.assoc] using h
  · have h := congrArg Hom.toOverHom hsnd
    simpa only [Hom.toOverHom_comp, toOverHom_snd, ← Category.assoc] using h

/-- Precomposing a pairing composes each of its components. -/
@[reassoc, simp]
lemma comp_lift {A B C D : AbelianVariety K} (h : D ⟶ C) (f : C ⟶ A) (g : C ⟶ B) :
    h ≫ lift f g = lift (h ≫ f) (h ≫ g) := by
  apply hom_ext <;> simp

/-- Pairing the two projections of a homomorphism into a product recovers that homomorphism. -/
@[simp]
lemma lift_comp_fst_snd {A B C : AbelianVariety K} (f : C ⟶ prod A B) :
    lift (f ≫ fst A B) (f ≫ snd A B) = f := by
  apply hom_ext <;> simp

private def binaryFan (A B : AbelianVariety K) : BinaryFan A B :=
  BinaryFan.mk (fst A B) (snd A B)

private def binaryFanIsLimit (A B : AbelianVariety K) :
    IsLimit (binaryFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ lift f g)
    (fun f g ↦ lift_fst f g)
    (fun f g ↦ lift_snd f g)
    (fun f g _ hfst hsnd ↦
      hom_ext
        (hfst.trans (lift_fst f g).symm)
        (hsnd.trans (lift_snd f g).symm))

end prod

/-- The concrete product supplies the categorical binary product of abelian varieties. -/
instance hasBinaryProduct (A B : AbelianVariety K) : HasBinaryProduct A B :=
  HasLimit.mk ⟨prod.binaryFan A B, prod.binaryFanIsLimit A B⟩

/-- Abelian varieties over a field have categorical binary products. -/
instance hasBinaryProducts : HasBinaryProducts (AbelianVariety K) :=
  hasBinaryProducts_of_hasLimit_pair (AbelianVariety K)

/-- Abelian varieties over a field have all finite products. -/
instance hasFiniteProducts : HasFiniteProducts (AbelianVariety K) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
