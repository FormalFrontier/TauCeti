/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup

/-!
# Base change of abelian-variety homomorphisms

This file makes extension of the base field functorial on abelian varieties. For a field
extension `K → L`, pullback from schemes over `Spec K` to schemes over `Spec L` carries an
abelian-variety homomorphism `A ⟶ B` to a homomorphism `A.baseChange L ⟶ B.baseChange L`.
These maps assemble into `AbelianVariety.baseChangeFunctor`.

Base change also respects the pointwise group law on homomorphisms of
`TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup`:
`AbelianVariety.Hom.baseChangeMonoidHom` bundles it as a homomorphism
`(A ⟶ B) →* (A.baseChange L ⟶ B.baseChange L)` of the homomorphism groups, with
`AbelianVariety.Hom.baseChange_one`, `baseChange_mul`, `baseChange_inv`, `baseChange_div` and
`baseChange_zpow` its unbundled forms.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E's basic
abelian-variety API and the base-change compatibility required in the end goal. It will allow
the Jacobian base-change comparison to be stated and used as an isomorphism of abelian varieties,
not merely as an isomorphism of their underlying schemes.

No external mathematics is vendored. The implementation uses Mathlib's lax monoidal pullback
functor on `Over` categories, whose action on group objects proves that the pulled-back morphism
preserves the unit and multiplication, together with Mathlib's multiplicativity of a monoidal
functor on morphisms into a monoid object (`CategoryTheory.Functor.map_mul`).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- Base change of a homomorphism of abelian varieties along a field extension.

This is the morphism obtained by applying pullback in the appropriate `Over` category. The
monoidal structure on pullback ensures that it is again a group-scheme homomorphism. -/
noncomputable def Hom.baseChange {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] : A.baseChange L ⟶ B.baseChange L := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  exact InducedCategory.homMk
    (eqToHom (commGrpMk_baseChange_toOver A L) ≫ F.mapCommGrp.map f.hom ≫
      eqToHom (commGrpMk_baseChange_toOver B L).symm)

/-- The underlying morphism over `Spec L` of a base-changed homomorphism is the pullback of its
underlying morphism over `Spec K`. -/
@[simp]
lemma Hom.toOverHom_baseChange {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.toOverHom (Hom.baseChange f L) =
      eqToHom (baseChange_toOver A L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
          (Hom.toOverHom f) ≫
        eqToHom (baseChange_toOver B L).symm := by
  -- No public rewrite lemma exposes both induced-category and `CommGrp.forget` wrappers;
  -- `change` displays the morphism supplied to `InducedCategory.homMk`.
  change (CommGrp.forget _).map
      (eqToHom (commGrpMk_baseChange_toOver A L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map f.hom ≫
        eqToHom (commGrpMk_baseChange_toOver B L).symm) = _
  simp only [Functor.map_comp, eqToHom_map]
  rfl

/-- The underlying scheme morphism of a base-changed homomorphism is the left component of the
pulled-back morphism in the `Over` category. -/
@[simp]
lemma Hom.toSchemeHom_baseChange {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.toSchemeHom (Hom.baseChange f L) =
      (eqToHom (baseChange_toOver A L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
          (Hom.toOverHom f) ≫
        eqToHom (baseChange_toOver B L).symm).left :=
  congrArg Over.Hom.left (Hom.toOverHom_baseChange f L)

/-- Base change preserves identity homomorphisms. -/
@[simp]
lemma Hom.baseChange_id (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (𝟙 A) L = 𝟙 (A.baseChange L) := by
  apply InducedCategory.hom_ext
  -- `InducedCategory.hom_ext` leaves bundled `CommGrp` morphisms; `change` displays the
  -- morphism supplied by `Hom.baseChange`, for which the functor identity law applies.
  change eqToHom (commGrpMk_baseChange_toOver A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map
        (𝟙 (CommGrp.mk A.toOver)) ≫
      eqToHom (commGrpMk_baseChange_toOver A L).symm = 𝟙 (CommGrp.mk (A.baseChange L).toOver)
  simp

/-- Base change preserves composition of homomorphisms. -/
@[simp]
lemma Hom.baseChange_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (f ≫ g) L = Hom.baseChange f L ≫ Hom.baseChange g L := by
  apply InducedCategory.hom_ext
  -- As above, this exposes the bundled morphisms supplied to `InducedCategory.homMk`, so the
  -- functor composition law and cancellation of the transport isomorphisms can be used.
  change eqToHom (commGrpMk_baseChange_toOver A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map
        (f.hom ≫ g.hom) ≫ eqToHom (commGrpMk_baseChange_toOver C L).symm =
    (eqToHom (commGrpMk_baseChange_toOver A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map f.hom ≫
      eqToHom (commGrpMk_baseChange_toOver B L).symm) ≫
    (eqToHom (commGrpMk_baseChange_toOver B L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map g.hom ≫
      eqToHom (commGrpMk_baseChange_toOver C L).symm)
  simp [Category.assoc]

/-- Extension of the base field defines a functor between the categories of abelian varieties.

Its action is characterized by `AbelianVariety.baseChangeFunctor_obj` and
`AbelianVariety.baseChangeFunctor_map`. -/
noncomputable def baseChangeFunctor (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety K ⥤ AbelianVariety L where
  obj A := A.baseChange L
  map f := Hom.baseChange f L
  map_id A := Hom.baseChange_id A L
  map_comp f g := Hom.baseChange_comp f g L

@[simp]
lemma baseChangeFunctor_obj (L : Type u) [Field L] [Algebra K L]
    (A : AbelianVariety K) :
    (baseChangeFunctor L).obj A = A.baseChange L :=
  (rfl)

@[simp]
lemma baseChangeFunctor_map {A B : AbelianVariety K} (L : Type u) [Field L] [Algebra K L]
    (f : A ⟶ B) :
    (baseChangeFunctor L).map f =
      eqToHom (baseChangeFunctor_obj L A) ≫ Hom.baseChange f L ≫
        eqToHom (baseChangeFunctor_obj L B).symm :=
  (rfl)

/-! ### Compatibility with the pointwise group law

Base change is a homomorphism for the pointwise group law of
`TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup`, not merely a functor. The two private
instances below say that the transport isomorphism `eqToHom (baseChange_toOver A L)` between the
group scheme underlying `A.baseChange L` and the pullback of the one underlying `A` is an
isomorphism of monoid objects; they are proof support for the two lemmas that follow, which
together with Mathlib's multiplicativity of a monoidal functor on morphisms into a monoid object
give the public interface. -/

open scoped Hom

/-- The transport isomorphism identifying the group scheme underlying `A.baseChange L` with the
pullback of the group scheme underlying `A` preserves the unit and the multiplication: by
construction, those of the base change *are* the pulled-back ones. -/
private instance isMonHom_eqToHom_baseChange_toOver (A : AbelianVariety K) (L : Type u) [Field L]
    [Algebra K L] :
    IsMonHom (eqToHom (baseChange_toOver A L)) where
  one_hom := by rw [baseChange_one, Functor.obj.η_def]
  mul_hom := by rw [baseChange_mul, Functor.obj.μ_def]

/-- The inverse transport isomorphism is a homomorphism of monoid objects as well. -/
private instance isMonHom_eqToHom_baseChange_toOver_symm (A : AbelianVariety K) (L : Type u)
    [Field L] [Algebra K L] :
    IsMonHom (eqToHom (baseChange_toOver A L).symm) :=
  haveI : IsMonHom (eqToIso (baseChange_toOver A L)).hom :=
    isMonHom_eqToHom_baseChange_toOver A L
  inferInstanceAs (IsMonHom (eqToIso (baseChange_toOver A L)).inv)

/-- Base change carries the identity element of the group of homomorphisms — the homomorphism
factoring through the unit section — to the identity element. -/
@[simp]
lemma Hom.baseChange_one (A B : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (1 : A ⟶ B) L = 1 := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_baseChange, Hom.toOverHom_one, Functor.map_one, MonObj.one_comp,
    MonObj.comp_one]
  rfl

/-- Base change is multiplicative for the pointwise group law: pulling back the pointwise product
of two homomorphisms gives the pointwise product of their pullbacks. -/
@[simp]
lemma Hom.baseChange_mul {A B : AbelianVariety K} (f g : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (f * g) L = Hom.baseChange f L * Hom.baseChange g L := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_baseChange, Hom.toOverHom_mul, Functor.map_mul, MonObj.mul_comp,
    MonObj.comp_mul]
  rfl

/-- Base change along a field extension, as a homomorphism of the groups of homomorphisms of
abelian varieties. -/
def Hom.baseChangeMonoidHom (A B : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    (A ⟶ B) →* (A.baseChange L ⟶ B.baseChange L) where
  toFun f := Hom.baseChange f L
  map_one' := Hom.baseChange_one A B L
  map_mul' f g := Hom.baseChange_mul f g L

@[simp]
lemma Hom.baseChangeMonoidHom_apply {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChangeMonoidHom A B L f = Hom.baseChange f L :=
  (rfl)

/-- Base change preserves pointwise inverses of homomorphisms. -/
@[simp]
lemma Hom.baseChange_inv {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange f⁻¹ L = (Hom.baseChange f L)⁻¹ :=
  map_inv (Hom.baseChangeMonoidHom A B L) f

/-- Base change preserves pointwise quotients of homomorphisms. -/
@[simp]
lemma Hom.baseChange_div {A B : AbelianVariety K} (f g : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (f / g) L = Hom.baseChange f L / Hom.baseChange g L :=
  map_div (Hom.baseChangeMonoidHom A B L) f g

/-- Base change preserves pointwise integer powers of homomorphisms. -/
@[simp]
lemma Hom.baseChange_zpow {A B : AbelianVariety K} (f : A ⟶ B) (n : ℤ)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (f ^ n) L = Hom.baseChange f L ^ n :=
  map_zpow (Hom.baseChangeMonoidHom A B L) f n

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
