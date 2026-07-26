/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic

/-!
# The group of homomorphisms of abelian varieties

For abelian varieties `A B : AbelianVariety K`, the homomorphisms `A ⟶ B` form a commutative
group under the pointwise group law of the target: since the group scheme underlying `B` is
commutative, the pointwise product `f * g := lift f g ≫ μ[B]` of two homomorphisms is again a
homomorphism. This file transports Mathlib's group structure on morphisms into a commutative group
object (`CategoryTheory.MonObj.Hom.commGroup`, applied in the category of group objects over
`Spec K`) onto `A ⟶ B`, and records how the underlying morphism over `Spec K` interacts with the
group operations.

The group law is written **multiplicatively**, matching the multiplicative encoding
(`GrpObj`, `μ`, `η`, `ι`) of the group-object structure carried by an `AbelianVariety`; for the
Jacobian this pointwise product is the tensor product of line bundles.

* `AbelianVariety.Hom.instCommGroup`: the commutative group structure on `A ⟶ B`
  (a `scoped instance`);
* `AbelianVariety.Hom.homMulEquiv`: the identification of `A ⟶ B` with homomorphisms of the
  underlying commutative group objects as a multiplicative equivalence;
* `AbelianVariety.Hom.toOverHom_mul`, `toOverHom_one`, `toOverHom_inv`, `toOverHom_div`: the
  underlying morphism over `Spec K` is a homomorphism of these groups;
* `AbelianVariety.Hom.mul_comp` and `AbelianVariety.Hom.comp_mul`: composition is bimultiplicative,
  so `AbelianVariety K` behaves like a preadditive category with respect to this group law.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", by supplying the group structure
on the homomorphism sets. Layer F's universal property produces a *unique* homomorphism of abelian
varieties; the group law here is the ambient structure in which that uniqueness and the Albanese
functoriality are expressed. No external mathematics is vendored; the group structure is transported
from Mathlib's `CategoryTheory.MonObj.Hom.commGroup` on morphisms into a commutative group object,
via the existing Tau Ceti abelian-variety homomorphism API.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

open scoped CategoryTheory.MonObj

noncomputable section

namespace Hom

/-- Homomorphisms of abelian varieties over `K` form a commutative group under the pointwise group
law of the target, transported from Mathlib's group structure on morphisms into a commutative group
object. -/
scoped instance instCommGroup (A B : AbelianVariety K) : CommGroup (A ⟶ B) :=
  (InducedCategory.homEquiv.trans InducedCategory.homEquiv).commGroup

variable {A B : AbelianVariety K}

/-- Identifying a homomorphism of abelian varieties with its underlying homomorphism of commutative
group objects is a group isomorphism onto the latter's group of homomorphisms. -/
def homMulEquiv (A B : AbelianVariety K) :
    (A ⟶ B) ≃* ((CommGrp.mk A.toOver).toGrp ⟶ (CommGrp.mk B.toOver).toGrp) where
  __ := InducedCategory.homEquiv.trans InducedCategory.homEquiv
  map_mul' := fun _ _ ↦
    (InducedCategory.homEquiv.trans InducedCategory.homEquiv).apply_symm_apply _

/-- The hom-set multiplicative equivalence evaluates to the nested underlying group-object
homomorphism. -/
@[simp] lemma homMulEquiv_apply (f : A ⟶ B) :
    homMulEquiv A B f = f.hom.hom := by
  unfold homMulEquiv
  rfl

/-- The underlying morphism over `Spec K` of a homomorphism of abelian varieties is the underlying
morphism of the corresponding commutative-group-object homomorphism. -/
private lemma toOverHom_eq_homMulEquiv (f : A ⟶ B) :
    toOverHom f = (homMulEquiv A B f).hom.hom := by
  rw [homMulEquiv_apply]
  simp [toOverHom, toOverFunctor]

/-- The underlying morphism over `Spec K` sends the product of two homomorphisms to the pointwise
product. -/
@[simp] lemma toOverHom_mul (f g : A ⟶ B) :
    toOverHom (f * g) = toOverHom f * toOverHom g := by
  rw [toOverHom_eq_homMulEquiv, toOverHom_eq_homMulEquiv,
    toOverHom_eq_homMulEquiv, map_mul]
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul]

/-- The underlying morphism over `Spec K` sends the identity of the group of homomorphisms to the
identity element `toUnit A.toOver ≫ η[B.toOver]` (the constant homomorphism through the unit
section). -/
@[simp] lemma toOverHom_one :
    toOverHom (1 : A ⟶ B) = 1 := by
  rw [toOverHom_eq_homMulEquiv, map_one]
  simp only [Grp.Hom.hom_one, Mon.Hom.hom_one]

/-- The underlying morphism over `Spec K` sends the inverse of a homomorphism to the pointwise
inverse. -/
@[simp] lemma toOverHom_inv (f : A ⟶ B) :
    toOverHom f⁻¹ = (toOverHom f)⁻¹ := by
  rw [toOverHom_eq_homMulEquiv, toOverHom_eq_homMulEquiv, map_inv]
  simp only [Grp.Hom.hom_hom_inv]

/-- The underlying morphism over `Spec K` sends the quotient of two homomorphisms to the pointwise
quotient. -/
@[simp] lemma toOverHom_div (f g : A ⟶ B) :
    toOverHom (f / g) = toOverHom f / toOverHom g := by
  rw [toOverHom_eq_homMulEquiv, toOverHom_eq_homMulEquiv,
    toOverHom_eq_homMulEquiv, map_div]
  simp only [Grp.Hom.hom_hom_div]

/-! ### Bilinearity of composition -/

/-- Composition of homomorphisms of abelian varieties distributes over the pointwise product on the
right: post-composition by a homomorphism is multiplicative. -/
@[simp, reassoc] lemma mul_comp {A B C : AbelianVariety K} (f g : A ⟶ B) (h : B ⟶ C) :
    (f * g) ≫ h = f ≫ h * g ≫ h := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_mul, MonObj.mul_comp]

/-- Composition of homomorphisms of abelian varieties distributes over the pointwise product on the
left: pre-composition by a homomorphism is multiplicative. -/
@[simp, reassoc] lemma comp_mul {A B C : AbelianVariety K} (f : A ⟶ B) (g h : B ⟶ C) :
    f ≫ (g * h) = f ≫ g * f ≫ h := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_mul, MonObj.comp_mul]

/-- Post-composition sends the identity element of a homomorphism group to the identity element. -/
@[simp] lemma one_comp {A B C : AbelianVariety K} (h : B ⟶ C) :
    (1 : A ⟶ B) ≫ h = 1 := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_one, MonObj.one_comp]

/-- Pre-composition sends the identity element of a homomorphism group to the identity element. -/
@[simp] lemma comp_one {A B C : AbelianVariety K} (f : A ⟶ B) :
    f ≫ (1 : B ⟶ C) = 1 := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_one, MonObj.comp_one]

/-- Post-composition preserves pointwise inverses of homomorphisms. -/
@[simp] lemma inv_comp {A B C : AbelianVariety K} (f : A ⟶ B) (h : B ⟶ C) :
    f⁻¹ ≫ h = (f ≫ h)⁻¹ := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_inv, GrpObj.inv_comp]

/-- Post-composition preserves pointwise quotients of homomorphisms. -/
@[simp] lemma div_comp {A B C : AbelianVariety K} (f g : A ⟶ B) (h : B ⟶ C) :
    (f / g) ≫ h = (f ≫ h) / (g ≫ h) := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_div, GrpObj.div_comp]

/-- Pre-composition preserves pointwise inverses of homomorphisms. -/
@[simp] lemma comp_inv {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ g⁻¹ = (f ≫ g)⁻¹ := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_inv, GrpObj.comp_inv]

/-- Pre-composition preserves pointwise quotients of homomorphisms. -/
@[simp] lemma comp_div {A B C : AbelianVariety K} (f : A ⟶ B) (g h : B ⟶ C) :
    f ≫ (g / h) = (f ≫ g) / (f ≫ h) := by
  apply Hom.toOverFunctor.map_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_div, GrpObj.comp_div]

end Hom

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
