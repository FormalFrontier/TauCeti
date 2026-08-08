/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.TangentSpace.Basic

/-!
# The tangent space of an abelian variety at the identity

The identity of an abelian variety `A/K` is a section `Spec K ⟶ A` of its structure morphism.
Evaluating that section at the unique point of `Spec K` gives `AbelianVariety.zeroPoint A`.
The section identifies the residue field at this point with `K`; this identification must be made
explicit because `κ(0)` and `K` are not definitionally equal.

## Main declarations

* `AbelianVariety.zeroSection A` is the identity section of `A`;
* `AbelianVariety.zeroPoint A` is its value at the closed point of `Spec K`;
* `AbelianVariety.zeroResidueFieldIso A` identifies `κ(0)` with `K`;
* `AbelianVariety.tangentSpace A` is `T₀A`, carrying its resulting `K`-vector-space structure;
* `AbelianVariety.finrank_tangentSpace_eq_finrank_cotangentSpace` computes its dimension as the
  dimension of `𝔪₀ / 𝔪₀²` over `κ(0)`.

This is the direct type-theoretic prerequisite for
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, milestone
"Tangent space `T₀ Pic⁰ ≅ H¹(X, 𝒪_X)`, hence `dim (Jac X) = g`". After this file, the milestone
still requires construction of the Picard scheme and the comparison of its tangent space with
cohomology. No formalization is vendored. The residue-field comparison reuses
`residueFieldIsoOfSection`, and the tangent space reuses the scheme-level API in
`TauCeti.AlgebraicGeometry.TangentSpace.Basic`.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- The identity section `Spec K ⟶ A` of an abelian variety. -/
abbrev zeroSection (A : AbelianVariety K) : Spec (.of K) ⟶ A.toScheme :=
  η[A.toOver].left

/-- The identity section is a section of the structure morphism of `A`. -/
@[reassoc (attr := simp)]
lemma zeroSection_comp_toOver_hom (A : AbelianVariety K) :
    A.zeroSection ≫ A.toOver.hom = 𝟙 (Spec (.of K)) := by
  simpa only [zeroSection, Over.tensorUnit_hom] using η[A.toOver].w

/-- The identity point of an abelian variety, obtained by evaluating its identity section at the
unique point of `Spec K`. -/
def zeroPoint (A : AbelianVariety K) : A.toScheme :=
  A.zeroSection (IsLocalRing.closedPoint K)

/-- The structure morphism sends the identity point to the unique point of `Spec K`. -/
@[simp]
lemma toOver_hom_zeroPoint (A : AbelianVariety K) :
    A.toOver.hom A.zeroPoint = IsLocalRing.closedPoint K := by
  change (A.zeroSection ≫ A.toOver.hom) (IsLocalRing.closedPoint K) = _
  rw [zeroSection_comp_toOver_hom]
  rfl

/-- The residue field of the unique point of `Spec K` is canonically isomorphic to `K`.

The intermediate `Ideal.ResidueField` is the quotient field of the bottom prime of `K`; the
second isomorphism is Mathlib's canonical equivalence for a prime ideal in a field. -/
private def baseResidueFieldIso (K : Type u) [Field K] :
    (Spec (.of K)).residueField (IsLocalRing.closedPoint K) ≅ .of K :=
  (Scheme.Spec.residueFieldIso (.of K) (IsLocalRing.closedPoint K)).trans
    (Ideal.algEquivResidueFieldOfField
      (IsLocalRing.closedPoint K).asIdeal).symm.toRingEquiv.toCommRingCatIso

/-- The residue field `κ(0)` of an abelian variety at its identity is canonically isomorphic to
the ground field. The first factor is the residue-field equivalence induced by the identity
section; the second identifies the residue field of the unique point of `Spec K` with `K`. -/
def zeroResidueFieldIso (A : AbelianVariety K) :
    A.toScheme.residueField A.zeroPoint ≅ .of K :=
  (residueFieldIsoOfSection (zeroSection_comp_toOver_hom A)
    (IsLocalRing.closedPoint K)).symm.trans (baseResidueFieldIso K)

/-- The ring equivalence `κ(0) ≃+* K` underlying `zeroResidueFieldIso`. This formulation exposes
the actual local-ring residue-field type used in the definition of the tangent space. -/
def zeroResidueFieldRingEquiv (A : AbelianVariety K) :
    IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint) ≃+* K :=
  A.zeroResidueFieldIso.commRingCatIsoToRingEquiv

/-- The residue field at the identity is a `K`-algebra via the inverse of
`zeroResidueFieldRingEquiv`. -/
instance (A : AbelianVariety K) :
    Algebra K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) :=
  A.zeroResidueFieldRingEquiv.symm.toRingHom.toAlgebra

/-- The tangent space `T₀A` of an abelian variety at its identity. As a type it is the Zariski
tangent space of the underlying scheme at `zeroPoint`; the instances below regard it as a vector
space over the ground field `K`. -/
abbrev tangentSpace (A : AbelianVariety K) : Type u :=
  ZariskiTangentSpace A.toScheme A.zeroPoint

/-- Restrict scalars on `T₀A` from `κ(0)` to `K` along the canonical residue-field
equivalence. -/
instance tangentSpace_module (A : AbelianVariety K) : Module K A.tangentSpace :=
  Module.compHom A.tangentSpace A.zeroResidueFieldRingEquiv.symm.toRingHom

/-- The ground-field action, the residue-field action, and the tangent-space action form the
expected scalar tower. -/
instance tangentSpace_isScalarTower (A : AbelianVariety K) : IsScalarTower K
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.tangentSpace :=
  IsScalarTower.of_compHom K _ _

/-- The tangent space of an abelian variety is finite-dimensional over its residue field.
Smoothness implies finite type over the Noetherian field base, hence the underlying scheme is
locally Noetherian. -/
instance tangentSpace_finiteDimensional_residueField (A : AbelianVariety K) :
    FiniteDimensional (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
      A.tangentSpace := by
  let _ : IsLocallyNoetherian A.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian A.toOver.hom
  infer_instance

/-- The tangent space of an abelian variety is finite-dimensional over the ground field. -/
instance tangentSpace_finiteDimensional (A : AbelianVariety K) :
    FiniteDimensional K A.tangentSpace := by
  exact Module.Finite.trans
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.tangentSpace

/-- The residue field at the identity has dimension one over the ground field. -/
@[simp]
lemma finrank_zeroResidueField (A : AbelianVariety K) :
    Module.finrank K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) = 1 := by
  let e : K ≃ₗ[K] IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint) :=
    Module.compHom.toLinearEquiv A.zeroResidueFieldRingEquiv.symm
  exact e.finrank_eq.symm.trans (Module.finrank_self K)

/-- Computing the dimension of `T₀A` over `K` is the same as computing it over the canonically
identified residue field `κ(0)`. -/
lemma finrank_tangentSpace_eq_finrank_residueField (A : AbelianVariety K) :
    Module.finrank K A.tangentSpace =
      Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        A.tangentSpace := by
  have h := Module.finrank_mul_finrank K
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.tangentSpace
  simpa only [finrank_zeroResidueField A, Nat.one_mul] using h.symm

/-- The dimension of the tangent space of an abelian variety over `K` is the dimension of the
cotangent space `𝔪₀ / 𝔪₀²` over `κ(0)`. -/
lemma finrank_tangentSpace_eq_finrank_cotangentSpace (A : AbelianVariety K) :
    Module.finrank K A.tangentSpace =
      Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        (ZariskiCotangentSpace A.toScheme A.zeroPoint) := by
  rw [finrank_tangentSpace_eq_finrank_residueField, finrank_zariskiTangentSpace_eq]

end


end AbelianVariety

end AlgebraicGeometry

end TauCeti
