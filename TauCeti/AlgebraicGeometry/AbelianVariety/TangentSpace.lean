/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Basic
public import TauCeti.AlgebraicGeometry.TangentSpace.Basic

/-!
# The tangent space of an abelian variety at the identity

The identity of an abelian variety `A/K` is a section `Spec K ⟶ A` of its structure morphism, so
the residue field `κ(0)` at the identity point is canonically the ground field; that
identification is `AbelianVariety.zeroResidueFieldRingEquiv`, built in
`TauCeti.AlgebraicGeometry.AbelianVariety.Basic`. It must be made explicit, because `κ(0)` and `K`
are not definitionally equal.

This file uses it to regard the Zariski tangent space at the identity as a vector space over the
ground field, and computes its dimension.

## Main declarations

* `AbelianVariety.TangentSpace A` is `T₀A`, the Zariski tangent space at the identity together
  with its `K`-vector-space structure;
* `AbelianVariety.finrank_tangentSpace_eq_finrank_cotangentSpace` computes its dimension as the
  dimension of `𝔪₀ / 𝔪₀²` over `κ(0)`.

For an *affine* group scheme the same tangent space is described in Hopf-algebra terms elsewhere
in the library: `TauCeti.Bialgebra.CotangentSpace` in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent` is the augmentation ideal modulo its square,
and `TauCeti.Algebra.AlgebraicGroup.Tangent.Basic` describes the tangent space at the identity by
counit-valued derivations. The construction here is the scheme-level Zariski tangent space at a
point, which applies to an abelian variety, and no comparison between the two is made.

This supplies the tangent-space part of the abelian-variety infrastructure explicitly listed in
`TauCetiRoadmap/JacobianChallenge/README.md` under "Inventory: what is missing (build here)" and
Layer E. It does not construct `Pic⁰` or prove the later comparison `T₀ Pic⁰ ≅ H¹(X, 𝒪_X)`.
No formalization is vendored: the ground-field dimension of `κ(0)` is Mathlib's
`Module.finrank_of_bijective_algebraMap`, the comparison of dimensions is
`Module.finrank_mul_finrank`, and the tangent space itself is the scheme-level API in
`TauCeti.AlgebraicGeometry.TangentSpace.Basic`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- The residue field at the identity has dimension one over the ground field, since the
structure map of the `K`-algebra `κ(0)` is the bijection `zeroResidueFieldRingEquiv.symm`. -/
@[simp]
lemma finrank_residueField_stalk_zeroPoint (A : AbelianVariety K) :
    Module.finrank K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) = 1 :=
  Module.finrank_of_bijective_algebraMap <| by
    rw [RingHom.algebraMap_toAlgebra]
    exact A.zeroResidueFieldRingEquiv.symm.bijective

/-- The residue field at the identity is a finite-dimensional `K`-vector space. -/
instance finiteDimensional_residueField_stalk_zeroPoint (A : AbelianVariety K) :
    FiniteDimensional K (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) :=
  .of_finrank_eq_succ (n := 0) A.finrank_residueField_stalk_zeroPoint

/-- The tangent space `T₀A` of an abelian variety at its identity: the Zariski tangent space of
the underlying scheme at `zeroPoint`, carrying the `K`-vector-space structure transported along
`zeroResidueFieldRingEquiv`.

This is a type synonym rather than an abbreviation, so that the residue-field action, the
ground-field action and their scalar tower are declared together on one type — the arrangement
Mathlib recommends, and the reason `Module.compHom` is registered here rather than on the
underlying `Module.Dual`. The equivalence `tangentSpaceLinearEquiv` is the public interface to
the underlying Zariski tangent space. -/
def TangentSpace (A : AbelianVariety K) : Type u :=
  ZariskiTangentSpace A.toScheme A.zeroPoint

instance tangentSpaceAddCommGroup (A : AbelianVariety K) : AddCommGroup A.TangentSpace :=
  inferInstanceAs (AddCommGroup (ZariskiTangentSpace A.toScheme A.zeroPoint))

instance tangentSpaceModuleResidueField (A : AbelianVariety K) :
    Module (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.TangentSpace :=
  inferInstanceAs (Module (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
    (ZariskiTangentSpace A.toScheme A.zeroPoint))

/-- The canonical residue-field-linear identification of `T₀A` with the underlying Zariski
tangent space. -/
noncomputable def tangentSpaceLinearEquiv (A : AbelianVariety K) :
    A.TangentSpace ≃ₗ[IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)]
      ZariskiTangentSpace A.toScheme A.zeroPoint where
  toFun := fun v ↦ v
  invFun := fun v ↦ v
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- The canonical equivalence sends a tangent vector to its underlying Zariski tangent vector. -/
@[simp]
lemma tangentSpaceLinearEquiv_apply (A : AbelianVariety K) (v : A.TangentSpace) :
    HEq (A.tangentSpaceLinearEquiv v) v := by
  unfold tangentSpaceLinearEquiv TangentSpace
  rfl

/-- Evaluate a tangent vector in `T₀A` on a Zariski cotangent vector through the canonical
identification `tangentSpaceLinearEquiv`. -/
noncomputable def tangentSpaceEval (A : AbelianVariety K) (v : A.TangentSpace)
    (m : ZariskiCotangentSpace A.toScheme A.zeroPoint) :
    IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint) :=
  A.tangentSpaceLinearEquiv v m

/-- Evaluation in `T₀A` is application of the underlying Zariski tangent vector. -/
@[simp]
lemma tangentSpaceEval_apply (A : AbelianVariety K) (v : A.TangentSpace)
    (m : ZariskiCotangentSpace A.toScheme A.zeroPoint) :
    A.tangentSpaceEval v m = A.tangentSpaceLinearEquiv v m :=
  by rw [tangentSpaceEval]

/-- Restrict scalars on `T₀A` from `κ(0)` to `K` along the canonical residue-field
equivalence. -/
instance tangentSpaceModule (A : AbelianVariety K) : Module K A.TangentSpace :=
  Module.compHom A.TangentSpace A.zeroResidueFieldRingEquiv.symm.toRingHom

/-- The ground-field action, the residue-field action, and the tangent-space action form the
expected scalar tower. -/
instance isScalarTower_tangentSpace (A : AbelianVariety K) : IsScalarTower K
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.TangentSpace :=
  IsScalarTower.of_compHom K _ _

/-- Ground-field scalar multiplication on `T₀A` is restriction of the residue-field action.

Not a simp lemma: with `algebraMap_zeroResidueField` the right-hand side is the ground-field
scalar `algebraMap K κ(0) k • v`, which Mathlib's `algebraMap_smul` rewrites back to the left-hand
side. -/
lemma tangentSpace_smul_def (A : AbelianVariety K) (k : K) (v : A.TangentSpace) :
    k • v = A.zeroResidueFieldRingEquiv.symm k • v :=
  (rfl)

/-- The tangent space is finite-dimensional over the residue field, since the underlying Zariski
tangent space is. -/
instance finiteDimensional_tangentSpace_residueField (A : AbelianVariety K) :
    FiniteDimensional (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
      A.TangentSpace :=
  Module.Finite.equiv A.tangentSpaceLinearEquiv.symm

/-- The tangent space of an abelian variety is finite-dimensional over the ground field. -/
instance finiteDimensional_tangentSpace (A : AbelianVariety K) :
    FiniteDimensional K A.TangentSpace :=
  Module.Finite.trans
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.TangentSpace

/-- The residue-field dimension of `T₀A` is that of the underlying Zariski tangent space: the
type synonym carries exactly the residue-field structure of the latter. -/
lemma finrank_residueField_tangentSpace (A : AbelianVariety K) :
    Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        A.TangentSpace =
      Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        (ZariskiTangentSpace A.toScheme A.zeroPoint) :=
  A.tangentSpaceLinearEquiv.finrank_eq

/-- Computing the dimension of `T₀A` over `K` is the same as computing it over the canonically
identified residue field `κ(0)`. -/
lemma finrank_tangentSpace_eq_finrank_residueField_tangentSpace (A : AbelianVariety K) :
    Module.finrank K A.TangentSpace =
      Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        A.TangentSpace := by
  have h := Module.finrank_mul_finrank K
    (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint)) A.TangentSpace
  simpa only [finrank_residueField_stalk_zeroPoint A, Nat.one_mul] using h.symm

/-- The dimension of the tangent space of an abelian variety over `K` is the dimension of the
cotangent space `𝔪₀ / 𝔪₀²` over `κ(0)`. -/
lemma finrank_tangentSpace_eq_finrank_cotangentSpace (A : AbelianVariety K) :
    Module.finrank K A.TangentSpace =
      Module.finrank (IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint))
        (ZariskiCotangentSpace A.toScheme A.zeroPoint) := by
  rw [finrank_tangentSpace_eq_finrank_residueField_tangentSpace,
    finrank_residueField_tangentSpace, Subspace.dual_finrank_eq]

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
