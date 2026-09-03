/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Equivalence
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Rigid

/-!
# The monoidal point-representation--comodule equivalence

The category of finite natural point representations of an affine group has the same tensor and
dual structures as the category of finite comodules over its coordinate Hopf algebra. This file
transports the established monoidal structure on finite comodules across the categorical
point-representation--comodule equivalence. The resulting equivalence is monoidal by
construction. Commutativity of the coordinate Hopf algebra supplies the symmetric braiding, and
over a field rigidity transports back along the monoidal equivalence.

## Main declarations

* `MonoidalCategory (TauCeti.FGPointRepresentationCat R H)`: the monoidal category of finite
  natural point representations.
* `TauCeti.fgPointRepresentationCategoryEquivalence`: now a monoidal equivalence with finite
  comodules.
* `SymmetricCategory (TauCeti.FGPointRepresentationCat R H)`: the symmetry that exchanges tensor
  factors.
* `RigidCategory (TauCeti.FGPointRepresentationCat k H)`: the rigid category of
  finite-dimensional point representations over a field.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1 and Proposition 9.44.

This completes the rigid monoidal refinement of the representation--comodule dictionary in
Layer 1 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u v

variable (R : Type u) [CommRing R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

namespace FGPointRepresentationCat

/-- Finite natural point representations form a monoidal category. Its tensor structure is
transported from the diagonal tensor product of finite comodules. -/
noncomputable instance instMonoidalCategory :
    MonoidalCategory (FGPointRepresentationCat.{u, v, u} R H) :=
  Monoidal.transport (fgPointRepresentationCategoryEquivalence R H).symm

/-- Finite natural point representations form a symmetric monoidal category. The braiding is
transported from the tensor-factor swap on finite comodules. -/
noncomputable instance instSymmetricCategory :
    SymmetricCategory (FGPointRepresentationCat.{u, v, u} R H) := by
  exact inferInstanceAs (SymmetricCategory (Monoidal.Transported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm))

end FGPointRepresentationCat

noncomputable instance fgPointRepresentationCategoryEquivalenceFunctorMonoidal :
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).functor.Monoidal := by
  exact inferInstanceAs ((Monoidal.equivalenceTransported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm).inverse.Monoidal)

noncomputable instance fgPointRepresentationCategoryEquivalenceInverseMonoidal :
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).inverse.Monoidal := by
  exact inferInstanceAs ((Monoidal.equivalenceTransported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm).functor.Monoidal)

noncomputable instance fgPointRepresentationCategoryEquivalence_isMonoidal :
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).IsMonoidal := by
  exact inferInstanceAs ((Monoidal.equivalenceTransported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm).symm.IsMonoidal)

/-- The forward functor of the finite point-representation--comodule equivalence preserves the
symmetric braiding. -/
noncomputable instance fgPointRepresentationCategoryEquivalenceFunctorBraided :
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).functor.Braided := by
  exact inferInstanceAs ((Monoidal.equivalenceTransported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm).inverse.Braided)

/-- The inverse functor of the finite point-representation--comodule equivalence preserves the
symmetric braiding. -/
noncomputable instance fgPointRepresentationCategoryEquivalenceInverseBraided :
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).inverse.Braided := by
  exact inferInstanceAs ((Monoidal.equivalenceTransported
    (fgPointRepresentationCategoryEquivalence.{u, v, u} R H).symm).functor.Braided)

namespace FGPointRepresentationCat

variable (k : Type u) [Field k]
variable (H : Type v) [CommRing H] [HopfAlgebra k H]

/-- Finite-dimensional natural point representations over a field form a rigid monoidal
category. The duals are transported from the antipode-twisted duals of finite comodules along the
monoidal representation--comodule equivalence. -/
noncomputable instance instRigidCategory :
    RigidCategory (FGPointRepresentationCat.{u, v, u} k H) :=
  CategoryTheory.rigidCategoryOfEquivalence
    (fgPointRepresentationCategoryEquivalence k H).toAdjunction

end FGPointRepresentationCat

end TauCeti
