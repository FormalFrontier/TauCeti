/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.SpecialLinear

/-!
# Reductivity of the type A standard carrier

The full-weight type `A_r` standard carrier is an explicit closed subgroup of `GL_{r+1}` over
`ℤ`, constructed from its numbered root subgroups and weight torus. After specialization to an
algebraically closed field, its defining Hopf ideal is the determinant-one ideal by
`TauCeti.SlStd.baseChangeDefiningIdeal_eq_specialLinearDefiningHopfIdeal`. Thus its coordinate
Hopf algebra is isomorphic to that of `SL_{r+1}`.

This file packages the specialized carrier as a finite-type commutative Hopf algebra, lifts the
coordinate isomorphism to that category, and transports the reductivity of `SL_{r+1}` across it.
Consequently the explicit type `A` carrier has the substantive reductive-group property required
of a Chevalley--Demazure carrier over every algebraically closed field, in arbitrary
characteristic.

## Main declarations

* `TauCeti.SlStd.finiteTypeSpecialization`: the specialized type `A_r` carrier as a finite-type
  commutative Hopf algebra.
* `TauCeti.SlStd.finiteTypeSpecializationSpecialLinearIso`: its canonical isomorphism with the
  coordinate Hopf algebra of `SL_{r+1}` over an algebraically closed field.
* `TauCeti.SlStd.reductiveCommHopfAlgProperty_finiteTypeSpecialization`: the specialized type
  `A_r` carrier is reductive.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of the ReductiveGroups roadmap:
the explicit type `A` carrier is now reductive over the algebraically closed fields on which the
finite groups of Lie type are constructed. Its consumer is milestone L0, "pinned ambient groups",
of the CFSGStatement roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.SlStd

universe u

noncomputable section

variable (r : ℕ)

section

variable (k : Type u) [CommRing k]

/-- The specialization of the full-weight type `A_r` carrier to `k`, bundled with its finite-type
property. It is the quotient of `O(GL_{r+1}/k)` by the transported integral carrier equations. -/
noncomputable def finiteTypeSpecialization : FiniteTypeCommHopfAlgCat k :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra k (r + 1),
      inferInstanceAs
        (Algebra.FiniteType k (GeneralLinear.coordinateHopfAlgebra k (r + 1)))⟩ :
      FiniteTypeCommHopfAlgCat k)
    (baseChangeDefiningIdeal r k)

/-- The object underlying the finite-type specialization is the quotient coordinate Hopf algebra
used by the base-change presentation of the carrier. -/
@[simp]
theorem finiteTypeSpecialization_obj :
    (finiteTypeSpecialization r k).obj =
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k (r + 1))
        (baseChangeDefiningIdeal r k) := by
  rw [finiteTypeSpecialization]

end

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, the specialized full-weight type `A_r` carrier is
canonically isomorphic to the finite-type coordinate Hopf algebra of `SL_{r+1}`. -/
noncomputable def finiteTypeSpecializationSpecialLinearIso :
    finiteTypeSpecialization r k ≅
      SpecialLinear.finiteTypeCoordinateHopfAlgebra k (r + 1) :=
  ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k)
    (eqToIso (finiteTypeSpecialization_obj r k) ≪≫
      baseChangeCoordinateSpecialLinearIso r k ≪≫
      eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k (r + 1)).symm)

/-- The underlying coordinate morphism of the finite-type carrier--special-linear isomorphism is
the canonical composite obtained from the quotient-coordinate isomorphism. -/
@[simp]
theorem finiteTypeSpecializationSpecialLinearIso_hom_hom :
    (finiteTypeSpecializationSpecialLinearIso r k).hom.hom =
      (eqToIso (finiteTypeSpecialization_obj r k) ≪≫
        baseChangeCoordinateSpecialLinearIso r k ≪≫
        eqToIso (SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj k (r + 1)).symm).hom := by
  simp only [finiteTypeSpecializationSpecialLinearIso, ObjectProperty.isoMk_hom,
    ObjectProperty.homMk_hom]

/-- **The full-weight type `A_r` carrier is reductive over every algebraically closed field.**

The statement is valid in arbitrary characteristic. It transports the reductivity of
`SL_{r+1}` across the scheme-theoretic identification of the explicit carrier with `SL_{r+1}`. -/
theorem reductiveCommHopfAlgProperty_finiteTypeSpecialization :
    reductiveCommHopfAlgProperty k (finiteTypeSpecialization r k) :=
  (reductiveCommHopfAlgProperty k).prop_of_iso
    (finiteTypeSpecializationSpecialLinearIso r k).symm
    (SpecialLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k (r + 1))

end

end TauCeti.SlStd
