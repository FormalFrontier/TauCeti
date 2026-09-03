/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup
public import TauCeti.RepresentationTheory.GaloisLattice.ActionField

/-!
# Separable action fields of Galois lattices

The continuous absolute-Galois action on an integral Galois lattice factors through the
automorphism group of the finite normal field `GaloisLatticeCat.actionField`. Over an imperfect
base that field need not itself be separable. This file replaces it by its maximal separable
subextension.

The original action field is purely inseparable over this subextension. Consequently restriction
induces an isomorphism between their automorphism groups: an automorphism of the action field is
uniquely determined on the separable subextension, and every automorphism of the latter extends by
normality. Transporting the lattice action across this isomorphism gives a realization over a
finite Galois extension of the base field.

## Main declarations

* `TauCeti.GaloisLatticeCat.separableActionField`: the maximal separable subextension of the
  finite normal action field.
* `TauCeti.GaloisLatticeCat.actionFieldGalEquivSeparableActionField`: restriction identifies the
  two automorphism groups.
* `TauCeti.GaloisLatticeCat.separableActionFieldRepresentation`: the lattice action by the
  automorphism group of the finite Galois action field.
* `TauCeti.GaloisLatticeCat.separableActionFieldRepresentation_comp_restriction`: pulling this
  action back to the absolute Galois group recovers the original representation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.

This supplies the finite Galois splitting field needed before constructing the semilinear descent
datum on the split coordinate Hopf algebra in Layer 4, "Tori: split and non-split", of the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti.GaloisLatticeCat

universe u

variable {k : Type u} [Field k]

/-- The module structure stored in the bundled representation. -/
noncomputable local instance separableActionFieldStoredModule (M : GaloisLatticeCat k) :
    Module ℤ M.obj :=
  M.obj.hV2

/-- The maximal separable subextension of the finite normal action field of a Galois lattice. -/
noncomputable def separableActionField (M : GaloisLatticeCat k) :
    IntermediateField k (actionField M) :=
  separableClosure k (actionField M)

/-- The separable action field is finite-dimensional over the base field. -/
noncomputable instance instFiniteDimensionalSeparableActionField (M : GaloisLatticeCat k) :
    FiniteDimensional k (separableActionField M) := by
  unfold separableActionField
  infer_instance

/-- The separable action field is a finite Galois extension of the base field. -/
noncomputable instance instIsGaloisSeparableActionField (M : GaloisLatticeCat k) :
    IsGalois k (separableActionField M) := by
  unfold separableActionField
  infer_instance

/-- Restriction from the original action field to its maximal separable subextension. -/
noncomputable def actionFieldGalToSeparableActionField (M : GaloisLatticeCat k) :
    Gal(actionField M/k) →* Gal(separableActionField M/k) :=
  AlgEquiv.restrictNormalHom (separableActionField M)

/-- Restriction identifies the automorphism group of the finite normal action field with that of
its finite Galois separable subextension. This is `separableClosureRestrictEquiv` for the normal
extension `actionField M / k`, forgetting its continuity. -/
noncomputable def actionFieldGalEquivSeparableActionField (M : GaloisLatticeCat k) :
    Gal(actionField M/k) ≃* Gal(separableActionField M/k) :=
  (separableClosureRestrictEquiv k (actionField M)).toMulEquiv

/-- The isomorphism of automorphism groups is restriction to the separable action field. -/
@[simp]
theorem actionFieldGalEquivSeparableActionField_apply (M : GaloisLatticeCat k)
    (sigma : Gal(actionField M/k)) :
    actionFieldGalEquivSeparableActionField M sigma =
      actionFieldGalToSeparableActionField M sigma :=
  separableClosureRestrictEquiv_apply sigma

/-- The automorphism group of the separable action field maps onto the faithful finite quotient
acting on the lattice. -/
noncomputable def separableActionFieldToActionQuotient (M : GaloisLatticeCat k) :
    Gal(separableActionField M/k) →* actionQuotient M :=
  (actionFieldToActionQuotient M).comp
    (actionFieldGalEquivSeparableActionField M).symm.toMonoidHom

/-- The map from the separable action field's automorphism group to the action quotient is
surjective. -/
theorem separableActionFieldToActionQuotient_surjective (M : GaloisLatticeCat k) :
    Function.Surjective (separableActionFieldToActionQuotient M) :=
  (actionFieldToActionQuotient_surjective M).comp
    (actionFieldGalEquivSeparableActionField M).symm.surjective

/-- Restriction of an absolute Galois automorphism to the separable action field, through the
original action field. -/
noncomputable def separableActionFieldRestriction (M : GaloisLatticeCat k) :
    Field.absoluteGaloisGroup k →* Gal(separableActionField M/k) :=
  (actionFieldGalEquivSeparableActionField M).toMonoidHom.comp (actionFieldRestriction M)

/-- Restriction from the absolute Galois group onto the separable action field is surjective. -/
theorem separableActionFieldRestriction_surjective (M : GaloisLatticeCat k) :
    Function.Surjective (separableActionFieldRestriction M) :=
  (actionFieldGalEquivSeparableActionField M).surjective.comp
    (actionFieldRestriction_surjective M)

/-- Restriction to the separable action field followed by the quotient map is the original class
in the faithful finite action quotient. -/
@[simp]
theorem separableActionFieldToActionQuotient_restrict (M : GaloisLatticeCat k)
    (sigma : Field.absoluteGaloisGroup k) :
    separableActionFieldToActionQuotient M (separableActionFieldRestriction M sigma) =
      (sigma : actionQuotient M) := by
  rw [separableActionFieldToActionQuotient, separableActionFieldRestriction]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply, actionFieldToActionQuotient_restrict]

/-- The representation of the finite Galois action field obtained from the original action-field
representation through the restriction isomorphism. -/
noncomputable def separableActionFieldRepresentation (M : GaloisLatticeCat k) :
    Representation ℤ Gal(separableActionField M/k) M.obj :=
  (actionQuotientRepresentation M).comp (separableActionFieldToActionQuotient M)

/-- Restricting an absolute Galois automorphism to the separable action field and then acting on
the lattice recovers the original absolute-Galois action. -/
@[simp]
theorem separableActionFieldRepresentation_restrict_apply (M : GaloisLatticeCat k)
    (sigma : Field.absoluteGaloisGroup k) (x : M.obj) :
    separableActionFieldRepresentation M (separableActionFieldRestriction M sigma) x =
      M.obj.ρ sigma x := by
  rw [separableActionFieldRepresentation]
  -- Expose composition of the bundled representation before applying the pointwise quotient API.
  change actionQuotientRepresentation M
      (separableActionFieldToActionQuotient M (separableActionFieldRestriction M sigma)) x = _
  rw [separableActionFieldToActionQuotient_restrict, actionQuotientRepresentation_mk_apply]

/-- The original absolute-Galois representation is the pullback of the representation over the
finite Galois separable action field. -/
theorem separableActionFieldRepresentation_comp_restriction (M : GaloisLatticeCat k) :
    (separableActionFieldRepresentation M).comp (separableActionFieldRestriction M) =
      M.obj.ρ := by
  ext sigma x
  exact separableActionFieldRepresentation_restrict_apply M sigma x

/-- An automorphism of the separable action field acts trivially exactly when it maps to the
identity in the faithful finite action quotient. -/
theorem separableActionFieldRepresentation_ker (M : GaloisLatticeCat k) :
    (separableActionFieldRepresentation M).ker =
      (separableActionFieldToActionQuotient M).ker := by
  rw [separableActionFieldRepresentation]
  exact MonoidHom.ker_comp_of_injective (separableActionFieldToActionQuotient M)
    (actionQuotientRepresentation M) (actionQuotientRepresentation_injective M)

end TauCeti.GaloisLatticeCat
