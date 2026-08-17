/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.GaloisLattice.FiniteQuotient

/-!
# Finite action fields of Galois lattices

The continuous action of the absolute Galois group on a Galois lattice factors through a finite
quotient. This file realizes that factorization over an actual finite normal subextension of the
chosen algebraic closure. Its fixing subgroup lies in the kernel of the lattice action, so the
action descends to the automorphism group of the subextension.

Over an imperfect base the chosen normal extension need not be separable, and no Galois claim is
made. Passing to a finite separable splitting field is a later refinement. The finite normal field
constructed here is the field-theoretic bridge needed before descending a split torus from the
algebraic closure, in Layer 4, "Tori: split and non-split", of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.GaloisLatticeCat.actionField`: a finite normal subextension whose fixing subgroup acts
  trivially on the lattice.
* `TauCeti.GaloisLatticeCat.actionFieldToActionQuotient`: the surjective map from the field's
  automorphism group to the finite quotient acting faithfully on the lattice.
* `TauCeti.GaloisLatticeCat.actionFieldRepresentation`: the resulting action of the finite
  automorphism group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

namespace TauCeti.GaloisLatticeCat

universe u

variable {k : Type u} [Field k]

/-- The module structure stored in the bundled representation. -/
noncomputable local instance actionFieldStoredModule (M : GaloisLatticeCat k) : Module ℤ M.obj :=
  M.obj.hV2

/-- A finite normal subextension of the algebraic closure through whose automorphism group the
action on a Galois lattice factors. -/
noncomputable def actionField (M : GaloisLatticeCat k) :
    IntermediateField k (AlgebraicClosure k) :=
  (Field.absoluteGaloisGroup.exists_finiteDimensional_normal_fixingSubgroup_le
    M.obj.ρ.ker (isOpen_ker_ρ M)).choose

/-- The action field is finite-dimensional over the base field. -/
noncomputable instance instFiniteDimensionalActionField (M : GaloisLatticeCat k) :
    FiniteDimensional k (actionField M) :=
  (Field.absoluteGaloisGroup.exists_finiteDimensional_normal_fixingSubgroup_le
    M.obj.ρ.ker (isOpen_ker_ρ M)).choose_spec.1

/-- The action field is normal over the base field. -/
noncomputable instance instNormalActionField (M : GaloisLatticeCat k) :
    Normal k (actionField M) :=
  (Field.absoluteGaloisGroup.exists_finiteDimensional_normal_fixingSubgroup_le
    M.obj.ρ.ker (isOpen_ker_ρ M)).choose_spec.2.1

/-- Every absolute Galois automorphism fixing the action field acts trivially on the lattice. -/
theorem actionField_fixingSubgroup_le_ker (M : GaloisLatticeCat k) :
    (actionField M).fixingSubgroup ≤ M.obj.ρ.ker :=
  (Field.absoluteGaloisGroup.exists_finiteDimensional_normal_fixingSubgroup_le
    M.obj.ρ.ker (isOpen_ker_ρ M)).choose_spec.2.2

/-- Restriction of an absolute Galois automorphism to the action field. -/
noncomputable def actionFieldRestriction (M : GaloisLatticeCat k) :
    Field.absoluteGaloisGroup k →* Gal(actionField M / k) := by
  -- `absoluteGaloisGroup` is a named copy of the automorphism group of the algebraic closure.
  change Gal(AlgebraicClosure k / k) →* Gal(actionField M / k)
  exact AlgEquiv.restrictNormalHom (actionField M)

/-- Restriction to the action field is surjective. -/
theorem actionFieldRestriction_surjective (M : GaloisLatticeCat k) :
    Function.Surjective (actionFieldRestriction M) := by
  -- Expose that same type synonym to apply Mathlib's restriction theorem.
  change Function.Surjective (AlgEquiv.restrictNormalHom (actionField M))
  exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure k)

/-- The kernel of restriction to the action field acts trivially on the lattice. -/
theorem actionFieldRestriction_ker_le (M : GaloisLatticeCat k) :
    (actionFieldRestriction M).ker ≤ M.obj.ρ.ker := by
  intro σ hσ
  apply actionField_fixingSubgroup_le_ker M
  rw [← (actionField M).restrictNormalHom_ker]
  exact hσ

/-- The quotient of the absolute Galois group by the fixing subgroup of the action field is its
automorphism group. -/
noncomputable def absoluteQuotientEquivGalActionField (M : GaloisLatticeCat k) :
    Field.absoluteGaloisGroup k ⧸ (actionFieldRestriction M).ker ≃*
      Gal(actionField M / k) :=
  QuotientGroup.liftEquiv (actionFieldRestriction M).ker
    (actionFieldRestriction_surjective M) rfl

/-- The quotient equivalence sends an absolute automorphism to its restriction to the action
field. -/
@[simp]
theorem absoluteQuotientEquivGalActionField_mk_apply (M : GaloisLatticeCat k)
    (σ : Field.absoluteGaloisGroup k) :
    absoluteQuotientEquivGalActionField M
        (σ : Field.absoluteGaloisGroup k ⧸ (actionFieldRestriction M).ker) =
      actionFieldRestriction M σ :=
  by
    rw [absoluteQuotientEquivGalActionField]
    exact QuotientGroup.liftEquiv_mk (N := (actionFieldRestriction M).ker)
      (actionFieldRestriction_surjective M) rfl σ

/-- The automorphism group of the action field maps to the faithful finite quotient acting on the
lattice. -/
noncomputable def actionFieldToActionQuotient (M : GaloisLatticeCat k) :
    Gal(actionField M / k) →* actionQuotient M :=
  (QuotientGroup.lift (actionFieldRestriction M).ker
      (QuotientGroup.mk' M.obj.ρ.ker) (by
        intro σ hσ
        rw [QuotientGroup.ker_mk']
        exact actionFieldRestriction_ker_le M hσ)).comp
    (absoluteQuotientEquivGalActionField M).symm.toMonoidHom

/-- Restriction to the action field followed by the quotient map is the original class in the
action quotient. -/
@[simp]
theorem actionFieldToActionQuotient_restrict (M : GaloisLatticeCat k)
    (σ : Field.absoluteGaloisGroup k) :
    actionFieldToActionQuotient M (actionFieldRestriction M σ) =
      (σ : actionQuotient M) := by
  rw [actionFieldToActionQuotient, MonoidHom.comp_apply]
  have hσ :
      (absoluteQuotientEquivGalActionField M).symm
          (actionFieldRestriction M σ) =
        (σ : Field.absoluteGaloisGroup k ⧸ (actionFieldRestriction M).ker) := by
    apply (absoluteQuotientEquivGalActionField M).injective
    rw [(absoluteQuotientEquivGalActionField M).apply_symm_apply]
    rfl
  simp only [MulEquiv.coe_toMonoidHom, hσ, QuotientGroup.lift_mk]
  rfl

/-- The map from the action field's automorphism group to the action quotient is surjective. -/
theorem actionFieldToActionQuotient_surjective (M : GaloisLatticeCat k) :
    Function.Surjective (actionFieldToActionQuotient M) := by
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective M.obj.ρ.ker q
  exact ⟨actionFieldRestriction M σ,
    actionFieldToActionQuotient_restrict M σ⟩

/-- The representation of the action field's finite automorphism group obtained by descending
the absolute-Galois action. -/
noncomputable def actionFieldRepresentation (M : GaloisLatticeCat k) :
    Representation ℤ Gal(actionField M / k) M.obj :=
  (actionQuotientRepresentation M).comp (actionFieldToActionQuotient M)

/-- Restricting an absolute Galois automorphism to the action field and then acting on the lattice
recovers the original action. -/
@[simp]
theorem actionFieldRepresentation_restrict_apply (M : GaloisLatticeCat k)
    (σ : Field.absoluteGaloisGroup k) (x : M.obj) :
    actionFieldRepresentation M (actionFieldRestriction M σ) x =
      M.obj.ρ σ x := by
  rw [actionFieldRepresentation]
  -- Expose composition of the two bundled representations before applying the pointwise API.
  change actionQuotientRepresentation M
      (actionFieldToActionQuotient M (actionFieldRestriction M σ)) x = M.obj.ρ σ x
  rw [actionFieldToActionQuotient_restrict, actionQuotientRepresentation_mk_apply]

/-- The original absolute-Galois representation is the pullback of the action-field
representation along restriction. -/
theorem actionFieldRepresentation_comp_restriction (M : GaloisLatticeCat k) :
    (actionFieldRepresentation M).comp (actionFieldRestriction M) = M.obj.ρ := by
  ext σ x
  exact actionFieldRepresentation_restrict_apply M σ x

/-- An automorphism of the action field acts trivially on the lattice exactly when it maps to the
identity in the faithful action quotient. -/
theorem actionFieldRepresentation_ker (M : GaloisLatticeCat k) :
    (actionFieldRepresentation M).ker = (actionFieldToActionQuotient M).ker := by
  rw [actionFieldRepresentation]
  exact MonoidHom.ker_comp_of_injective (actionFieldToActionQuotient M)
    (actionQuotientRepresentation M) (actionQuotientRepresentation_injective M)

end TauCeti.GaloisLatticeCat
