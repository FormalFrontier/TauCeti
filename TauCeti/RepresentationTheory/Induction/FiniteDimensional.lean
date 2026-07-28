/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Finite-dimensional induced representations

This file constructs the finite-dimensional representation induced from a finite-index subgroup.
The main input is a linear equivalence between coinduction and a product indexed by right cosets.
Composing it with Mathlib's finite-index isomorphism from induction to coinduction gives the
dimension formula
`finrank k (Ind_S^G A) = S.index * finrank k A`.
Induction on finite-dimensional representations is packaged both objectwise, as `indFDRep`, and
functorially, as `indFDRepFunctor`, the latter naturally isomorphic to `Rep.indFunctor` under the
forgetful functor to `Rep k G`.

## References

This implements the first item of Layer 2, “Induction preserves finite-dimensionality, via an
explicit coset model”, in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

namespace Rep

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G}

/-- The element of `S` carrying the chosen representative of the right coset of `g` to `g`. -/
noncomputable def rightCosetFactor (g : G) : S :=
  ⟨g * (Quotient.out (Quotient.mk'' g :
      Quotient (QuotientGroup.rightRel S)))⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.eq''.mp (Quotient.out_eq' (Quotient.mk'' g)))⟩

/-- Left multiplication by an element of `S` does not change a right coset. -/
@[simp]
theorem rightCoset_mk_mul (s : S) (g : G) :
    Quotient.mk'' ((s : G) * g) =
      (Quotient.mk'' g : Quotient (QuotientGroup.rightRel S)) :=
  Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by simp))

/-- The right-coset factor is equivariant under left multiplication by `S`. -/
@[simp]
theorem rightCosetFactor_mul (s : S) (g : G) :
    rightCosetFactor (S := S) ((s : G) * g) = s * rightCosetFactor (S := S) g := by
  ext
  simp [rightCosetFactor, mul_assoc]

/-- The right-coset factor carries the chosen representative back to the original element. -/
@[simp]
theorem rightCosetFactor_mul_out (g : G) :
    (rightCosetFactor (S := S) g : G) *
        Quotient.out (Quotient.mk'' g :
          Quotient (QuotientGroup.rightRel S)) = g := by
  simp [rightCosetFactor]

/-- The right-coset factor of a chosen representative is trivial. -/
@[simp]
theorem rightCosetFactor_out (q : Quotient (QuotientGroup.rightRel S)) :
    rightCosetFactor (S := S) q.out = 1 := by
  ext
  simp [rightCosetFactor]

/-- Coinduction from a subgroup is linearly equivalent to a product of copies of the original
representation indexed by the right cosets. The forward map evaluates an equivariant function at
the chosen representative of each right coset. -/
noncomputable def coindSubtypeEquivPi (A : Rep.{u} k S) :
    Rep.coind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) where
  toFun f q := f.1 q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x :=
    ⟨fun g ↦ A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)),
      fun s g ↦ by
        -- Expose the function carried by `coindV` so the two coset rewrites match syntactically.
        change A.ρ (rightCosetFactor (S := S) ((s : G) * g))
          (x (Quotient.mk'' ((s : G) * g))) =
            A.ρ s (A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)))
        rw [rightCoset_mk_mul, rightCosetFactor_mul, ← Module.End.mul_apply, ← map_mul]⟩
  left_inv f := by
    ext g
    have h := f.2 (rightCosetFactor (S := S) g)
      (Quotient.out (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel S)))
    -- Expose `S.subtype` so the representative reconstruction lemma rewrites its argument.
    change f.1 ((rightCosetFactor (S := S) g : G) *
      Quotient.out (Quotient.mk'' g :
        Quotient (QuotientGroup.rightRel S))) =
        A.ρ (rightCosetFactor (S := S) g)
          (f.1 (Quotient.out (Quotient.mk'' g :
            Quotient (QuotientGroup.rightRel S)))) at h
    simpa only [rightCosetFactor_mul_out] using h.symm
  right_inv x := by
    funext q
    -- Expose the inverse's underlying function before normalizing its chosen representative.
    change A.ρ (rightCosetFactor (S := S) q.out) (x (Quotient.mk'' q.out)) = x q
    rw [rightCosetFactor_out]
    simp

/-- The coset model evaluates a coinduced function at the chosen representative. -/
@[simp]
theorem coindSubtypeEquivPi_apply (A : Rep.{u} k S)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    coindSubtypeEquivPi A f q = f.1 q.out := by
  rw [coindSubtypeEquivPi]
  rfl

/-- The inverse coset model extends a value from each representative by `S`-equivariance. -/
@[simp]
theorem coindSubtypeEquivPi_symm_apply (A : Rep.{u} k S)
    (x : Quotient (QuotientGroup.rightRel S) → A) (g : G) :
    ((coindSubtypeEquivPi A).symm x).1 g =
      A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)) := by
  rw [coindSubtypeEquivPi]
  rfl

/-- The underlying vector space of induction from a finite-index subgroup is a product of copies
of the original representation indexed by the right cosets. -/
noncomputable def indSubtypeEquivPi [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]
    (A : Rep.{u} k S) :
    Rep.ind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) :=
  (((forget₂ (Rep k G) (ModuleCat k)).mapIso (Rep.indCoindIso A)).toLinearEquiv).trans
    (coindSubtypeEquivPi A)

/-- The coset model of induction transports along `Rep.indCoindIso` and then evaluates at the
chosen representative of each right coset. -/
@[simp]
theorem indSubtypeEquivPi_apply [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]
    (A : Rep.{u} k S) (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A x q = ((Rep.indCoindIso A).hom.hom x).1 q.out := by
  rw [indSubtypeEquivPi]
  rfl

/-- The inverse coset model of induction extends by `S`-equivariance and then transports back
along `Rep.indCoindIso`. -/
@[simp]
theorem indSubtypeEquivPi_symm_apply [DecidableRel (QuotientGroup.rightRel S)] [S.FiniteIndex]
    (A : Rep.{u} k S) (x : Quotient (QuotientGroup.rightRel S) → A) :
    (indSubtypeEquivPi A).symm x =
      (Rep.indCoindIso A).inv.hom ((coindSubtypeEquivPi A).symm x) := by
  rw [indSubtypeEquivPi]
  rfl

/-- Induction from a finite-index subgroup preserves finite-dimensionality. -/
noncomputable instance finiteDimensional_ind [S.FiniteIndex] (A : Rep.{u} k S)
    [FiniteDimensional k A] : FiniteDimensional k (Rep.ind S.subtype A) := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  letI := S.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  letI : FiniteDimensional k
      (Quotient (QuotientGroup.rightRel S) → A) := inferInstance
  exact (indSubtypeEquivPi A).symm.finiteDimensional

/-- The dimension of induction from a finite-index subgroup is the index times the original
dimension. -/
theorem finrank_ind [S.FiniteIndex] (A : Rep.{u} k S) [FiniteDimensional k A] :
    Module.finrank k (Rep.ind S.subtype A) = S.index * Module.finrank k A := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  letI := S.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  -- Transfer the computation to the explicit finite product supplied by the coset model.
  rw [LinearEquiv.finrank_eq (indSubtypeEquivPi A), Module.finrank_pi_fintype]
  simp [QuotientGroup.card_quotient_rightRel, Subgroup.index_eq_card]

end Rep

/-- The finite-dimensional representation induced from a finite-index subgroup. -/
noncomputable def indFDRep {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) : FDRep k G := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  -- Register the finite-dimensional structure hidden behind the forgetful object's wrapper.
  letI : FiniteDimensional k A' := by
    change FiniteDimensional k A
    infer_instance
  exact FDRep.of (Rep.ind S.subtype A').ρ

/-- Forgetting finite-dimensionality from `indFDRep` recovers Mathlib's induced
representation. -/
noncomputable def indFDRepForgetIso {k G : Type u} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) :
    (forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A) ≅
      Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A) :=
  Iso.refl _

/-- Induction from a finite-index subgroup, as a functor on finite-dimensional representations.
It acts on objects as `indFDRep`; on intertwiners it is Mathlib's `Rep.indFunctor`, transported
back along the fully faithful forgetful functor `FDRep k G ⥤ Rep k G`. -/
noncomputable def indFDRepFunctor {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] : FDRep k S ⥤ FDRep k G where
  obj A := indFDRep A
  map f := (forget₂ (FDRep k G) (Rep k G)).preimage
    ((Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f))
  map_id _ := (forget₂ (FDRep k G) (Rep k G)).map_injective (by
    rw [Functor.map_preimage, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl)
  map_comp _ _ := (forget₂ (FDRep k G) (Rep k G)).map_injective (by
    rw [Functor.map_preimage, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    rfl)

/-- Under the forgetful functor to `Rep k G`, `indFDRepFunctor` is naturally isomorphic to
Mathlib's induction functor. -/
noncomputable def indFDRepForgetNatIso {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] :
    indFDRepFunctor (k := k) (S := S) ⋙ forget₂ (FDRep k G) (Rep k G) ≅
      forget₂ (FDRep k S) (Rep k S) ⋙ Rep.indFunctor k S.subtype :=
  NatIso.ofComponents (fun A ↦ indFDRepForgetIso A) fun f ↦ by
    simp only [indFDRepFunctor, indFDRepForgetIso, Functor.comp_map, Iso.refl_hom,
      Functor.map_preimage]
    rfl

/-- The dimension of an induced representation is the subgroup index times the dimension of the
original representation. -/
theorem finrank_indFDRep {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) :
    Module.finrank k (indFDRep A) = S.index * Module.finrank k A := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  -- Register the finite-dimensional structure hidden behind the forgetful object's wrapper.
  letI : FiniteDimensional k A' := by
    change FiniteDimensional k A
    infer_instance
  exact Rep.finrank_ind A'

end TauCeti
