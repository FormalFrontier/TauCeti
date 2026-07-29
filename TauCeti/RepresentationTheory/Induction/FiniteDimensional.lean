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

The coset-representative construction below — `rightCosetFactor` together with the two rewriting
lemmas `rightCoset_mk_mul` and `rightCosetFactor_mul` that make it `S`-equivariant, and the proof
plan of building an equivariant function from values at the chosen representatives — is adapted
from the proof of the `PreservesEpimorphisms` instance for `Rep.coindFunctor` in
`Mathlib.RepresentationTheory.Coinduced`, where the same factor appears inline as a local
definition `γ` with auxiliary facts `hmk` and `hγ`. Here it is extracted as standalone API and
used to build the coset equivalence rather than a surjectivity witness.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

namespace Rep

variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}

section CosetModel

variable [CommRing k]

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
noncomputable def coindSubtypeEquivPi (A : Rep.{max u v w} k S) :
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
theorem coindSubtypeEquivPi_apply (A : Rep.{max u v w} k S)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    coindSubtypeEquivPi A f q = f.1 q.out := by
  rw [coindSubtypeEquivPi]
  rfl

/-- The inverse coset model extends a value from each representative by `S`-equivariance. -/
@[simp]
theorem coindSubtypeEquivPi_symm_apply (A : Rep.{max u v w} k S)
    (x : Quotient (QuotientGroup.rightRel S) → A) (g : G) :
    ((coindSubtypeEquivPi A).symm x).1 g =
      A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)) := by
  rw [coindSubtypeEquivPi]
  rfl

/-- In the coset model the `G`-action on coinduction is the coordinate permutation
`q ↦ ⟦q.out * g⟧` followed by the action of the coset factor of `q.out * g`.

Not a `simp` lemma: Mathlib's `@[simps]` on `Representation.coind` rewrites
`(Rep.coind φ A).ρ g` to its underlying `LinearMap`, so this left-hand side is not in `simp`
normal form. Mathlib states its own action lemma `Representation.ind_mk` the same way. -/
theorem coindSubtypeEquivPi_rho_apply (A : Rep.{max u v w} k S) (g : G)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    coindSubtypeEquivPi A ((Rep.coind S.subtype A).ρ g f) q =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (coindSubtypeEquivPi A f (Quotient.mk'' (q.out * g))) := by
  have h := f.2 (rightCosetFactor (S := S) (q.out * g))
    (Quotient.out (Quotient.mk'' (q.out * g) :
      Quotient (QuotientGroup.rightRel S)))
  -- Expose `S.subtype` so the representative reconstruction lemma rewrites its argument.
  change f.1 ((rightCosetFactor (S := S) (q.out * g) : G) *
    Quotient.out (Quotient.mk'' (q.out * g) :
      Quotient (QuotientGroup.rightRel S))) =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (f.1 (Quotient.out (Quotient.mk'' (q.out * g) :
          Quotient (QuotientGroup.rightRel S)))) at h
  rw [coindSubtypeEquivPi_apply, coindSubtypeEquivPi_apply]
  -- The coinduced action evaluates `f` at `q.out * g`.
  change f.1 (q.out * g) = _
  simpa only [rightCosetFactor_mul_out] using h

/-- The underlying vector space of induction from a finite-index subgroup is a product of copies
of the original representation indexed by the right cosets. -/
noncomputable def indSubtypeEquivPi [S.FiniteIndex] (A : Rep.{max u v w} k S) :
    Rep.ind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  exact
    ((forget₂ (Rep k G) (ModuleCat k)).mapIso
      (Rep.indCoindIso.{max u v w, u, v} A)).toLinearEquiv.trans (coindSubtypeEquivPi A)

/-- The coset model of induction transports along `Rep.indCoindIso` and then evaluates at the
chosen representative of each right coset. -/
@[simp]
theorem indSubtypeEquivPi_apply [S.FiniteIndex] (A : Rep.{max u v w} k S)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A x q =
      ((letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
        Rep.indCoindIso.{max u v w, u, v} A).hom.hom x).1 q.out := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  rw [indSubtypeEquivPi]
  rfl

/-- The inverse coset model of induction extends by `S`-equivariance and then transports back
along `Rep.indCoindIso`. -/
@[simp]
theorem indSubtypeEquivPi_symm_apply [S.FiniteIndex] (A : Rep.{max u v w} k S)
    (x : Quotient (QuotientGroup.rightRel S) → A) :
    (indSubtypeEquivPi A).symm x =
      (letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
       Rep.indCoindIso.{max u v w, u, v} A).inv.hom
        ((coindSubtypeEquivPi A).symm x) := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  rw [indSubtypeEquivPi]
  rfl

/-- In the coset model of induction the `G`-action is the coordinate permutation
`q ↦ ⟦q.out * g⟧` followed by the action of the coset factor of `q.out * g`. This is the form a
trace computation over the coset model consumes.

Not a `simp` lemma, for the same reason as `coindSubtypeEquivPi_rho_apply`: `@[simps]` on
`Representation.ind` takes `(Rep.ind φ A).ρ g` out of `simp` normal form. -/
theorem indSubtypeEquivPi_rho_apply [S.FiniteIndex] (A : Rep.{max u v w} k S) (g : G)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A ((Rep.ind S.subtype A).ρ g x) q =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (indSubtypeEquivPi A x (Quotient.mk'' (q.out * g))) := by
  rw [indSubtypeEquivPi_apply, indSubtypeEquivPi_apply, Rep.hom_comm_apply]
  exact coindSubtypeEquivPi_rho_apply A g _ q

end CosetModel

section Dimension

variable [Field k]

/-- Induction from a finite-index subgroup preserves finite-dimensionality. -/
noncomputable instance finiteDimensional_ind [S.FiniteIndex] (A : Rep.{max u v w} k S)
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
@[simp]
theorem finrank_ind [S.FiniteIndex] (A : Rep.{max u v w} k S) [FiniteDimensional k A] :
    Module.finrank k (Rep.ind S.subtype A) = S.index * Module.finrank k A := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  letI := S.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  -- Transfer the computation to the explicit finite product supplied by the coset model.
  rw [LinearEquiv.finrank_eq (indSubtypeEquivPi A), Module.finrank_pi_fintype]
  simp [QuotientGroup.card_quotient_rightRel, Subgroup.index_eq_card]

end Dimension

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

/-- Forgetting finite-dimensionality from `indFDRep` recovers Mathlib's induced representation.
This is the one place where the two objects are identified; everything below about `indFDRep` is
stated and proved through this isomorphism. -/
noncomputable def indFDRepForgetIso {k G : Type u} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) :
    (forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A) ≅
      Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A) :=
  Iso.refl _

/-- Induction from a finite-index subgroup, as a functor on finite-dimensional representations.
It acts on objects as `indFDRep`; on intertwiners it is Mathlib's `Rep.indFunctor`, conjugated by
`indFDRepForgetIso` and transported back along the fully faithful forgetful functor
`FDRep k G ⥤ Rep k G`.

`@[simps obj map]` supplies the projection lemmas `indFDRepFunctor_obj` and
`indFDRepFunctor_map`; they are proved by `rfl`, so this definition is `@[expose]`. -/
@[expose, simps obj map]
noncomputable def indFDRepFunctor {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] : FDRep k S ⥤ FDRep k G where
  obj A := indFDRep A
  map {A B} f := (forget₂ (FDRep k G) (Rep k G)).preimage
    ((indFDRepForgetIso A).hom ≫
      (Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f) ≫
        (indFDRepForgetIso B).inv)
  -- Both laws hold after pushing the forgetful functor through the preimage: the conjugating
  -- copies of `indFDRepForgetIso` then cancel, so neither law unfolds `indFDRep`.
  map_id _ := (forget₂ (FDRep k G) (Rep k G)).map_injective (by
    simp only [Functor.map_preimage, CategoryTheory.Functor.map_id, Rep.indFunctor_obj,
      Category.id_comp, Iso.hom_inv_id])
  map_comp _ _ := (forget₂ (FDRep k G) (Rep k G)).map_injective (by
    simp only [Functor.map_preimage, CategoryTheory.Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc])

/-- Under the forgetful functor to `Rep k G`, `indFDRepFunctor` is naturally isomorphic to
Mathlib's induction functor, componentwise by `indFDRepForgetIso`. -/
noncomputable def indFDRepForgetNatIso {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] :
    indFDRepFunctor (k := k) (S := S) ⋙ forget₂ (FDRep k G) (Rep k G) ≅
      forget₂ (FDRep k S) (Rep k S) ⋙ Rep.indFunctor k S.subtype :=
  NatIso.ofComponents (fun A ↦ indFDRepForgetIso A) fun {A B} f ↦ by
    -- Naturality is the cancellation of the conjugating isomorphisms in `indFDRepFunctor.map`.
    have h := (forget₂ (FDRep k G) (Rep k G)).map_preimage
      ((indFDRepForgetIso A).hom ≫
        (Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f) ≫
          (indFDRepForgetIso B).inv)
    change (forget₂ (FDRep k G) (Rep k G)).map ((forget₂ (FDRep k G) (Rep k G)).preimage
        ((indFDRepForgetIso A).hom ≫
          (Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f) ≫
            (indFDRepForgetIso B).inv)) ≫ (indFDRepForgetIso B).hom =
      (indFDRepForgetIso A).hom ≫
        (Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f)
    rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The dimension of an induced representation is the subgroup index times the dimension of the
original representation. -/
@[simp]
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
