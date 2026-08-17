/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RingTheory.Finiteness.Small

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

The objectwise construction, its character formula, dimension theorem, and functor on `FDRep`
allow the scalar field and group to live in separate universes. It uses a small model of Mathlib's
induced carrier, compared by `indFDRepForgetEquiv`. The comparison isomorphism and natural
isomorphism into Mathlib's `Rep` category retain a common universe because that category is indexed
by one carrier universe.

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
theorem rightCosetFactor_mul_out (g : G) : (rightCosetFactor (S := S) g : G) *
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
noncomputable def coindSubtypeEquivPi (A : Rep.{w} k S) :
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
theorem coindSubtypeEquivPi_apply (A : Rep.{w} k S)
    (f : Rep.coind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    coindSubtypeEquivPi A f q = f.1 q.out := by
  rw [coindSubtypeEquivPi]
  rfl

/-- The inverse coset model extends a value from each representative by `S`-equivariance. -/
@[simp]
theorem coindSubtypeEquivPi_symm_apply (A : Rep.{w} k S)
    (x : Quotient (QuotientGroup.rightRel S) → A) (g : G) : ((coindSubtypeEquivPi A).symm x).1 g =
      A.ρ (rightCosetFactor (S := S) g) (x (Quotient.mk'' g)) := by
  rw [coindSubtypeEquivPi]
  rfl

/-- In the coset model the `G`-action on coinduction is the coordinate permutation
`q ↦ ⟦q.out * g⟧` followed by the action of the coset factor of `q.out * g`.

Not a `simp` lemma: Mathlib's `@[simps]` on `Representation.coind` rewrites
`(Rep.coind φ A).ρ g` to its underlying `LinearMap`, so this left-hand side is not in `simp`
normal form. Mathlib states its own action lemma `Representation.ind_mk` the same way. -/
theorem coindSubtypeEquivPi_ρ_apply (A : Rep.{w} k S) (g : G)
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
noncomputable def indSubtypeEquivPi [S.FiniteIndex] (A : Rep.{max w u} k S) :
    Rep.ind S.subtype A ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) := by
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  exact
    ((forget₂ (Rep k G) (ModuleCat k)).mapIso
      (Rep.indCoindIso.{w, u, v} A)).toLinearEquiv.trans (coindSubtypeEquivPi A)

/-- The coset model of induction transports along `Rep.indCoindIso` and then evaluates at the
chosen representative of each right coset.

Not a `simp` lemma: its right-hand side names `Rep.indCoindIso`, so rewriting with it replaces
the coset model by the comparison isomorphism it is built from. The intended interface is
`indSubtypeEquivPi_ρ_apply`, which stays inside the coset model. -/
theorem indSubtypeEquivPi_apply [S.FiniteIndex] (A : Rep.{max w u} k S)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A x q =
      ((letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
        Rep.indCoindIso.{w, u, v} A).hom.hom x).1 q.out := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  rw [indSubtypeEquivPi]
  rfl

/-- The inverse coset model of induction extends by `S`-equivariance and then transports back
along `Rep.indCoindIso`.

Not a `simp` lemma, for the same reason as `indSubtypeEquivPi_apply`: it rewrites the coset
model into the comparison isomorphism. -/
theorem indSubtypeEquivPi_symm_apply [S.FiniteIndex] (A : Rep.{max w u} k S)
    (x : Quotient (QuotientGroup.rightRel S) → A) : (indSubtypeEquivPi A).symm x =
      (letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
       Rep.indCoindIso.{w, u, v} A).inv.hom
        ((coindSubtypeEquivPi A).symm x) := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  rw [indSubtypeEquivPi]
  rfl

/-- In the coset model of induction the `G`-action is the coordinate permutation
`q ↦ ⟦q.out * g⟧` followed by the action of the coset factor of `q.out * g`. This is the form a
trace computation over the coset model consumes.

Not a `simp` lemma, for the same reason as `coindSubtypeEquivPi_ρ_apply`: `@[simps]` on
`Representation.ind` takes `(Rep.ind φ A).ρ g` out of `simp` normal form. -/
theorem indSubtypeEquivPi_ρ_apply [S.FiniteIndex] (A : Rep.{max w u} k S) (g : G)
    (x : Rep.ind S.subtype A) (q : Quotient (QuotientGroup.rightRel S)) :
    indSubtypeEquivPi A ((Rep.ind S.subtype A).ρ g x) q =
      A.ρ (rightCosetFactor (S := S) (q.out * g))
        (indSubtypeEquivPi A x (Quotient.mk'' (q.out * g))) := by
  rw [indSubtypeEquivPi_apply, indSubtypeEquivPi_apply, Rep.hom_comm_apply]
  exact coindSubtypeEquivPi_ρ_apply A g _ q

end CosetModel

section Dimension

variable [Field k]

/-- Induction from a finite-index subgroup preserves finite-dimensionality. -/
noncomputable instance finiteDimensional_ind [S.FiniteIndex] (A : Rep.{max w u} k S)
    [FiniteDimensional k A] : FiniteDimensional k (Rep.ind S.subtype A) := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let := S.fintypeQuotientOfFiniteIndex
  let : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  let : FiniteDimensional k
      (Quotient (QuotientGroup.rightRel S) → A) := inferInstance
  exact (indSubtypeEquivPi A).symm.finiteDimensional

/-- The dimension of induction from a finite-index subgroup is the index times the original
dimension. -/
@[simp]
theorem finrank_ind [S.FiniteIndex] (A : Rep.{max w u} k S) [FiniteDimensional k A] :
    Module.finrank k (Rep.ind S.subtype A) = S.index * Module.finrank k A := by
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  let := S.fintypeQuotientOfFiniteIndex
  let : Fintype (Quotient (QuotientGroup.rightRel S)) :=
    QuotientGroup.fintypeQuotientRightRel
  -- Transfer the computation to the explicit finite product supplied by the coset model.
  rw [LinearEquiv.finrank_eq (indSubtypeEquivPi A), Module.finrank_pi_fintype]
  simp [QuotientGroup.card_quotient_rightRel, Subgroup.index_eq_card]

end Dimension

end Rep

/-- Forgetting finite generation keeps the finite-generation instance on the carrier. -/
instance moduleFinite_forgetFDRep {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A)

/-- Forgetting finite-dimensionality does not change the dimension of the carrier. -/
@[simp]
theorem finrank_forgetFDRep {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

/-- Conjugation by `Shrink.linearEquiv` gives an equivariant equivalence from the shrunk model
back to the original representation. -/
private noncomputable def shrinkRepEquiv {k : Type u} {G : Type v} {V : Type w}
    [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [Small.{u} V]
    (ρ : Representation k G V) :
    Representation.Equiv
      ((Shrink.linearEquiv k V).symm.conjRingEquiv.toMonoidHom.comp ρ) ρ := by
  apply Representation.Equiv.mk (Shrink.linearEquiv k V)
  intro g
  ext x
  simp

/-- The small induced object together with its comparison to Mathlib's induced representation. -/
private structure IndSmallModel {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) where
  object : FDRep k G
  equiv : ((forget₂ (FDRep k G) (Rep k G)).obj object).ρ.Equiv
    (Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)).ρ

/-- Construct the small induced object and comparison equivalence with one choice of shrinking
data. -/
private noncomputable def indSmallModel {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) : IndSmallModel A := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  let V := Rep.ind S.subtype A'
  -- The forgotten carrier lies in `u`, so `w := 0` specializes `max w u` to `u`.
  letI : FiniteDimensional k V := Rep.finiteDimensional_ind.{u, v, 0} A'
  letI : Small.{u} V := Module.Finite.small k V
  let ρ := (Shrink.linearEquiv k V).symm.conjRingEquiv.toMonoidHom.comp V.ρ
  exact { object := FDRep.of ρ, equiv := shrinkRepEquiv V.ρ }

/-- The finite-dimensional representation induced from a finite-index subgroup. -/
noncomputable def indFDRep {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) : FDRep k G :=
  (indSmallModel A).object

/-- The small carrier chosen by `indFDRep` is equivariantly linearly equivalent to Mathlib's
possibly universe-large induced representation. -/
noncomputable def indFDRepForgetEquiv {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) :
    ((forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A)).ρ.Equiv
      (Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)).ρ :=
  (indSmallModel A).equiv

/-- Same-universe categorical wrapper around `indFDRepForgetEquiv`: forgetting
finite-dimensionality from `indFDRep` recovers Mathlib's induced representation. -/
noncomputable def indFDRepForgetIso {k G : Type u} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S) :
    (forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A) ≅
      Rep.ind S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A) :=
  Rep.mkIso (indFDRepForgetEquiv A)

/-- The hom of the categorical comparison applies its underlying equivariant equivalence. -/
@[simp]
private theorem indFDRepForgetIso_hom_hom_apply {k G : Type u} [Field k] [Group G]
    {S : Subgroup G} [S.FiniteIndex] (A : FDRep k S)
    (x : (forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A)) :
    (indFDRepForgetIso A).hom.hom x = indFDRepForgetEquiv A x :=
  rfl

/-- `FDRep.forget₂HomLinearEquiv` is inverse to the forgetful functor on morphisms. -/
private theorem forget₂_map_forget₂HomLinearEquiv {R : Type u} {G : Type v}
    [CommRing R] [Monoid G] (X Y : FDRep R G)
    (f : (forget₂ (FDRep R G) (Rep R G)).obj X ⟶
      (forget₂ (FDRep R G) (Rep R G)).obj Y) :
    (forget₂ (FDRep R G) (Rep R G)).map (FDRep.forget₂HomLinearEquiv X Y f) = f :=
  rfl

/-- Induction of an intertwiner of finite-dimensional representations, obtained by conjugating
Mathlib's induced intertwiner by the small-carrier comparison equivalences. -/
noncomputable def indFDRepMap {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] {A B : FDRep k S} (f : A ⟶ B) : indFDRep A ⟶ indFDRep B := by
  let f' := Rep.ofHom
    ((indFDRepForgetEquiv B).symm.toIntertwiningMap.comp
      ((Rep.indMap S.subtype ((forget₂ (FDRep k S) (Rep k S)).map f)).hom.comp
        (indFDRepForgetEquiv A).toIntertwiningMap))
  exact FDRep.forget₂HomLinearEquiv _ _ f'

/-- `indFDRepMap` applies Mathlib's induced intertwiner between the two small-carrier comparison
equivalences. -/
@[simp]
theorem indFDRepMap_apply {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] {A B : FDRep k S} (f : A ⟶ B)
    (x : (forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A)) :
    ((forget₂ (FDRep k G) (Rep k G)).map (indFDRepMap f)).hom x =
      (indFDRepForgetEquiv B).symm
      ((Rep.indMap S.subtype ((forget₂ (FDRep k S) (Rep k S)).map f)).hom
        (indFDRepForgetEquiv A x)) := by
  simp only [indFDRepMap]
  rw [forget₂_map_forget₂HomLinearEquiv]
  simp

/-- Induction of intertwiners preserves identities. -/
theorem indFDRepMap_id {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) : indFDRepMap (𝟙 A) = 𝟙 (indFDRep A) := by
  let A' := (forget₂ (FDRep k S) (Rep k S)).obj A
  have hInd : Rep.indMap S.subtype (𝟙 A') = 𝟙 (Rep.ind S.subtype A') := by
    simpa using (Rep.indFunctor k S.subtype).map_id A'
  apply (forget₂ (FDRep k G) (Rep k G)).map_injective
  apply Rep.hom_ext
  ext x
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  simp [A', hInd]

/-- Induction of intertwiners preserves composition. -/
theorem indFDRepMap_comp {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] {A B C : FDRep k S} (f : A ⟶ B) (g : B ⟶ C) :
    indFDRepMap (f ≫ g) = indFDRepMap f ≫ indFDRepMap g := by
  let f' := (forget₂ (FDRep k S) (Rep k S)).map f
  let g' := (forget₂ (FDRep k S) (Rep k S)).map g
  have hInd : Rep.indMap S.subtype (f' ≫ g') =
      Rep.indMap S.subtype f' ≫ Rep.indMap S.subtype g' := by
    simpa using (Rep.indFunctor k S.subtype).map_comp f' g'
  apply (forget₂ (FDRep k G) (Rep k G)).map_injective
  apply Rep.hom_ext
  ext x
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  simp [hInd, f', g']

/-- Induction from a finite-index subgroup, as a functor on finite-dimensional representations.
It acts on objects as `indFDRep` and on intertwiners as `indFDRepMap`.

`@[simps obj map]` supplies the projection lemmas `indFDRepFunctor_obj` and
`indFDRepFunctor_map`. Both are proved by `rfl`, and the type of the second needs
`indFDRepFunctor.obj A` to reduce to `indFDRep A`, so this definition is `@[expose]`. Exposing it
publishes exactly those two projections: the construction of the morphism map lives in
`indFDRepMap`, which stays opaque behind `indFDRepMap_apply`. -/
@[expose, simps obj map]
noncomputable def indFDRepFunctor {k : Type u} {G : Type v} [Field k] [Group G]
    {S : Subgroup G}
    [S.FiniteIndex] : FDRep k S ⥤ FDRep k G where
  obj A := indFDRep A
  map f := indFDRepMap f
  map_id A := indFDRepMap_id A
  map_comp f g := indFDRepMap_comp f g

/-- Under the forgetful functor to `Rep k G`, `indFDRepFunctor` is naturally isomorphic to
Mathlib's induction functor, componentwise by `indFDRepForgetIso`. -/
noncomputable def indFDRepForgetNatIso {k G : Type u} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] :
    indFDRepFunctor (k := k) (S := S) ⋙ forget₂ (FDRep k G) (Rep k G) ≅
      forget₂ (FDRep k S) (Rep k S) ⋙ Rep.indFunctor k S.subtype :=
  NatIso.ofComponents (fun A ↦ indFDRepForgetIso A) fun {A B} f ↦ by
    change (forget₂ (FDRep k G) (Rep k G)).map (indFDRepMap f) ≫ (indFDRepForgetIso B).hom =
      (indFDRepForgetIso A).hom ≫
        (Rep.indFunctor k S.subtype).map ((forget₂ (FDRep k S) (Rep k S)).map f)
    ext x
    rw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      LinearMap.comp_apply]
    simp only [Representation.IntertwiningMap.toLinearMap_apply]
    rw [indFDRepMap_apply,
      indFDRepForgetIso_hom_hom_apply, indFDRepForgetIso_hom_hom_apply]
    simp

/-- The dimension of an induced representation is the subgroup index times the dimension of the
original representation. -/
@[simp]
theorem finrank_indFDRep {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G}
    [S.FiniteIndex] (A : FDRep k S) :
    Module.finrank k (indFDRep A) = S.index * Module.finrank k A := by
  rw [← finrank_forgetFDRep (indFDRep A),
    LinearEquiv.finrank_eq (indFDRepForgetEquiv A).toLinearEquiv,
    Rep.finrank_ind, finrank_forgetFDRep]

end TauCeti
