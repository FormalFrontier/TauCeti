/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.ObjectCodeMonoid
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Split `K₀` of an additive category

The split Grothendieck group `TauCeti.SplitK0 C` of an essentially small category `C` with zero
morphisms and binary biproducts -- an additive category, in the intended application -- is the
free abelian group on the isomorphism classes of objects modulo the biproduct relations
`[X ⊞ Y] = [X] + [Y]`. It is the universal recipient of an invariant which is constant on
isomorphism classes and additive on binary biproducts.

A short complex with a splitting is a conflation of *every* exact structure on `C`
(`TauCeti.ExactStructure.conflation_of_splitting`), so the biproduct relations are imposed by
every exact structure. Once exact `K₀` is available, the comparison homomorphism out of split
`K₀` will therefore be an instance of `TauCeti.SplitK0.ofLE`; no such comparison is stated here.

The construction is the presentation engine of
`TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean` applied to the biproduct relations,
so smallness is handled once and for all there and the whole public API below is phrased in terms
of objects of `C`.

The last section identifies `SplitK0 C` with Mathlib's group completion
`Algebra.GrothendieckAddGroup` of the additive monoid of isomorphism classes under `⊞`, built in
`TauCeti/CategoryTheory/GrothendieckGroup/ObjectCodeMonoid.lean`. That monoid structure is carried
by `TauCeti.ObjectCode C` itself, so the identification is an isomorphism of additive groups in
the same small universe.

## Main definitions

* `TauCeti.splitRelation X Y`: the relation `[X ⊞ Y] - [X] - [Y]`, and `TauCeti.splitRelations C`
  the family of all of them.
* `TauCeti.SplitK0 C`: split `K₀`, with class map `TauCeti.SplitK0.of`.
* `TauCeti.SplitK0.ofLE`: the comparison to a presentation imposing more relations.
* `TauCeti.SplitK0.AdditiveInvariant C G`: an isomorphism-invariant, biproduct-additive function
  on objects, and `TauCeti.SplitK0.lift` the homomorphism it induces.
* `TauCeti.SplitK0.map` and `TauCeti.SplitK0.mapEquiv`: functoriality for additive functors and
  invariance under additive equivalences.
* `TauCeti.SplitK0.ofCode`: the class map on the monoid of isomorphism classes of objects.

## Main results

* `TauCeti.SplitK0.of_biprod` and `TauCeti.SplitK0.of_eq_zero_of_isZero`: the defining biproduct
  relation and its consequence for a zero object.
* `TauCeti.SplitK0.liftEquiv`: the universal property. Biproduct-additive invariants with values
  in `G` correspond bijectively to homomorphisms `SplitK0 C →+ G`.
* `TauCeti.SplitK0.grothendieckAddGroupEquiv`: split `K₀` is the group completion of the additive
  monoid of isomorphism classes of objects.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 5,
  where split `K₀` of a symmetric monoidal category is constructed as the group completion of the
  monoid of isomorphism classes, and Section 6 for the presentation by generators and relations.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69, Section 13.1,
  for the split exact structure whose conflations impose exactly these relations.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

section Relations

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- The biproduct relation `[X ⊞ Y] - [X] - [Y]` imposed in split `K₀`. -/
noncomputable def splitRelation (X Y : C) : FreeAbelianGroup (ObjectCode C) :=
  freeOf (X ⊞ Y) - freeOf X - freeOf Y

/-- The defining equation of `TauCeti.splitRelation`. -/
lemma splitRelation_def (X Y : C) :
    splitRelation X Y = freeOf (X ⊞ Y) - freeOf X - freeOf Y := (rfl)

variable (C) in
/-- The family of biproduct relations presenting split `K₀`. -/
def splitRelations : Set (FreeAbelianGroup (ObjectCode C)) :=
  {r | ∃ X Y : C, r = splitRelation X Y}

/-- Membership in the family of biproduct relations. -/
lemma mem_splitRelations_iff {r : FreeAbelianGroup (ObjectCode C)} :
    r ∈ splitRelations C ↔ ∃ X Y : C, r = splitRelation X Y := (Iff.rfl)

lemma splitRelation_mem_splitRelations (X Y : C) : splitRelation X Y ∈ splitRelations C :=
  mem_splitRelations_iff.2 ⟨X, Y, rfl⟩

end Relations

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- The split Grothendieck group of an essentially small category with zero morphisms and binary
biproducts: the free abelian group on the isomorphism classes of objects, modulo
`[X ⊞ Y] = [X] + [Y]`. -/
def SplitK0 : Type w := PresentedK0 (splitRelations C)

noncomputable instance : AddCommGroup (SplitK0 C) :=
  inferInstanceAs (AddCommGroup (PresentedK0 (splitRelations C)))

namespace SplitK0

variable {C}

/-- The class of an object in split `K₀`. -/
noncomputable def of (X : C) : SplitK0 C := PresentedK0.of X

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : SplitK0 C) = of Y :=
  PresentedK0.of_congr e

/-- The comparison from split `K₀` to a presentation imposing every split relation. -/
noncomputable def ofLE {rels : Set (FreeAbelianGroup (ObjectCode C))}
    (h : splitRelations C ⊆ AddSubgroup.closure rels) : SplitK0 C →+ PresentedK0 rels :=
  PresentedK0.ofLE h

@[simp]
lemma ofLE_of {rels : Set (FreeAbelianGroup (ObjectCode C))}
    (h : splitRelations C ⊆ AddSubgroup.closure rels) (X : C) :
    ofLE h (of X) = (PresentedK0.of X : PresentedK0 rels) :=
  PresentedK0.ofLE_of h X

/-- The defining relation of split `K₀`: the class of a biproduct is the sum of the classes. -/
@[simp]
theorem of_biprod (X Y : C) : (of (X ⊞ Y) : SplitK0 C) = of X + of Y := by
  have h : (PresentedK0.mk (splitRelation X Y) : PresentedK0 (splitRelations C)) = 0 :=
    PresentedK0.mk_eq_zero_of_mem (splitRelation_mem_splitRelations X Y)
  rw [splitRelation_def, map_sub, map_sub, PresentedK0.mk_freeOf, PresentedK0.mk_freeOf,
    PresentedK0.mk_freeOf, sub_sub, sub_eq_zero] at h
  exact h

/-- The class of an object which is zero vanishes. -/
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : (of X : SplitK0 C) = 0 := by
  have h := of_biprod X X
  rw [of_congr (isoBiprodZero hX).symm] at h
  exact add_eq_right.1 h.symm

/-- The class of the zero object vanishes. -/
@[simp]
theorem of_zero [HasZeroObject C] : (of (0 : C) : SplitK0 C) = 0 :=
  of_eq_zero_of_isZero (isZero_zero C)

/-- The image of the class map generates split `K₀`. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → SplitK0 C)) = ⊤ :=
  PresentedK0.closure_range_of

/-- Induction on the classes of objects of `C`. -/
@[elab_as_elim]
theorem induction_on {motive : SplitK0 C → Prop} (x : SplitK0 C) (zero : motive 0)
    (of : ∀ X : C, motive (SplitK0.of X)) (add : ∀ a b, motive a → motive b → motive (a + b))
    (neg : ∀ a, motive a → motive (-a)) : motive x :=
  PresentedK0.induction_on x zero of add neg

variable {G : Type*} [AddCommGroup G]

/-- Two homomorphisms out of split `K₀` agreeing on the classes of objects are equal. -/
@[ext]
theorem hom_ext {f g : SplitK0 C →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  PresentedK0.hom_ext h

variable (C) in
/-- An additive invariant for split `K₀`: a function on objects of `C`, constant on isomorphism
classes and additive on binary biproducts. These are exactly the data that factor through
`TauCeti.SplitK0 C`; see `TauCeti.SplitK0.liftEquiv`. -/
@[ext]
structure AdditiveInvariant (G : Type*) [AddCommGroup G] where
  /-- The value of the invariant on an object. -/
  obj : C → G
  /-- Isomorphic objects receive equal values. -/
  map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y
  /-- The value on a biproduct is the sum of the values. -/
  map_biprod : ∀ X Y : C, obj (X ⊞ Y) = obj X + obj Y

private noncomputable def AdditiveInvariant.toPresented (a : AdditiveInvariant C G) :
    PresentedK0.AdditiveInvariant (splitRelations C) G where
  obj := a.obj
  map_iso := a.map_iso
  map_rel := by
    rintro _ ⟨X, Y, rfl⟩
    rw [splitRelation_def, map_sub, map_sub, freeLift_freeOf a.map_iso,
      freeLift_freeOf a.map_iso, freeLift_freeOf a.map_iso, a.map_biprod]
    abel

@[simp] private lemma AdditiveInvariant.toPresented_obj (a : AdditiveInvariant C G) :
    a.toPresented.obj = a.obj :=
  (rfl)

/-- The homomorphism out of split `K₀` induced by a biproduct-additive invariant. -/
noncomputable def lift (a : AdditiveInvariant C G) : SplitK0 C →+ G :=
  PresentedK0.lift a.toPresented

@[simp]
lemma lift_of (a : AdditiveInvariant C G) (X : C) : lift a (of X) = a.obj X :=
  PresentedK0.lift_of a.toPresented X

/-- Any homomorphism agreeing with an additive invariant on object classes is its induced lift. -/
theorem lift_unique (a : AdditiveInvariant C G) (f : SplitK0 C →+ G)
    (hf : ∀ X : C, f (of X) = a.obj X) : f = lift a :=
  hom_ext fun X => by rw [hf, lift_of]

/-- The universal property of split `K₀`: biproduct-additive invariants with values in `G`
correspond bijectively to additive homomorphisms `SplitK0 C →+ G`. -/
noncomputable def liftEquiv : AdditiveInvariant C G ≃ (SplitK0 C →+ G) where
  toFun := lift
  invFun f :=
    { obj := fun X => f (of X)
      map_iso := fun _ _ e => by rw [of_congr e]
      map_biprod := fun X Y => by rw [of_biprod, map_add] }
  left_inv a := by ext X; exact lift_of a X
  right_inv f := (lift_unique _ f fun _ => rfl).symm

@[simp]
lemma liftEquiv_apply (a : AdditiveInvariant C G) : liftEquiv a = lift a := (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (f : SplitK0 C →+ G) (X : C) :
    ((liftEquiv (C := C) (G := G)).symm f).obj X = f (of X) := (rfl)

end SplitK0

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]
  [EssentiallySmall.{w'} D]

private lemma freeMap_splitRelation (F : C ⥤ D) [F.Additive] (X Y : C) :
    freeMap F (splitRelation X Y) = splitRelation (F.obj X) (F.obj Y) := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  rw [splitRelation_def, map_sub, map_sub, freeMap_freeOf, freeMap_freeOf, freeMap_freeOf,
    freeOf_congr (F.mapBiprod X Y), splitRelation_def]

private lemma freeMap_splitRelations_mem_closure (F : C ⥤ D) [F.Additive] :
    ∀ r ∈ splitRelations C, freeMap F r ∈ AddSubgroup.closure (splitRelations D) := by
  rintro _ ⟨X, Y, rfl⟩
  rw [freeMap_splitRelation]
  exact AddSubgroup.subset_closure (splitRelation_mem_splitRelations _ _)

namespace SplitK0

/-- The homomorphism of split Grothendieck groups induced by an additive functor. -/
noncomputable def map (F : C ⥤ D) [F.Additive] : SplitK0 C →+ SplitK0 D :=
  PresentedK0.map F (freeMap_splitRelations_mem_closure F)

@[simp]
lemma map_of (F : C ⥤ D) [F.Additive] (X : C) : map F (of X) = of (F.obj X) :=
  PresentedK0.map_of F _ X

/-- `SplitK0.map` sends the identity functor to the identity homomorphism. -/
@[simp]
lemma map_id : map (𝟭 C) = AddMonoidHom.id (SplitK0 C) :=
  PresentedK0.map_id _

/-- `SplitK0.map` sends a composite of additive functors to the composite homomorphism. -/
@[simp]
lemma map_comp {E : Type u''} [Category.{v''} E] [Preadditive E] [HasBinaryBiproducts E]
    [EssentiallySmall.{w''} E] (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] :
    map (F ⋙ G) = (map G).comp (map F) :=
  PresentedK0.map_comp F G _ _ _

/-- Objectwise isomorphic additive functors induce the same map; in particular naturally
isomorphic ones do. -/
lemma map_congr {F G : C ⥤ D} [F.Additive] [G.Additive]
    (h : ∀ X : C, Nonempty (F.obj X ≅ G.obj X)) : map F = map G :=
  PresentedK0.map_congr h _ _

/-- Invariance under additive equivalences. -/
noncomputable def mapEquiv (e : C ≌ D) [e.functor.Additive] : SplitK0 C ≃+ SplitK0 D :=
  PresentedK0.mapEquiv e (freeMap_splitRelations_mem_closure e.functor)
    (freeMap_splitRelations_mem_closure e.inverse)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.Additive] (X : C) :
    mapEquiv e (of X) = of (e.functor.obj X) :=
  PresentedK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.Additive] (Y : D) :
    (mapEquiv e).symm (of Y) = of (e.inverse.obj Y) :=
  PresentedK0.mapEquiv_symm_of e _ _ Y

/-- The homomorphism underlying the equivalence invariance is the functorial map. -/
@[simp]
lemma mapEquiv_toAddMonoidHom (e : C ≌ D) [e.functor.Additive] :
    ((mapEquiv e : SplitK0 C ≃+ SplitK0 D) : SplitK0 C →+ SplitK0 D) = map e.functor :=
  PresentedK0.mapEquiv_toAddMonoidHom e _ _

end SplitK0

end Functoriality

section IsoClasses

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

namespace SplitK0

omit [HasZeroObject C] in
private lemma of_eq_of_objectCode_eq {X Y : C} (h : objectCode X = objectCode Y) :
    (of X : SplitK0 C) = of Y :=
  of_congr (objectCode_eq_objectCode_iff.1 h).some

/-- The class map of split `K₀`, as a homomorphism from the additive monoid of isomorphism
classes of objects. -/
noncomputable def ofCode : ObjectCode C →+ SplitK0 C where
  toFun c := of (Function.surjInv objectCode_surjective c)
  map_zero' := by
    refine (of_eq_of_objectCode_eq (Y := (0 : C)) ?_).trans of_zero
    rw [Function.surjInv_eq objectCode_surjective, objectCode_zero]
  map_add' a b := by
    have h : objectCode (Function.surjInv objectCode_surjective (a + b)) =
        objectCode (Function.surjInv objectCode_surjective a ⊞
          Function.surjInv objectCode_surjective b) := by
      rw [Function.surjInv_eq objectCode_surjective, objectCode_biprod,
        Function.surjInv_eq objectCode_surjective, Function.surjInv_eq objectCode_surjective]
    exact (of_eq_of_objectCode_eq h).trans (of_biprod _ _)

@[simp]
lemma ofCode_objectCode (X : C) : ofCode (objectCode X) = (of X : SplitK0 C) :=
  of_eq_of_objectCode_eq (Function.surjInv_eq objectCode_surjective (objectCode X))

variable (C) in
/-- The invariant sending an object to its isomorphism class, viewed in the group completion of
the monoid of isomorphism classes. -/
noncomputable def grothendieckAddGroupInvariant :
    AdditiveInvariant C (Algebra.GrothendieckAddGroup (ObjectCode C)) where
  obj X := Algebra.GrothendieckAddGroup.of (objectCode X)
  map_iso _ _ e := by rw [objectCode_congr e]
  map_biprod X Y := by rw [objectCode_biprod, map_add]

@[simp]
lemma grothendieckAddGroupInvariant_obj (X : C) :
    (grothendieckAddGroupInvariant C).obj X = Algebra.GrothendieckAddGroup.of (objectCode X) :=
  (rfl)

variable (C) in
/-- Split `K₀` is the group completion of the additive monoid of isomorphism classes of objects
under the binary biproduct. This is Weibel's description of split `K₀`. -/
noncomputable def grothendieckAddGroupEquiv :
    Algebra.GrothendieckAddGroup (ObjectCode C) ≃+ SplitK0 C where
  toFun := Algebra.GrothendieckAddGroup.lift ofCode
  invFun := lift (grothendieckAddGroupInvariant C)
  map_add' := map_add _
  left_inv x := by
    have h : ((lift (grothendieckAddGroupInvariant C)).comp
        (Algebra.GrothendieckAddGroup.lift ofCode)) = AddMonoidHom.id _ :=
      (AddLocalization.addMonoidOf ⊤).epic_of_localizationMap <| AddMonoidHom.ext fun c => by
        obtain ⟨X, rfl⟩ := objectCode_surjective c
        have hX : Algebra.GrothendieckAddGroup.lift ofCode
            (Algebra.GrothendieckAddGroup.of (objectCode X)) = (of X : SplitK0 C) :=
          (AddSubmonoid.LocalizationMap.lift_eq _ _ (objectCode X)).trans (ofCode_objectCode X)
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply]
        rw [hX, lift_of, grothendieckAddGroupInvariant_obj]
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : ((Algebra.GrothendieckAddGroup.lift ofCode).comp
        (lift (grothendieckAddGroupInvariant C))) = AddMonoidHom.id (SplitK0 C) := by
      refine hom_ext fun X => ?_
      rw [AddMonoidHom.comp_apply, lift_of, AddMonoidHom.id_apply,
        grothendieckAddGroupInvariant_obj]
      exact (AddSubmonoid.LocalizationMap.lift_eq _ _ (objectCode X)).trans (ofCode_objectCode X)
    exact DFunLike.congr_fun h x

/-- The group-completion isomorphism sends the class of an isomorphism class to the class of the
object. It is not a `simp` lemma: `Algebra.GrothendieckAddGroup.of` is reducible, so `simp`
rewrites its left-hand side. -/
lemma grothendieckAddGroupEquiv_of_objectCode (X : C) :
    grothendieckAddGroupEquiv C (Algebra.GrothendieckAddGroup.of (objectCode X)) =
      (of X : SplitK0 C) :=
  (AddSubmonoid.LocalizationMap.lift_eq _ _ (objectCode X)).trans (ofCode_objectCode X)

@[simp]
lemma grothendieckAddGroupEquiv_symm_of (X : C) :
    (grothendieckAddGroupEquiv C).symm (of X) =
      Algebra.GrothendieckAddGroup.of (objectCode X) :=
  (grothendieckAddGroupEquiv C).symm_apply_eq.2 (grothendieckAddGroupEquiv_of_objectCode X).symm

end SplitK0

end IsoClasses

end TauCeti
