/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Presentation
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Split `K₀` of an additive category

The split Grothendieck group `TauCeti.SplitK0 C` of an essentially small additive category `C` is
the free abelian group on the isomorphism classes of objects modulo the biproduct relations
`[X ⊞ Y] = [X] + [Y]`. It is the universal recipient of an invariant which is constant on
isomorphism classes and additive on binary biproducts. It is universal among the categorical
Grothendieck groups of `C`: every other one is a quotient of it, since any exact structure imposes
at least these relations because a biproduct short complex is a conflation of every exact
structure.

The construction is the presentation engine of
`TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean` applied to the biproduct relations,
so smallness is handled once and for all there and the whole public API below is phrased in terms
of objects of `C`.

The last section identifies `SplitK0 C` with Mathlib's group completion
`Algebra.GrothendieckAddGroup` of the additive monoid of isomorphism classes under `⊞`. That
monoid structure is put on `TauCeti.ObjectCode C` itself, so the identification is an isomorphism
of additive groups in the same small universe.

## Main definitions

* `TauCeti.splitRelation X Y`: the relation `[X ⊞ Y] - [X] - [Y]`, and `TauCeti.splitRelations C`
  the family of all of them.
* `TauCeti.SplitK0 C`: split `K₀`, with class map `TauCeti.SplitK0.of`.
* `TauCeti.SplitK0.AdditiveInvariant C G`: an isomorphism-invariant, biproduct-additive function
  on objects, and `TauCeti.SplitK0.lift` the homomorphism it induces.
* `TauCeti.SplitK0.map` and `TauCeti.SplitK0.mapEquiv`: functoriality for additive functors and
  invariance under additive equivalences.
* the `AddCommMonoid (TauCeti.ObjectCode C)` instance: the monoid of isomorphism classes of
  objects under the binary biproduct, with class map `TauCeti.SplitK0.ofCode`.

## Main results

* `TauCeti.SplitK0.of_biprod` and `TauCeti.SplitK0.of_zero`: the defining biproduct relation and
  its consequence for the zero object.
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

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- The biproduct relation `[X ⊞ Y] - [X] - [Y]` imposed in split `K₀`. -/
noncomputable def splitRelation (X Y : C) : FreeAbelianGroup (ObjectCode C) :=
  freeOf (X ⊞ Y) - freeOf X - freeOf Y

variable (C) in
/-- The family of biproduct relations presenting split `K₀`. -/
def splitRelations : Set (FreeAbelianGroup (ObjectCode C)) :=
  {r | ∃ X Y : C, r = splitRelation X Y}

lemma splitRelation_mem_splitRelations (X Y : C) : splitRelation X Y ∈ splitRelations C :=
  ⟨X, Y, rfl⟩

end Relations

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- The split Grothendieck group of an essentially small additive category: the free abelian
group on the isomorphism classes of objects, modulo `[X ⊞ Y] = [X] + [Y]`. -/
def SplitK0 : Type w := PresentedK0 (splitRelations C)

noncomputable instance : AddCommGroup (SplitK0 C) :=
  inferInstanceAs (AddCommGroup (PresentedK0 (splitRelations C)))

namespace SplitK0

variable {C}

/-- The class of an object in split `K₀`. -/
noncomputable def of (X : C) : SplitK0 C := PresentedK0.of X

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : SplitK0 C) = of Y :=
  PresentedK0.of_congr e

/-- The defining relation of split `K₀`: the class of a biproduct is the sum of the classes. -/
@[simp]
theorem of_biprod (X Y : C) : (of (X ⊞ Y) : SplitK0 C) = of X + of Y := by
  have h : (PresentedK0.mk (splitRelation X Y) : PresentedK0 (splitRelations C)) = 0 :=
    PresentedK0.mk_eq_zero_of_mem (splitRelation_mem_splitRelations X Y)
  rw [splitRelation, map_sub, map_sub, PresentedK0.mk_freeOf, PresentedK0.mk_freeOf,
    PresentedK0.mk_freeOf, sub_sub, sub_eq_zero] at h
  exact h

/-- The class of a zero object vanishes. -/
@[simp]
theorem of_zero [HasZeroObject C] : (of (0 : C) : SplitK0 C) = 0 := by
  have h := of_biprod (0 : C) (0 : C)
  rw [of_congr (isoBiprodZero (isZero_zero C)).symm] at h
  exact add_eq_right.1 h.symm

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

/-- A biproduct-additive invariant is an additive invariant for the biproduct relations. -/
noncomputable def AdditiveInvariant.toPresented (a : AdditiveInvariant C G) :
    PresentedK0.AdditiveInvariant (splitRelations C) G where
  obj := a.obj
  map_iso := a.map_iso
  map_rel := by
    rintro _ ⟨X, Y, rfl⟩
    rw [splitRelation, map_sub, map_sub, freeLift_freeOf a.map_iso, freeLift_freeOf a.map_iso,
      freeLift_freeOf a.map_iso, a.map_biprod]
    abel

/-- The homomorphism out of split `K₀` induced by a biproduct-additive invariant. -/
noncomputable def lift (a : AdditiveInvariant C G) : SplitK0 C →+ G :=
  PresentedK0.lift a.toPresented

@[simp]
lemma lift_of (a : AdditiveInvariant C G) (X : C) : lift a (of X) = a.obj X :=
  PresentedK0.lift_of a.toPresented X

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

/-- An additive functor carries the biproduct relation of `X` and `Y` to the biproduct relation of
their images. -/
lemma freeMap_splitRelation (F : C ⥤ D) [F.Additive] (X Y : C) :
    freeMap F (splitRelation X Y) = splitRelation (F.obj X) (F.obj Y) := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  rw [splitRelation, map_sub, map_sub, freeMap_freeOf, freeMap_freeOf, freeMap_freeOf,
    freeOf_congr (F.mapBiprod X Y), splitRelation]

/-- An additive functor carries the biproduct relations into the subgroup they generate in the
target, which is what functoriality of the presentation asks for. -/
lemma freeMap_splitRelations_mem_closure (F : C ⥤ D) [F.Additive] :
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
noncomputable def mapEquiv (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    SplitK0 C ≃+ SplitK0 D :=
  PresentedK0.mapEquiv e (freeMap_splitRelations_mem_closure e.functor)
    (freeMap_splitRelations_mem_closure e.inverse)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] (X : C) :
    mapEquiv e (of X) = of (e.functor.obj X) :=
  PresentedK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] (Y : D) :
    (mapEquiv e).symm (of Y) = of (e.inverse.obj Y) :=
  PresentedK0.mapEquiv_symm_of e _ _ Y

/-- The homomorphism underlying the equivalence invariance is the functorial map. -/
@[simp]
lemma mapEquiv_toAddMonoidHom (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    ((mapEquiv e : SplitK0 C ≃+ SplitK0 D) : SplitK0 C →+ SplitK0 D) = map e.functor :=
  PresentedK0.mapEquiv_toAddMonoidHom e _ _

end SplitK0

end Functoriality

section IsoClasses

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- Isomorphism classes of objects are added by taking the binary biproduct of chosen
representatives. The choice never escapes: `TauCeti.objectCode_biprod` computes the sum on the
codes of actual objects. -/
noncomputable instance : Add (ObjectCode C) :=
  ⟨fun c d => objectCode (objectCodeOut c ⊞ objectCodeOut d)⟩

/-- The class of the zero object is the neutral isomorphism class. -/
noncomputable instance : Zero (ObjectCode C) := ⟨objectCode (0 : C)⟩

omit [HasZeroObject C] in
/-- The code of a binary biproduct is the sum of the object codes. -/
@[simp]
lemma objectCode_biprod (X Y : C) : objectCode (X ⊞ Y) = objectCode X + objectCode Y :=
  (objectCode_congr (biprod.mapIso (objectCodeOutIso X) (objectCodeOutIso Y))).symm

omit [Preadditive C] [HasBinaryBiproducts C] in
@[simp]
lemma objectCode_zeroObject : objectCode (0 : C) = (0 : ObjectCode C) := (rfl)

/-- The isomorphism classes of an essentially small additive category form an additive commutative
monoid under the binary biproduct. -/
noncomputable instance : AddCommMonoid (ObjectCode C) where
  nsmul := nsmulRec
  add_assoc a b c := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    obtain ⟨B, rfl⟩ := objectCode_surjective b
    obtain ⟨D, rfl⟩ := objectCode_surjective c
    rw [← objectCode_biprod, ← objectCode_biprod, ← objectCode_biprod, ← objectCode_biprod]
    exact objectCode_congr (biprod.associator A B D)
  add_comm a b := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    obtain ⟨B, rfl⟩ := objectCode_surjective b
    rw [← objectCode_biprod, ← objectCode_biprod]
    exact objectCode_congr (biprod.braiding A B)
  add_zero a := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    rw [← objectCode_zeroObject, ← objectCode_biprod]
    exact objectCode_congr (isoBiprodZero (isZero_zero C)).symm
  zero_add a := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    rw [← objectCode_zeroObject, ← objectCode_biprod]
    exact objectCode_congr (isoZeroBiprod (isZero_zero C)).symm

namespace SplitK0

/-- The class map of split `K₀`, as a homomorphism from the additive monoid of isomorphism
classes of objects. -/
noncomputable def ofCode : ObjectCode C →+ SplitK0 C where
  toFun c := of (objectCodeOut c)
  map_zero' := by
    rw [← objectCode_zeroObject, of_congr (objectCodeOutIso (0 : C)), of_zero]
  map_add' a b := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    obtain ⟨B, rfl⟩ := objectCode_surjective b
    rw [← objectCode_biprod, of_congr (objectCodeOutIso (A ⊞ B)),
      of_congr (objectCodeOutIso A), of_congr (objectCodeOutIso B), of_biprod]

@[simp]
lemma ofCode_objectCode (X : C) : ofCode (objectCode X) = (of X : SplitK0 C) :=
  of_congr (objectCodeOutIso X)

private lemma grothendieckAddGroup_hom_ext {M : Type w} [AddCommMonoid M] {G : Type*}
    [AddCommGroup G] {f g : Algebra.GrothendieckAddGroup M →+ G}
    (h : ∀ m : M, f (Algebra.GrothendieckAddGroup.of m) =
      g (Algebra.GrothendieckAddGroup.of m)) : f = g :=
  Algebra.GrothendieckAddGroup.lift.symm.injective <| by
    simpa only [Algebra.GrothendieckAddGroup.lift_symm_apply] using AddMonoidHom.ext h

private lemma grothendieckAddGroup_lift_of {M : Type w} [AddCommMonoid M] {G : Type*}
    [AddCommGroup G] (f : M →+ G) (m : M) :
    Algebra.GrothendieckAddGroup.lift f (Algebra.GrothendieckAddGroup.of m) = f m := by
  simp [Algebra.GrothendieckAddGroup.lift]

variable (C) in
/-- The invariant sending an object to its isomorphism class, viewed in the group completion of
the monoid of isomorphism classes. -/
noncomputable def toGrothendieckAddGroupInvariant :
    AdditiveInvariant C (Algebra.GrothendieckAddGroup (ObjectCode C)) where
  obj X := Algebra.GrothendieckAddGroup.of (objectCode X)
  map_iso _ _ e := by rw [objectCode_congr e]
  map_biprod X Y := by rw [objectCode_biprod, map_add]

variable (C) in
/-- Split `K₀` is the group completion of the additive monoid of isomorphism classes of objects
under the binary biproduct. This is Weibel's description of split `K₀`. -/
noncomputable def grothendieckAddGroupEquiv :
    Algebra.GrothendieckAddGroup (ObjectCode C) ≃+ SplitK0 C where
  toFun := Algebra.GrothendieckAddGroup.lift ofCode
  invFun := lift (toGrothendieckAddGroupInvariant C)
  map_add' := map_add _
  left_inv x := by
    have h : ((lift (toGrothendieckAddGroupInvariant C)).comp
        (Algebra.GrothendieckAddGroup.lift ofCode)) = AddMonoidHom.id _ := by
      refine grothendieckAddGroup_hom_ext fun c => ?_
      obtain ⟨X, rfl⟩ := objectCode_surjective c
      rw [AddMonoidHom.comp_apply, grothendieckAddGroup_lift_of, ofCode_objectCode,
        AddMonoidHom.id_apply, lift_of]
      rfl
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : ((Algebra.GrothendieckAddGroup.lift ofCode).comp
        (lift (toGrothendieckAddGroupInvariant C))) = AddMonoidHom.id (SplitK0 C) := by
      refine hom_ext fun X => ?_
      rw [AddMonoidHom.comp_apply, lift_of, AddMonoidHom.id_apply]
      exact (grothendieckAddGroup_lift_of ofCode (objectCode X)).trans (ofCode_objectCode X)
    exact DFunLike.congr_fun h x

/-- The group-completion isomorphism sends the class of an isomorphism class to the class of the
object. It is not a `simp` lemma: `Algebra.GrothendieckAddGroup.of` is reducible, so `simp`
rewrites its left-hand side. -/
lemma grothendieckAddGroupEquiv_of (X : C) :
    grothendieckAddGroupEquiv C (Algebra.GrothendieckAddGroup.of (objectCode X)) =
      (of X : SplitK0 C) :=
  (grothendieckAddGroup_lift_of ofCode (objectCode X)).trans (ofCode_objectCode X)

@[simp]
lemma grothendieckAddGroupEquiv_symm_of (X : C) :
    (grothendieckAddGroupEquiv C).symm (of X) =
      Algebra.GrothendieckAddGroup.of (objectCode X) :=
  lift_of (toGrothendieckAddGroupInvariant C) X

end SplitK0

end IsoClasses

end TauCeti
