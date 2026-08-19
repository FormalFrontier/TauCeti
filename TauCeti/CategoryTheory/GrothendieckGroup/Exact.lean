/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Equivalence
public import TauCeti.CategoryTheory.Exact.Split
public import TauCeti.CategoryTheory.GrothendieckGroup.Presentation

/-!
# Exact `K₀` of a Quillen exact category

The exact Grothendieck group `TauCeti.ExactK0 E` of an essentially small additive category `C`
equipped with a Quillen exact structure `E` is the free abelian group on the isomorphism classes
of objects modulo the relations `[X₂] = [X₁] + [X₃]`, one for each `E`-conflation
`X₁ ↪ X₂ ↠ X₃`. It is the universal recipient of an invariant which is constant on isomorphism
classes and additive on conflations.

The construction is the presentation engine of
`TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean` applied to the conflation relations,
so the skeleton and shrink choices are made once and for all there, and the whole public API
below is phrased in terms of objects and conflations of `C`.

Exact `K₀` is monotone in the exact structure: an exact structure with more conflations imposes
more relations, and `TauCeti.ExactK0.ofLE` is the resulting surjective comparison. The split
exact structure is the smallest one (`TauCeti.ExactStructure.conflation_of_splitting`), so
`TauCeti.ExactK0.fromSplit` compares its `K₀` with the exact `K₀` of an arbitrary exact structure
on the same category. That source is split `K₀`, not merely a variant of it:
`TauCeti.ExactK0.splitAdditiveInvariant` shows its universal property to be the one presented by
the biproduct relations `[X ⊞ Z] = [X] + [Z]`. Both maps are characterized by their values on
object classes, and both are natural in conflation-exact functors.

## Main definitions

* `TauCeti.conflationRelation S`: the relation `[X₂] - [X₁] - [X₃]` attached to a short complex,
  and `TauCeti.exactRelations E` the family of those attached to the conflations of `E`.
* `TauCeti.ExactK0 E`: exact `K₀`, with class map `TauCeti.ExactK0.of`.
* `TauCeti.ExactK0.AdditiveInvariant E G`: an isomorphism-invariant, conflation-additive function
  on objects, and `TauCeti.ExactK0.lift` the homomorphism it induces.
* `TauCeti.ExactK0.map` and `TauCeti.ExactK0.mapEquiv`: functoriality for conflation-exact
  functors and invariance under exact equivalences, with `TauCeti.ExactK0.transportEquiv` the
  instance of the latter for a transported exact structure.
* `TauCeti.ExactK0.ofLE` and `TauCeti.ExactK0.fromSplit`: the comparison induced by the identity
  functor towards an exact structure with more conflations, and its instance out of the split
  exact structure.
* `TauCeti.ExactK0.splitAdditiveInvariant`: an isomorphism-invariant, biproduct-additive function
  is an additive invariant for the split exact structure, so the source of
  `TauCeti.ExactK0.fromSplit` carries the universal property of the biproduct presentation of
  split `K₀`.

## Main results

* `TauCeti.ExactK0.of_conflation`: the defining relation, with `TauCeti.ExactK0.of_biprod` and
  `TauCeti.ExactK0.of_eq_zero_of_isZero` its biproduct and zero-object consequences.
* `TauCeti.ExactK0.liftEquiv`: the universal property. Conflation-additive invariants with values
  in `G` correspond bijectively to homomorphisms `ExactK0 E →+ G`.
* `TauCeti.ExactK0.ofLE_unique` and `TauCeti.ExactK0.ofLE_surjective`: the comparison map is the
  unique homomorphism preserving object classes, and it is surjective, so exact `K₀` is a
  quotient of the exact `K₀` of any smaller exact structure.
* `TauCeti.ExactK0.map_comp_ofLE`: naturality of the comparison in a conflation-exact functor.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  where `K₀` of an exact category is presented by the conflation relations and its universal
  property for additive invariants is stated, and Section 6 for the presentation and the
  set-theoretic care taken in the engine consumed here.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69, Section 13.1
  for the split exact structure, the smallest one, whose comparison map is
  `TauCeti.ExactK0.fromSplit`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

section Relations

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [EssentiallySmall.{w} C]

/-- The relation `[X₂] - [X₁] - [X₃]` attached to a short complex. It is imposed in exact `K₀`
exactly for the distinguished conflations. -/
noncomputable def conflationRelation (S : ShortComplex C) : FreeAbelianGroup (ObjectCode C) :=
  freeOf S.X₂ - freeOf S.X₁ - freeOf S.X₃

/-- The defining equation of `TauCeti.conflationRelation`. -/
@[simp]
lemma conflationRelation_def (S : ShortComplex C) :
    conflationRelation S = freeOf S.X₂ - freeOf S.X₁ - freeOf S.X₃ := (rfl)

/-- An additive homomorphism annihilates the relation of a short complex exactly when it is
additive on that complex. This evaluates a conflation relation once and for all, for both the
quotient map presenting exact `K₀` and the free extension of an invariant. -/
lemma map_conflationRelation_eq_zero_iff {G : Type*} [AddCommGroup G]
    (f : FreeAbelianGroup (ObjectCode C) →+ G) (S : ShortComplex C) :
    f (conflationRelation S) = 0 ↔ f (freeOf S.X₂) = f (freeOf S.X₁) + f (freeOf S.X₃) := by
  rw [conflationRelation_def, map_sub, map_sub, sub_sub, sub_eq_zero]

/-- The free map of a functor carries the relation of a short complex to the relation of its
image. -/
lemma freeMap_conflationRelation {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    [EssentiallySmall.{w'} D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) :
    freeMap F (conflationRelation S) = conflationRelation (S.map F) := by
  simp only [conflationRelation_def, map_sub, freeMap_freeOf, ShortComplex.map_X₁,
    ShortComplex.map_X₂, ShortComplex.map_X₃]

end Relations

section ExactRelations

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

/-- The family of conflation relations presenting the exact `K₀` of an exact structure. -/
def exactRelations (E : ExactStructure C) : Set (FreeAbelianGroup (ObjectCode C)) :=
  {r | ∃ S : ShortComplex C, E.Conflation S ∧ r = conflationRelation S}

variable {E E' : ExactStructure C}

/-- Membership in the family of conflation relations. -/
@[simp]
lemma mem_exactRelations_iff {r : FreeAbelianGroup (ObjectCode C)} :
    r ∈ exactRelations E ↔ ∃ S : ShortComplex C, E.Conflation S ∧ r = conflationRelation S :=
  (Iff.rfl)

lemma conflationRelation_mem_exactRelations {S : ShortComplex C} (hS : E.Conflation S) :
    conflationRelation S ∈ exactRelations E :=
  mem_exactRelations_iff.2 ⟨S, hS, rfl⟩

/-- An exact structure with more conflations imposes more relations. -/
lemma exactRelations_mono (h : ∀ S : ShortComplex C, E.Conflation S → E'.Conflation S) :
    exactRelations E ⊆ exactRelations E' := by
  rintro _ ⟨S, hS, rfl⟩
  exact conflationRelation_mem_exactRelations (h S hS)

end ExactRelations

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

/-- The Grothendieck group of a Quillen exact structure `E` on an essentially small additive
category: the free abelian group on the isomorphism classes of objects, modulo
`[X₂] = [X₁] + [X₃]` for every `E`-conflation `X₁ ↪ X₂ ↠ X₃`. -/
def ExactK0 (E : ExactStructure C) : Type w := PresentedK0 (exactRelations E)

instance (E : ExactStructure C) : AddCommGroup (ExactK0 E) :=
  inferInstanceAs (AddCommGroup (PresentedK0 (exactRelations E)))

namespace ExactK0

variable {E E'' : ExactStructure C} {E' : ExactStructure D}

/-- The class of an object in exact `K₀`. -/
noncomputable def of (X : C) : ExactK0 E := PresentedK0.of X

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : ExactK0 E) = of Y :=
  PresentedK0.of_congr e

/-- **The defining relation of exact `K₀`**: the class of the middle term of a conflation is the
sum of the classes of its outer terms. -/
theorem of_conflation {S : ShortComplex C} (hS : E.Conflation S) :
    (of S.X₂ : ExactK0 E) = of S.X₁ + of S.X₃ := by
  have h := (map_conflationRelation_eq_zero_iff (PresentedK0.mk (rels := exactRelations E)) S).1
    (PresentedK0.mk_eq_zero_of_mem (conflationRelation_mem_exactRelations hS))
  rwa [PresentedK0.mk_freeOf, PresentedK0.mk_freeOf, PresentedK0.mk_freeOf] at h

/-- The defining relation of exact `K₀`, stated for a conflation presented by its two maps. -/
theorem of_eq_add_of_conflation {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z} (zero : i ≫ p = 0)
    (hS : E.Conflation (ShortComplex.mk i p zero)) : (of Y : ExactK0 E) = of X + of Z :=
  of_conflation hS

/-- The class of the subobject of a conflation is the difference of the other two classes. -/
theorem of_eq_sub_of_conflation {S : ShortComplex C} (hS : E.Conflation S) :
    (of S.X₁ : ExactK0 E) = of S.X₂ - of S.X₃ := by
  rw [of_conflation hS]
  abel

/-- The class of a biproduct is the sum of the classes: every exact structure contains the
biproduct conflations. -/
@[simp]
theorem of_biprod (X Z : C) : (of (X ⊞ Z) : ExactK0 E) = of X + of Z :=
  of_conflation (E.conflation_biprodShortComplex X Z)

/-- The class of an object which is zero vanishes. -/
@[simp]
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : (of X : ExactK0 E) = 0 := by
  have h := of_biprod (E := E) X X
  rw [of_congr (isoBiprodZero hX).symm] at h
  exact add_eq_right.1 h.symm

/-- The class of the zero object vanishes. -/
@[simp]
theorem of_zero : (of (0 : C) : ExactK0 E) = 0 :=
  of_eq_zero_of_isZero (isZero_zero C)

/-- The image of the class map generates exact `K₀`. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → ExactK0 E)) = ⊤ :=
  PresentedK0.closure_range_of

/-- Induction on the classes of objects of `C`: no skeleton representative is ever mentioned. -/
@[elab_as_elim]
theorem induction_on {motive : ExactK0 E → Prop} (x : ExactK0 E) (zero : motive 0)
    (of : ∀ X : C, motive (ExactK0.of X)) (add : ∀ a b, motive a → motive b → motive (a + b))
    (neg : ∀ a, motive a → motive (-a)) : motive x :=
  PresentedK0.induction_on x zero of add neg

variable {G : Type*} [AddCommGroup G]

/-- Two homomorphisms out of exact `K₀` agreeing on the classes of objects are equal. -/
@[ext]
theorem hom_ext {f g : ExactK0 E →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  PresentedK0.hom_ext h

variable (E) in
/-- An additive invariant for exact `K₀`: a function on objects of `C`, constant on isomorphism
classes and additive on the conflations of `E`. These are exactly the data that factor through
`TauCeti.ExactK0 E`; see `TauCeti.ExactK0.liftEquiv`. -/
@[ext]
structure AdditiveInvariant (G : Type*) [AddCommGroup G] where
  /-- The value of the invariant on an object. -/
  obj : C → G
  /-- Isomorphic objects receive equal values. -/
  map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y
  /-- The value on the middle term of a conflation is the sum of the outer values. -/
  map_conflation : ∀ ⦃S : ShortComplex C⦄, E.Conflation S → obj S.X₂ = obj S.X₁ + obj S.X₃

private noncomputable def AdditiveInvariant.toPresented (a : AdditiveInvariant E G) :
    PresentedK0.AdditiveInvariant (exactRelations E) G where
  obj := a.obj
  map_iso := a.map_iso
  map_rel := by
    rintro _ ⟨S, hS, rfl⟩
    rw [map_conflationRelation_eq_zero_iff, freeLift_freeOf a.map_iso,
      freeLift_freeOf a.map_iso, freeLift_freeOf a.map_iso]
    exact a.map_conflation hS

@[simp] private lemma AdditiveInvariant.toPresented_obj (a : AdditiveInvariant E G) :
    a.toPresented.obj = a.obj :=
  (rfl)

/-- The homomorphism out of exact `K₀` induced by a conflation-additive invariant. -/
noncomputable def lift (a : AdditiveInvariant E G) : ExactK0 E →+ G :=
  PresentedK0.lift a.toPresented

@[simp]
lemma lift_of (a : AdditiveInvariant E G) (X : C) : lift a (of X) = a.obj X :=
  PresentedK0.lift_of a.toPresented X

/-- Any homomorphism agreeing with a conflation-additive invariant on object classes is its
induced lift. -/
theorem lift_unique (a : AdditiveInvariant E G) (f : ExactK0 E →+ G)
    (hf : ∀ X : C, f (of X) = a.obj X) : f = lift a :=
  hom_ext fun X => by rw [hf, lift_of]

/-- **The universal property of exact `K₀`**: conflation-additive invariants with values in `G`
correspond bijectively to additive homomorphisms `ExactK0 E →+ G`. -/
noncomputable def liftEquiv : AdditiveInvariant E G ≃ (ExactK0 E →+ G) where
  toFun := lift
  invFun f :=
    { obj := fun X => f (of X)
      map_iso := fun _ _ e => by rw [of_congr e]
      map_conflation := fun _ hS => by rw [of_conflation hS, map_add] }
  left_inv a := by ext X; exact lift_of a X
  right_inv f := (lift_unique _ f fun _ => rfl).symm

@[simp]
lemma liftEquiv_apply (a : AdditiveInvariant E G) : liftEquiv a = lift a := (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (f : ExactK0 E →+ G) (X : C) :
    ((liftEquiv (E := E) (G := G)).symm f).obj X = f (of X) := (rfl)

section Functoriality

variable (F : C ⥤ D) [F.Additive]

/-- A conflation-exact functor carries every chosen relation of the source into the relations of
the target. -/
theorem mapsTo_exactRelations (hF : E.IsConflationExact E' F) :
    ∀ r ∈ exactRelations E, freeMap F r ∈ AddSubgroup.closure (exactRelations E') := by
  rintro _ ⟨S, hS, rfl⟩
  rw [freeMap_conflationRelation]
  exact AddSubgroup.subset_closure
    (conflationRelation_mem_exactRelations (hF.map_conflation hS))

/-- **Functoriality of exact `K₀`**: a conflation-exact functor induces a homomorphism of exact
Grothendieck groups. -/
noncomputable def map (hF : E.IsConflationExact E' F) : ExactK0 E →+ ExactK0 E' :=
  PresentedK0.map F (mapsTo_exactRelations F hF)

@[simp]
lemma map_of (hF : E.IsConflationExact E' F) (X : C) :
    map F hF (of X) = (of (F.obj X) : ExactK0 E') :=
  PresentedK0.map_of F _ X

/-- Any homomorphism sending object classes to the classes of their images is the induced map. -/
theorem map_unique (hF : E.IsConflationExact E' F) (f : ExactK0 E →+ ExactK0 E')
    (hf : ∀ X : C, f (of X) = (of (F.obj X) : ExactK0 E')) : f = map F hF :=
  hom_ext fun X => by rw [hf, map_of]

variable (E) in
/-- The identity functor induces the identity of exact `K₀`. -/
@[simp]
theorem map_id : map (𝟭 C) ExactStructure.IsConflationExact.id = AddMonoidHom.id (ExactK0 E) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.id_apply, Functor.id_obj]

/-- The induced maps of a composite of conflation-exact functors compose. -/
theorem map_comp {K : Type u''} [Category.{v''} K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] [EssentiallySmall.{w''} K] {E'' : ExactStructure K} (H : D ⥤ K)
    [H.Additive] (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    map (F ⋙ H) (hF.comp hH) = (map H hH).comp (map F hF) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.comp_apply, map_of, map_of, Functor.comp_obj]

/-- Naturally isomorphic conflation-exact functors induce the same map. -/
theorem map_congr {F' : C ⥤ D} [F'.Additive] (e : F ≅ F') (hF : E.IsConflationExact E' F)
    (hF' : E.IsConflationExact E' F') : map F hF = map F' hF' :=
  hom_ext fun X => by rw [map_of, map_of, of_congr (e.app X)]

/-- **Equivalence invariance of exact `K₀`**: an exact equivalence, that is an equivalence whose
two functors are conflation-exact, induces an isomorphism of exact Grothendieck groups. -/
noncomputable def mapEquiv (e : C ≌ D) [e.functor.Additive]
    (hF : E.IsConflationExact E' e.functor) (hG : E'.IsConflationExact E e.inverse) :
    ExactK0 E ≃+ ExactK0 E' :=
  PresentedK0.mapEquiv e (mapsTo_exactRelations _ hF) (mapsTo_exactRelations _ hG)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.Additive] (hF : E.IsConflationExact E' e.functor)
    (hG : E'.IsConflationExact E e.inverse) (X : C) :
    mapEquiv e hF hG (of X) = (of (e.functor.obj X) : ExactK0 E') :=
  PresentedK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.Additive] (hF : E.IsConflationExact E' e.functor)
    (hG : E'.IsConflationExact E e.inverse) (Y : D) :
    (mapEquiv e hF hG).symm (of Y) = (of (e.inverse.obj Y) : ExactK0 E) :=
  PresentedK0.mapEquiv_symm_of e _ _ Y

/-- Transporting an exact structure along an additive equivalence does not change its exact
`K₀`. -/
noncomputable def transportEquiv (E : ExactStructure C) (e : C ≌ D) [e.functor.Additive] :
    ExactK0 E ≃+ ExactK0 (E.transport e) :=
  mapEquiv e (E.isConflationExact_functor_transport e) (E.isConflationExact_inverse_transport e)

@[simp]
lemma transportEquiv_of (E : ExactStructure C) (e : C ≌ D) [e.functor.Additive] (X : C) :
    transportEquiv E e (of X) = (of (e.functor.obj X) : ExactK0 (E.transport e)) :=
  mapEquiv_of e _ _ X

end Functoriality

section Comparison

/-- **The comparison map of two exact structures**: enlarging the class of conflations imposes
more relations, and the identity functor induces a homomorphism of exact Grothendieck groups. -/
noncomputable def ofLE (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S) :
    ExactK0 E →+ ExactK0 E'' :=
  PresentedK0.ofLE fun _ hr => AddSubgroup.subset_closure (exactRelations_mono h hr)

@[simp]
lemma ofLE_of (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S) (X : C) :
    ofLE h (of X) = (of X : ExactK0 E'') :=
  PresentedK0.ofLE_of _ X

/-- **The universal characterization of the comparison map**: it is the unique homomorphism
preserving the classes of objects. -/
theorem ofLE_unique (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S)
    (f : ExactK0 E →+ ExactK0 E'') (hf : ∀ X : C, f (of X) = (of X : ExactK0 E'')) :
    f = ofLE h :=
  hom_ext fun X => by rw [hf, ofLE_of]

/-- The comparison map is surjective: exact `K₀` is a quotient of the exact `K₀` of any exact
structure with fewer conflations. -/
theorem ofLE_surjective (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S) :
    Function.Surjective (ofLE h) := by
  intro x
  induction x using ExactK0.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of X => exact ⟨of X, ofLE_of h X⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | neg a ha =>
    obtain ⟨a', rfl⟩ := ha
    exact ⟨-a', map_neg _ _⟩

/-- The comparison map of an exact structure with itself is the identity. -/
@[simp]
theorem ofLE_refl : ofLE (E := E) (E'' := E) (fun _ hS => hS) = AddMonoidHom.id (ExactK0 E) :=
  hom_ext fun X => by rw [ofLE_of, AddMonoidHom.id_apply]

/-- Comparison maps for successive enlargements of the class of conflations compose. -/
theorem ofLE_comp {E₃ : ExactStructure C}
    (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S)
    (h' : ∀ S : ShortComplex C, E''.Conflation S → E₃.Conflation S) :
    (ofLE h').comp (ofLE h) = ofLE fun S hS => h' S (h S hS) :=
  hom_ext fun X => by rw [AddMonoidHom.comp_apply, ofLE_of, ofLE_of, ofLE_of]

/-- **Naturality of the comparison map** in a functor which is conflation-exact for both pairs of
exact structures. -/
theorem map_comp_ofLE {E₁' E₂' : ExactStructure D}
    (h : ∀ S : ShortComplex C, E.Conflation S → E''.Conflation S)
    (h' : ∀ S : ShortComplex D, E₁'.Conflation S → E₂'.Conflation S) (F : C ⥤ D) [F.Additive]
    (hF : E.IsConflationExact E₁' F) (hF' : E''.IsConflationExact E₂' F) :
    (map F hF').comp (ofLE h) = (ofLE h').comp (map F hF) :=
  hom_ext fun X => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ofLE_of, map_of, map_of, ofLE_of]

/-- **The biproduct presentation of split `K₀`.** A function on objects which is constant on
isomorphism classes and additive on binary biproducts is automatically additive on the
conflations of the split exact structure, because a split short complex is isomorphic to the
biproduct one. With `TauCeti.ExactK0.of_biprod` for the converse direction and
`TauCeti.ExactK0.liftEquiv` for the universal property, this identifies
`ExactK0 (ExactStructure.split C)` with the group presented by the relations
`[X ⊞ Z] = [X] + [Z]`: homomorphisms out of it correspond bijectively to isomorphism-invariant,
biproduct-additive functions on objects. -/
def splitAdditiveInvariant (obj : C → G) (map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y)
    (map_biprod : ∀ X Z : C, obj (X ⊞ Z) = obj X + obj Z) :
    AdditiveInvariant (ExactStructure.split C) G where
  obj := obj
  map_iso := map_iso
  map_conflation _ hS := by
    obtain ⟨s⟩ := (ExactStructure.split_conflation _).mp hS
    rw [map_iso s.isoBinaryBiproduct, map_biprod]

omit [EssentiallySmall.{w} C] in
@[simp]
lemma splitAdditiveInvariant_obj (obj : C → G) (map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y)
    (map_biprod : ∀ X Z : C, obj (X ⊞ Z) = obj X + obj Z) (X : C) :
    (splitAdditiveInvariant obj map_iso map_biprod).obj X = obj X := (rfl)

variable (E) in
/-- **The canonical comparison out of the split exact structure.** Its conflations are the split
short complexes, which are conflations of every exact structure, so the identity functor induces
a surjection from split `K₀` onto the exact `K₀` of any exact structure on the same additive
category. The source is split `K₀` in the sense of the biproduct presentation, by
`TauCeti.ExactK0.splitAdditiveInvariant` and `TauCeti.ExactK0.of_biprod`. -/
noncomputable def fromSplit : ExactK0 (ExactStructure.split C) →+ ExactK0 E :=
  ofLE fun _ hS => E.conflation_of_split_conflation hS

@[simp]
lemma fromSplit_of (X : C) : fromSplit E (of X) = (of X : ExactK0 E) :=
  ofLE_of _ X

/-- The canonical comparison out of split `K₀` is the unique homomorphism preserving the classes
of objects. -/
theorem fromSplit_unique (f : ExactK0 (ExactStructure.split C) →+ ExactK0 E)
    (hf : ∀ X : C, f (of X) = (of X : ExactK0 E)) : f = fromSplit E :=
  ofLE_unique _ f hf

/-- The canonical comparison out of split `K₀` is surjective: the classes of objects generate
exact `K₀`, so the exact `K₀` of any exact structure is a quotient of split `K₀`. -/
theorem fromSplit_surjective : Function.Surjective (fromSplit E) :=
  ofLE_surjective _

/-- The canonical comparison out of split `K₀` is natural in a conflation-exact functor: every
additive functor is conflation-exact for the split exact structures. -/
theorem map_comp_fromSplit (F : C ⥤ D) [F.Additive] (hF : E.IsConflationExact E' F) :
    (map F hF).comp (fromSplit E) =
      (fromSplit E').comp (map F (ExactStructure.isConflationExact_split F)) :=
  map_comp_ofLE _ _ F (ExactStructure.isConflationExact_split F) hF

end Comparison

end ExactK0

end TauCeti
