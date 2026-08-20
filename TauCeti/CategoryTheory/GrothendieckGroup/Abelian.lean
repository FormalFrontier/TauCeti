/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Exact

/-!
# Grothendieck groups of abelian categories

The Grothendieck group `TauCeti.AbelianK0 C` of an essentially small abelian category is the exact
Grothendieck group for its canonical exact structure. Thus it is the free abelian group on
isomorphism classes of objects, modulo the equations `[Y] = [X] + [Z]` coming from short exact
complexes `X ⟶ Y ⟶ Z`.

This file specializes the exact-`K₀` interface to the language of abelian categories. In
particular, its defining relation and universal property are stated with
`CategoryTheory.ShortComplex.ShortExact`, and an additive functor induces a map when it preserves
finite limits and finite colimits. Equivalences which are additive induce additive equivalences of
Grothendieck groups.

## Main definitions

* `TauCeti.AbelianK0 C`: the Grothendieck group of an essentially small abelian category.
* `TauCeti.AbelianK0.AdditiveInvariant C G`: an isomorphism-invariant function on objects which is
  additive on short exact complexes.
* `TauCeti.AbelianK0.map` and `TauCeti.AbelianK0.mapEquiv`: functoriality for exact additive
  functors and invariance under additive equivalences.

## Main results

* `TauCeti.AbelianK0.of_shortExact`: the defining short-exact-sequence relation.
* `TauCeti.AbelianK0.liftEquiv`: the universal property for short-exact additive invariants.
* `TauCeti.AbelianK0.fromSplit`: the canonical surjection from split `K₀`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 6.1.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The Grothendieck group of an essentially small abelian category. It is exact `K₀` for the
canonical exact structure, whose conflations are precisely the short exact complexes. -/
noncomputable def AbelianK0 : Type w := ExactK0 (ExactStructure.abelian C)

noncomputable instance : AddCommGroup (AbelianK0 C) :=
  inferInstanceAs (AddCommGroup (ExactK0 (ExactStructure.abelian C)))

namespace AbelianK0

variable {C}

/-- The class of an object in the Grothendieck group of an abelian category. -/
noncomputable def of (X : C) : AbelianK0 C := ExactK0.of X

/-- Isomorphic objects have the same class in abelian `K₀`. -/
lemma of_congr {X Y : C} (e : X ≅ Y) : of X = (of Y : AbelianK0 C) :=
  ExactK0.of_congr e

/-- **The defining relation of abelian `K₀`**: the class of the middle object of a short exact
complex is the sum of the classes of its outer objects. -/
theorem of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (of S.X₂ : AbelianK0 C) = of S.X₁ + of S.X₃ :=
  ExactK0.of_conflation ((ExactStructure.abelian_conflation S).2 hS)

/-- The defining relation of abelian `K₀`, stated for a short exact complex presented by its two
maps. -/
theorem of_eq_add_of_shortExact {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z} (zero : i ≫ p = 0)
    (hS : (ShortComplex.mk i p zero).ShortExact) :
    (of Y : AbelianK0 C) = of X + of Z :=
  of_shortExact hS

/-- The class of the first object in a short exact complex is the difference of the classes of
the other two objects. -/
theorem of_eq_sub_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (of S.X₁ : AbelianK0 C) = of S.X₂ - of S.X₃ := by
  rw [of_shortExact hS]
  abel

/-- The class of a biproduct is the sum of the classes. -/
@[simp]
theorem of_biprod (X Z : C) : (of (X ⊞ Z) : AbelianK0 C) = of X + of Z :=
  ExactK0.of_biprod X Z

/-- The class of an object which is zero vanishes. -/
@[simp]
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : (of X : AbelianK0 C) = 0 :=
  ExactK0.of_eq_zero_of_isZero hX

/-- The class of the zero object vanishes. -/
@[simp]
theorem of_zero : (of (0 : C) : AbelianK0 C) = 0 :=
  ExactK0.of_zero

/-- The classes of objects generate abelian `K₀`. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → AbelianK0 C)) = ⊤ :=
  ExactK0.closure_range_of

/-- Induction on the classes of objects of an abelian category. -/
@[elab_as_elim]
theorem induction_on {motive : AbelianK0 C → Prop} (x : AbelianK0 C) (zero : motive 0)
    (of : ∀ X : C, motive (AbelianK0.of X))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (neg : ∀ a, motive a → motive (-a)) : motive x :=
  ExactK0.induction_on x zero of add neg

variable {G : Type*} [AddCommGroup G]

/-- Two homomorphisms out of abelian `K₀` which agree on object classes are equal. -/
@[ext]
theorem hom_ext {f g : AbelianK0 C →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  ExactK0.hom_ext h

variable (C) in
/-- An additive invariant of an abelian category: an isomorphism-invariant function on objects
whose value on the middle object of a short exact complex is the sum of its values on the outer
objects. These are precisely the functions which factor through `TauCeti.AbelianK0 C`. -/
@[ext]
structure AdditiveInvariant (G : Type*) [AddCommGroup G] where
  /-- The value of the invariant on an object. -/
  obj : C → G
  /-- Isomorphic objects receive equal values. -/
  map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y
  /-- The value on the middle object of a short exact complex is the sum of the outer values. -/
  map_shortExact : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → obj S.X₂ = obj S.X₁ + obj S.X₃

private def AdditiveInvariant.toExact (a : AdditiveInvariant C G) :
    ExactK0.AdditiveInvariant (ExactStructure.abelian C) G where
  obj := a.obj
  map_iso := a.map_iso
  map_conflation := fun {S} hS ↦
    a.map_shortExact ((ExactStructure.abelian_conflation S).1 hS)

/-- The homomorphism out of abelian `K₀` induced by an additive invariant. -/
noncomputable def lift (a : AdditiveInvariant C G) : AbelianK0 C →+ G :=
  ExactK0.lift a.toExact

@[simp]
lemma lift_of (a : AdditiveInvariant C G) (X : C) : lift a (of X) = a.obj X :=
  ExactK0.lift_of a.toExact X

/-- A homomorphism agreeing with an additive invariant on object classes is its induced lift. -/
theorem lift_unique (a : AdditiveInvariant C G) (f : AbelianK0 C →+ G)
    (hf : ∀ X : C, f (of X) = a.obj X) : f = lift a :=
  hom_ext fun X ↦ by rw [hf, lift_of]

/-- **The universal property of abelian `K₀`**: short-exact additive invariants with values in
`G` correspond bijectively to additive homomorphisms `AbelianK0 C →+ G`. -/
noncomputable def liftEquiv : AdditiveInvariant C G ≃ (AbelianK0 C →+ G) where
  toFun := lift
  invFun f :=
    { obj := fun X ↦ f (of X)
      map_iso := fun _ _ e ↦ by rw [of_congr e]
      map_shortExact := fun _ hS ↦ by rw [of_shortExact hS, map_add] }
  left_inv a := by ext X; exact lift_of a X
  right_inv f := (lift_unique _ f fun _ ↦ rfl).symm

@[simp]
lemma liftEquiv_apply (a : AdditiveInvariant C G) : liftEquiv a = lift a :=
  (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (f : AbelianK0 C →+ G) (X : C) :
    ((liftEquiv (C := C) (G := G)).symm f).obj X = f (of X) :=
  (rfl)

section Functoriality

variable {D : Type u'} [Category.{v'} D] [Abelian D] [EssentiallySmall.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- An exact additive functor between abelian categories induces a homomorphism of their
Grothendieck groups. Here exactness is Mathlib's preservation of finite limits and finite
colimits. -/
noncomputable def map : AbelianK0 C →+ AbelianK0 D :=
  ExactK0.map F (ExactStructure.isConflationExact_abelian F)

@[simp]
lemma map_of (X : C) : map F (of X) = (of (F.obj X) : AbelianK0 D) :=
  ExactK0.map_of F _ X

/-- Any homomorphism sending object classes to the classes of their images is the map induced by
the functor. -/
theorem map_unique (f : AbelianK0 C →+ AbelianK0 D)
    (hf : ∀ X : C, f (of X) = (of (F.obj X) : AbelianK0 D)) : f = map F :=
  hom_ext fun X ↦ by rw [hf, map_of]

/-- The identity functor induces the identity on abelian `K₀`. -/
@[simp]
theorem map_id : map (𝟭 C : C ⥤ C) = AddMonoidHom.id (AbelianK0 C) :=
  hom_ext fun X ↦ by rw [map_of, AddMonoidHom.id_apply, Functor.id_obj]

/-- The map of a composite of exact additive functors is the composite of their maps. -/
theorem map_comp {K : Type u''} [Category.{v''} K] [Abelian K] [EssentiallySmall.{w''} K]
    (H : D ⥤ K) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    map (F ⋙ H) = (map H).comp (map F) :=
  hom_ext fun X ↦ by rw [map_of, AddMonoidHom.comp_apply, map_of, map_of, Functor.comp_obj]

/-- Naturally isomorphic exact additive functors induce the same map. -/
theorem map_congr {F' : C ⥤ D} [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (e : F ≅ F') : map F = map F' :=
  hom_ext fun X ↦ by rw [map_of, map_of, of_congr (e.app X)]

/-- **Equivalence invariance of abelian `K₀`**: an additive equivalence of abelian categories
induces an additive equivalence of their Grothendieck groups. -/
noncomputable def mapEquiv (e : C ≌ D) [e.functor.Additive] : AbelianK0 C ≃+ AbelianK0 D :=
  ExactK0.mapEquiv e (ExactStructure.isConflationExact_abelian e.functor)
    (ExactStructure.isConflationExact_abelian e.inverse)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.Additive] (X : C) :
    mapEquiv e (of X) = (of (e.functor.obj X) : AbelianK0 D) :=
  ExactK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.Additive] (Y : D) :
    (mapEquiv e).symm (of Y) = (of (e.inverse.obj Y) : AbelianK0 C) :=
  ExactK0.mapEquiv_symm_of e _ _ Y

end Functoriality

section Comparison

/-- The canonical comparison from split `K₀` to the Grothendieck group of an abelian category. -/
noncomputable def fromSplit : SplitK0 C →+ AbelianK0 C :=
  ExactK0.fromSplit (ExactStructure.abelian C)

@[simp]
lemma fromSplit_of (X : C) : fromSplit (SplitK0.of X) = (of X : AbelianK0 C) :=
  ExactK0.fromSplit_of X

/-- The comparison from split `K₀` is the unique homomorphism preserving object classes. -/
theorem fromSplit_unique (f : SplitK0 C →+ AbelianK0 C)
    (hf : ∀ X : C, f (SplitK0.of X) = (of X : AbelianK0 C)) : f = fromSplit :=
  SplitK0.hom_ext fun X ↦ by rw [hf, fromSplit_of]

/-- The comparison from split `K₀` to abelian `K₀` is surjective. -/
theorem fromSplit_surjective : Function.Surjective (fromSplit : SplitK0 C →+ AbelianK0 C) :=
  ExactK0.fromSplit_surjective

/-- The comparison from split `K₀` is natural in exact additive functors. -/
theorem map_comp_fromSplit {D : Type u'} [Category.{v'} D] [Abelian D]
    [EssentiallySmall.{w'} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    (map F).comp fromSplit = fromSplit.comp (SplitK0.map F) :=
  SplitK0.hom_ext fun X ↦ by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, fromSplit_of, map_of,
      SplitK0.map_of, fromSplit_of]

end Comparison

end AbelianK0

end TauCeti
