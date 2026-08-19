/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulated `K₀` of a pretriangulated category

The triangulated Grothendieck group `TauCeti.TriangulatedK0 C` of an essentially small
pretriangulated category `C` is the free abelian group on the isomorphism classes of objects
modulo the relations `[Y] = [X] + [Z]`, one for each distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. It is the universal recipient of an invariant which is constant on
isomorphism classes and additive on distinguished triangles.

The construction is the presentation engine of
`TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean` applied to the triangle relations,
so the skeleton and shrink choices are made once and for all there, and the whole public API
below is phrased in terms of objects and distinguished triangles of `C`.

Unlike exact `K₀`, triangulated `K₀` sees the shift: the distinguished triangle
`X ⟶ 0 ⟶ X⟦1⟧ ⟶ X⟦1⟧` forces `[X⟦1⟧] = -[X]`, hence `[X⟦n⟧] = (-1)ⁿ[X]` for every integer `n`.
The sign is recorded by `Int.negOnePow`, so that one statement covers negative shifts as well.
The biproduct triangles are distinguished, so the class map is additive on biproducts and
`TauCeti.TriangulatedK0.fromSplit` compares split `K₀` with triangulated `K₀`.

## Main definitions

* `TauCeti.triangleRelation T`: the relation `[T.obj₂] - [T.obj₁] - [T.obj₃]` attached to a
  triangle, and `TauCeti.triangulatedRelations C` the family of those attached to the
  distinguished triangles.
* `TauCeti.TriangulatedK0 C`: triangulated `K₀`, with class map `TauCeti.TriangulatedK0.of`.
* `TauCeti.TriangulatedK0.AdditiveInvariant C G`: an isomorphism-invariant, triangle-additive
  function on objects, and `TauCeti.TriangulatedK0.lift` the homomorphism it induces.
* `TauCeti.TriangulatedK0.map` and `TauCeti.TriangulatedK0.mapEquiv`: functoriality for
  triangulated functors and invariance under triangulated equivalences.
* `TauCeti.TriangulatedK0.fromSplit`: the canonical comparison from split `K₀`.

## Main results

* `TauCeti.TriangulatedK0.of_distTriang`: the defining relation, with
  `TauCeti.TriangulatedK0.of_biprod` and `TauCeti.TriangulatedK0.of_eq_zero_of_isZero` its
  biproduct and zero-object consequences.
* `TauCeti.TriangulatedK0.of_shift_one` and `TauCeti.TriangulatedK0.of_shift`: the class of a
  shift, `[X⟦1⟧] = -[X]` and `[X⟦n⟧] = (-1)ⁿ[X]`.
* `TauCeti.TriangulatedK0.liftEquiv`: the universal property. Triangle-additive invariants with
  values in `G` correspond bijectively to homomorphisms `TriangulatedK0 C →+ G`.
* `TauCeti.TriangulatedK0.fromSplit_surjective` and
  `TauCeti.TriangulatedK0.map_comp_fromSplit`: triangulated `K₀` is a quotient of split `K₀`,
  naturally in a triangulated functor.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise II.9.15, where `K₀` of a triangulated category is presented by the distinguished
  triangles, and Section 6 for the presentation engine consumed here.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe w w' w'' v v' v'' u u' u''

section Relations

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] [EssentiallySmall.{w} C]

/-- The relation `[T.obj₂] - [T.obj₁] - [T.obj₃]` attached to a triangle. It is imposed in
triangulated `K₀` exactly for the distinguished triangles. -/
noncomputable def triangleRelation (T : Triangle C) : FreeAbelianGroup (ObjectCode C) :=
  freeOf T.obj₂ - freeOf T.obj₁ - freeOf T.obj₃

/-- The defining equation of `TauCeti.triangleRelation`. -/
@[simp]
lemma triangleRelation_def (T : Triangle C) :
    triangleRelation T = freeOf T.obj₂ - freeOf T.obj₁ - freeOf T.obj₃ := (rfl)

/-- An additive homomorphism annihilates the relation of a triangle exactly when it is additive
on that triangle. This evaluates a triangle relation once and for all, for both the quotient map
presenting triangulated `K₀` and the free extension of an invariant. -/
lemma map_triangleRelation_eq_zero_iff {G : Type*} [AddCommGroup G]
    (f : FreeAbelianGroup (ObjectCode C) →+ G) (T : Triangle C) :
    f (triangleRelation T) = 0 ↔ f (freeOf T.obj₂) = f (freeOf T.obj₁) + f (freeOf T.obj₃) := by
  rw [triangleRelation_def, map_sub, map_sub, sub_sub, sub_eq_zero]

/-- The free map of a functor commuting with the shift carries the relation of a triangle to the
relation of its image. -/
lemma freeMap_triangleRelation {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
    [EssentiallySmall.{w'} D] (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C) :
    freeMap F (triangleRelation T) = triangleRelation (F.mapTriangle.obj T) := by
  simp only [triangleRelation_def, map_sub, freeMap_freeOf]
  rfl

end Relations

section TriangulatedRelations

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]

/-- The family of triangle relations presenting the triangulated `K₀` of a pretriangulated
category. -/
def triangulatedRelations : Set (FreeAbelianGroup (ObjectCode C)) :=
  {r | ∃ T : Triangle C, T ∈ distTriang C ∧ r = triangleRelation T}

variable {C}

lemma mem_triangulatedRelations_iff {r : FreeAbelianGroup (ObjectCode C)} :
    r ∈ triangulatedRelations C ↔ ∃ T : Triangle C, T ∈ distTriang C ∧ r = triangleRelation T :=
  Iff.rfl

lemma triangleRelation_mem_triangulatedRelations {T : Triangle C} (hT : T ∈ distTriang C) :
    triangleRelation T ∈ triangulatedRelations C :=
  ⟨T, hT, rfl⟩

end TriangulatedRelations

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [EssentiallySmall.{w'} D]

variable (C) in
/-- The Grothendieck group of an essentially small pretriangulated category: the free abelian
group on the isomorphism classes of objects, modulo `[Y] = [X] + [Z]` for every distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. -/
def TriangulatedK0 : Type w := PresentedK0 (triangulatedRelations C)

instance : AddCommGroup (TriangulatedK0 C) :=
  inferInstanceAs (AddCommGroup (PresentedK0 (triangulatedRelations C)))

namespace TriangulatedK0

/-- The class of an object in triangulated `K₀`. -/
noncomputable def of (X : C) : TriangulatedK0 C := PresentedK0.of X

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : TriangulatedK0 C) = of Y :=
  PresentedK0.of_congr e

/-- **The defining relation of triangulated `K₀`**: the class of the middle term of a
distinguished triangle is the sum of the classes of its two outer terms. -/
theorem of_distTriang {T : Triangle C} (hT : T ∈ distTriang C) :
    (of T.obj₂ : TriangulatedK0 C) = of T.obj₁ + of T.obj₃ := by
  have h := (map_triangleRelation_eq_zero_iff
    (PresentedK0.mk (rels := triangulatedRelations C)) T).1
    (PresentedK0.mk_eq_zero_of_mem (triangleRelation_mem_triangulatedRelations hT))
  rwa [PresentedK0.mk_freeOf, PresentedK0.mk_freeOf, PresentedK0.mk_freeOf] at h

/-- The defining relation of triangulated `K₀`, stated for a triangle presented by its three
maps. -/
theorem of_eq_add_of_distTriang {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : (of Y : TriangulatedK0 C) = of X + of Z :=
  of_distTriang hT

/-- The class of the cone of a distinguished triangle is the difference of the classes of its
first two terms. -/
theorem of_eq_sub_of_distTriang {T : Triangle C} (hT : T ∈ distTriang C) :
    (of T.obj₃ : TriangulatedK0 C) = of T.obj₂ - of T.obj₁ := by
  rw [of_distTriang hT]
  abel

/-- The class of the zero object vanishes: it is the third term of the contractible triangle. -/
@[simp]
theorem of_zero : (of (0 : C) : TriangulatedK0 C) = 0 := by
  have h : (of (0 : C) : TriangulatedK0 C) = of (0 : C) + of (0 : C) :=
    of_eq_add_of_distTriang (contractible_distinguished (0 : C))
  simpa using h

/-- The class of an object which is zero vanishes. -/
@[simp]
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : (of X : TriangulatedK0 C) = 0 := by
  rw [of_congr (hX.iso (isZero_zero C)), of_zero]

/-- The class of a biproduct is the sum of the classes: the biproduct triangles are
distinguished. -/
@[simp]
theorem of_biprod (X Y : C) : (of (X ⊞ Y) : TriangulatedK0 C) = of X + of Y :=
  of_distTriang (binaryBiproductTriangle_distinguished X Y)

/-- **The class of a shift**: `[X⟦1⟧] = -[X]`, forced by the distinguished triangle
`X ⟶ 0 ⟶ X⟦1⟧ ⟶ X⟦1⟧`. -/
theorem of_shift_one (X : C) : (of (X⟦(1 : ℤ)⟧) : TriangulatedK0 C) = -of X :=
  eq_neg_of_add_eq_zero_right
    ((of_eq_add_of_distTriang (contractible_distinguished₂ X)).symm.trans of_zero)

/-- **The class of an iterated shift**: `[X⟦n⟧] = (-1)ⁿ[X]` for every integer `n`, the sign being
`Int.negOnePow n`. -/
theorem of_shift (n : ℤ) (X : C) :
    (of (X⟦n⟧) : TriangulatedK0 C) = (n.negOnePow : ℤ) • of X := by
  have hpred : ∀ m : ℤ, (m - 1).negOnePow = -m.negOnePow := fun m => by
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]
  induction n using Int.induction_on with
  | zero => simp [of_congr ((shiftFunctorZero C ℤ).app X)]
  | succ n ih =>
    rw [of_congr ((shiftFunctorAdd' C (n : ℤ) 1 ((n : ℤ) + 1) rfl).app X), Functor.comp_obj,
      of_shift_one, ih, Int.negOnePow_succ, Units.val_neg, neg_zsmul]
  | pred n ih =>
    have h : (of (X⟦(-(n : ℤ))⟧) : TriangulatedK0 C) = -of (X⟦(-(n : ℤ) - 1)⟧) := by
      rw [of_congr ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by simp)).app X),
        Functor.comp_obj, of_shift_one]
    rw [hpred, Units.val_neg, neg_zsmul, ← ih, h, neg_neg]

/-- The image of the class map generates triangulated `K₀`. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → TriangulatedK0 C)) = ⊤ :=
  PresentedK0.closure_range_of

/-- Induction on the classes of objects of `C`: no skeleton representative is ever mentioned. -/
@[elab_as_elim]
theorem induction_on {motive : TriangulatedK0 C → Prop} (x : TriangulatedK0 C)
    (zero : motive 0) (of : ∀ X : C, motive (TriangulatedK0.of X))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (neg : ∀ a, motive a → motive (-a)) : motive x :=
  PresentedK0.induction_on x zero of add neg

variable {G : Type*} [AddCommGroup G]

/-- Two homomorphisms out of triangulated `K₀` agreeing on the classes of objects are equal. -/
@[ext]
theorem hom_ext {f g : TriangulatedK0 C →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  PresentedK0.hom_ext h

variable (C) in
/-- An additive invariant for triangulated `K₀`: a function on objects of `C`, constant on
isomorphism classes and additive on the distinguished triangles. These are exactly the data that
factor through `TauCeti.TriangulatedK0 C`; see `TauCeti.TriangulatedK0.liftEquiv`. -/
@[ext]
structure AdditiveInvariant (G : Type*) [AddCommGroup G] where
  /-- The value of the invariant on an object. -/
  obj : C → G
  /-- Isomorphic objects receive equal values. -/
  map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y
  /-- The value on the middle term of a distinguished triangle is the sum of the outer values. -/
  map_distTriang : ∀ ⦃T : Triangle C⦄, T ∈ distTriang C → obj T.obj₂ = obj T.obj₁ + obj T.obj₃

private noncomputable def AdditiveInvariant.toPresented (a : AdditiveInvariant C G) :
    PresentedK0.AdditiveInvariant (triangulatedRelations C) G where
  obj := a.obj
  map_iso := a.map_iso
  map_rel := by
    rintro _ ⟨T, hT, rfl⟩
    rw [map_triangleRelation_eq_zero_iff, freeLift_freeOf a.map_iso,
      freeLift_freeOf a.map_iso, freeLift_freeOf a.map_iso]
    exact a.map_distTriang hT

@[simp] private lemma AdditiveInvariant.toPresented_obj (a : AdditiveInvariant C G) :
    a.toPresented.obj = a.obj :=
  (rfl)

/-- The homomorphism out of triangulated `K₀` induced by a triangle-additive invariant. -/
noncomputable def lift (a : AdditiveInvariant C G) : TriangulatedK0 C →+ G :=
  PresentedK0.lift a.toPresented

@[simp]
lemma lift_of (a : AdditiveInvariant C G) (X : C) : lift a (of X) = a.obj X :=
  PresentedK0.lift_of a.toPresented X

/-- Any homomorphism agreeing with a triangle-additive invariant on object classes is its induced
lift. -/
theorem lift_unique (a : AdditiveInvariant C G) (f : TriangulatedK0 C →+ G)
    (hf : ∀ X : C, f (of X) = a.obj X) : f = lift a :=
  hom_ext fun X => by rw [hf, lift_of]

/-- **The universal property of triangulated `K₀`**: triangle-additive invariants with values in
`G` correspond bijectively to additive homomorphisms `TriangulatedK0 C →+ G`. -/
noncomputable def liftEquiv : AdditiveInvariant C G ≃ (TriangulatedK0 C →+ G) where
  toFun := lift
  invFun f :=
    { obj := fun X => f (of X)
      map_iso := fun _ _ e => by rw [of_congr e]
      map_distTriang := fun _ hT => by rw [of_distTriang hT, map_add] }
  left_inv a := by ext X; exact lift_of a X
  right_inv f := (lift_unique _ f fun _ => rfl).symm

@[simp]
lemma liftEquiv_apply (a : AdditiveInvariant C G) : liftEquiv a = lift a := (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (f : TriangulatedK0 C →+ G) (X : C) :
    ((liftEquiv (C := C) (G := G)).symm f).obj X = f (of X) := (rfl)

section Functoriality

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- A triangulated functor carries every chosen relation of the source into the relations of the
target. -/
private theorem mapsTo_triangulatedRelations :
    ∀ r ∈ triangulatedRelations C,
      freeMap F r ∈ AddSubgroup.closure (triangulatedRelations D) := by
  rintro _ ⟨T, hT, rfl⟩
  rw [freeMap_triangleRelation]
  exact AddSubgroup.subset_closure
    (triangleRelation_mem_triangulatedRelations (F.map_distinguished T hT))

/-- **Functoriality of triangulated `K₀`**: a triangulated functor induces a homomorphism of
triangulated Grothendieck groups. -/
noncomputable def map : TriangulatedK0 C →+ TriangulatedK0 D :=
  PresentedK0.map F (mapsTo_triangulatedRelations F)

@[simp]
lemma map_of (X : C) : map F (of X) = (of (F.obj X) : TriangulatedK0 D) :=
  PresentedK0.map_of F _ X

/-- Any homomorphism sending object classes to the classes of their images is the induced map. -/
theorem map_unique (f : TriangulatedK0 C →+ TriangulatedK0 D)
    (hf : ∀ X : C, f (of X) = (of (F.obj X) : TriangulatedK0 D)) : f = map F :=
  hom_ext fun X => by rw [hf, map_of]

variable (C) in
/-- The identity functor induces the identity of triangulated `K₀`. -/
@[simp]
theorem map_id : map (𝟭 C) = AddMonoidHom.id (TriangulatedK0 C) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.id_apply, Functor.id_obj]

/-- The induced maps of a composite of triangulated functors compose. -/
theorem map_comp {K : Type u''} [Category.{v''} K] [Preadditive K] [HasZeroObject K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive] [Pretriangulated K]
    [EssentiallySmall.{w''} K] (H : D ⥤ K) [H.CommShift ℤ] [H.IsTriangulated] :
    map (F ⋙ H) = (map H).comp (map F) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.comp_apply, map_of, map_of, Functor.comp_obj]

/-- Naturally isomorphic triangulated functors induce the same map. -/
theorem map_congr {F' : C ⥤ D} [F'.CommShift ℤ] [F'.IsTriangulated] (e : F ≅ F') :
    map F = map F' :=
  hom_ext fun X => by rw [map_of, map_of, of_congr (e.app X)]

end Functoriality

section Equivalence

/-- **Equivalence invariance of triangulated `K₀`**: a triangulated equivalence induces an
isomorphism of triangulated Grothendieck groups. -/
noncomputable def mapEquiv (e : C ≌ D) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.IsTriangulated] : TriangulatedK0 C ≃+ TriangulatedK0 D :=
  PresentedK0.mapEquiv e (mapsTo_triangulatedRelations e.functor)
    (mapsTo_triangulatedRelations e.inverse)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.IsTriangulated] (X : C) :
    mapEquiv e (of X) = (of (e.functor.obj X) : TriangulatedK0 D) :=
  PresentedK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.IsTriangulated] (Y : D) :
    (mapEquiv e).symm (of Y) = (of (e.inverse.obj Y) : TriangulatedK0 C) :=
  PresentedK0.mapEquiv_symm_of e _ _ Y

/-- The homomorphism underlying equivalence invariance is the map induced by the functor. -/
@[simp]
lemma mapEquiv_toAddMonoidHom (e : C ≌ D) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    [e.IsTriangulated] :
    ((mapEquiv e : TriangulatedK0 C ≃+ TriangulatedK0 D) : TriangulatedK0 C →+ TriangulatedK0 D) =
      map e.functor :=
  hom_ext fun X => by simp

end Equivalence

section Comparison

variable (C) in
/-- **The canonical comparison from split `K₀` to triangulated `K₀`.** It is induced by the class
map, which respects the biproduct relations because the biproduct triangles are distinguished. -/
noncomputable def fromSplit : SplitK0 C →+ TriangulatedK0 C :=
  SplitK0.lift
    { obj := fun X => of X
      map_iso := fun _ _ e => of_congr e
      map_biprod := of_biprod }

@[simp]
lemma fromSplit_of (X : C) : fromSplit C (SplitK0.of X) = (of X : TriangulatedK0 C) :=
  SplitK0.lift_of _ X

/-- The canonical comparison out of split `K₀` is the unique homomorphism preserving the classes
of objects. -/
theorem fromSplit_unique (f : SplitK0 C →+ TriangulatedK0 C)
    (hf : ∀ X : C, f (SplitK0.of X) = (of X : TriangulatedK0 C)) : f = fromSplit C :=
  SplitK0.hom_ext fun X => by rw [hf, fromSplit_of]

/-- The canonical comparison out of split `K₀` is surjective: the classes of objects generate
triangulated `K₀`, so triangulated `K₀` is a quotient of split `K₀`. -/
theorem fromSplit_surjective : Function.Surjective (fromSplit C) := by
  intro x
  induction x using TriangulatedK0.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of X => exact ⟨SplitK0.of X, fromSplit_of X⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | neg a ha =>
    obtain ⟨a', rfl⟩ := ha
    exact ⟨-a', map_neg _ _⟩

/-- **Naturality of the comparison out of split `K₀`** in a triangulated functor, which is in
particular additive and so also acts on split `K₀`. -/
theorem map_comp_fromSplit (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    (map F).comp (fromSplit C) = (fromSplit D).comp (SplitK0.map F) :=
  SplitK0.hom_ext fun X => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, fromSplit_of, map_of,
      SplitK0.map_of, fromSplit_of]

end Comparison

end TriangulatedK0

end TauCeti
