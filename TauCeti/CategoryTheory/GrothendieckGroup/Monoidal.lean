/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Associator
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# The tensor product makes split `K₀` a ring

The split Grothendieck group `TauCeti.SplitK0 C` of
`TauCeti/CategoryTheory/GrothendieckGroup/Split.lean` records the additive structure of a
category: `[X ⊞ Y] = [X] + [Y]`. When `C` also
carries a monoidal structure whose tensor product is additive in each factor
(`CategoryTheory.MonoidalPreadditive`), the tensor product descends to a multiplication on
`SplitK0 C` and makes it a ring, commutative as soon as `C` is braided.

The construction is entirely a matter of feeding the tensor product to the universal property
twice. For a fixed object `X`, tensoring on the left is an additive endofunctor of `C`, so
`TauCeti.SplitK0.map` turns it into an endomorphism of the group. Sending `X` to that
endomorphism is itself an isomorphism-invariant, biproduct-additive function of `X` -- additivity
in `X` is `TauCeti.SplitK0.map` applied to tensoring on the *right* -- so it
descends to `TauCeti.SplitK0.mulHom`, a biadditive multiplication with
`[X] * [Y] = [X ⊗ Y]`. Distributivity is then automatic, and the remaining ring axioms are the
associator, the unitors, and the braiding: each of them is an equality of bundled additive maps, so
it is checked on the classes of objects by `TauCeti.SplitK0.hom_ext`.

The multiplication is *not* obtained by a second presentation: no new relation is imposed, and the
underlying additive group is unchanged. In particular a biproduct-additive invariant into a ring
becomes a ring homomorphism `TauCeti.SplitK0.liftRingHom` exactly when it sends the tensor unit to
`1` and is multiplicative on the classes of objects, which is how character-style invariants are
recognized.

This is the ring structure the representation ring `R(G)` of a finite group carries. Split `K₀`
is the right home for it: the Grothendieck group of a semisimple category, such as the
finite-dimensional representations of a finite group over a field of characteristic zero, has no
relations beyond the biproduct ones, so the split group *is* the representation ring there.
Producing that instantiation additionally needs the smallness of the representation category,
which is a separate matter and is not proved here; nothing below assumes semisimplicity.

## Main definitions

* `TauCeti.SplitK0.mulHom C`: multiplication on split `K₀`, as a biadditive map.
* `TauCeti.SplitK0.instRing` and `TauCeti.SplitK0.instCommRing`: the ring structure, commutative
  for a braided category.
* `TauCeti.SplitK0.liftRingHom`: the ring homomorphism induced by a multiplicative, unit-preserving
  biproduct-additive invariant.
* `TauCeti.SplitK0.mapRingHom`: the ring homomorphism induced by a monoidal additive functor.

## Main results

* `TauCeti.SplitK0.of_mul_of`: the computation rule `[X] * [Y] = [X ⊗ Y]`, and
  `TauCeti.SplitK0.one_def`: the unit is the class of the tensor unit.
* `TauCeti.SplitK0.ringHom_ext`: two ring homomorphisms out of split `K₀` agreeing on the classes
  of objects are equal.
* `TauCeti.SplitK0.mapRingHom_id` and `TauCeti.SplitK0.mapRingHom_comp`: the induced ring
  homomorphism is functorial.

## Implementation notes

`TauCeti.SplitK0.mulHom` is stated as a bundled `SplitK0 C →+ SplitK0 C →+ SplitK0 C` rather than
as a bare function, because biadditivity is exactly what makes the ring axioms checkable on the
classes of objects: associativity, commutativity, and multiplicativity of an induced map are each
an equality of bundled maps, so `TauCeti.SplitK0.hom_ext` reduces them to the classes of objects
with no additive bookkeeping left to do.

Tensoring on the left by a fixed object, and the two lemmas saying that it is an
isomorphism-invariant, biproduct-additive function of that object, are the input to the second use
of the universal property and have no role afterwards, so they are private: the public computation
rule is `TauCeti.SplitK0.of_mul_of`.

The `Mul` and `One` instances are installed before the `Ring` instance so that the axioms can be
stated in the usual notation; the `Ring` instance reuses them rather than introducing new
operations. Distributivity alone stages a private `NonUnitalNonAssocRing` structure, which is what
makes Mathlib's bundled `AddMonoidHom.mulLeft₃`, `AddMonoidHom.mulRight₃` and `AddMonoidHom.mul`
applicable to the remaining axioms. No axiom witness is exported under a `TauCeti.SplitK0` name:
each is a field of the instance it discharges, so the general lemmas `mul_assoc`, `one_mul`, ...
are the only ones to use.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for the product on `K₀` of a symmetric monoidal category.
* `Mathlib/Algebra/DirectSum/Ring.lean`, whose bundled-multiplication proof pattern for the ring
  structure on a graded direct sum is the one followed here: the associativity proof below is the
  same `AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃` argument, the unit proofs the same
  `mulHom 1 = AddMonoidHom.id` and `(mulHom).flip 1 = AddMonoidHom.id` arguments, and
  `TauCeti.SplitK0.ringHom_ext` the same `RingHom.coe_addMonoidHom_injective` argument as
  `DirectSum.ringHom_ext`, with the additive extensionality of the direct sum replaced by
  `TauCeti.SplitK0.hom_ext`.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 4b, whose representation ring `R(G)` -- the Grothendieck ring of `FDRep k G` with addition
  from `⊕` and multiplication from `⊗` -- is the motivating instance of this ring structure.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w w' w'' v v' v'' u u' u''

namespace SplitK0

section Ring

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- Tensoring on the left by `X`, as an endomorphism of split `K₀`. -/
private noncomputable def mulLeft (X : C) : SplitK0 C →+ SplitK0 C :=
  map (tensorLeft X)

/-- Tensoring on the left by `X` sends the class of `Y` to the class of `X ⊗ Y`. -/
@[simp]
private lemma mulLeft_of (X Y : C) : mulLeft X (of Y) = (of (X ⊗ Y) : SplitK0 C) :=
  map_of (tensorLeft X) Y

/-- Isomorphic objects tensor on the left to the same endomorphism of split `K₀`. -/
private lemma mulLeft_congr {X Y : C} (e : X ≅ Y) :
    (mulLeft X : SplitK0 C →+ SplitK0 C) = mulLeft Y :=
  map_congr fun Z => ⟨whiskerRightIso e Z⟩

/-- Tensoring on the left by a biproduct is the sum of tensoring on the left by each summand;
this is tensoring on the *right* applied to the defining relation of split `K₀`. -/
private lemma mulLeft_biprod (X Y : C) :
    (mulLeft (X ⊞ Y) : SplitK0 C →+ SplitK0 C) = mulLeft X + mulLeft Y := by
  refine hom_ext fun Z => ?_
  have h := congrArg (map (tensorRight Z)) (of_biprod X Y)
  simp only [map_add, map_of] at h
  simpa using h

variable (C) in
/-- Tensoring on the left is a biproduct-additive invariant of the left factor: this is the datum
that descends the tensor product to a multiplication on split `K₀`. -/
private noncomputable def mulInvariant : AdditiveInvariant C (SplitK0 C →+ SplitK0 C) where
  obj := mulLeft
  map_iso _ _ e := mulLeft_congr e
  map_biprod := mulLeft_biprod

/-- The invariant `TauCeti.SplitK0.mulInvariant` takes an object to tensoring on the left by it. -/
@[simp]
private lemma mulInvariant_obj (X : C) : (mulInvariant C).obj X = mulLeft X := (rfl)

variable (C) in
/-- Multiplication on split `K₀`, as a biadditive map. -/
noncomputable def mulHom : SplitK0 C →+ SplitK0 C →+ SplitK0 C :=
  lift (mulInvariant C)

/-- Multiplication by the class of an object is tensoring on the left by that object. -/
@[simp]
private lemma mulHom_of (X : C) : mulHom C (of X) = mulLeft X := by
  rw [mulHom, lift_of, mulInvariant_obj]

/-- The multiplication on split `K₀` induced by the tensor product. -/
noncomputable instance instMul : Mul (SplitK0 C) where
  mul a b := mulHom C a b

/-- The multiplication on split `K₀` is `TauCeti.SplitK0.mulHom`. -/
lemma mul_def (a b : SplitK0 C) : a * b = mulHom C a b := (rfl)

/-- The unit of split `K₀` is the class of the tensor unit. -/
noncomputable instance instOne : One (SplitK0 C) where
  one := of (𝟙_ C)

omit [MonoidalPreadditive C] in
/-- The unit of split `K₀` is the class of the tensor unit. -/
lemma one_def : (1 : SplitK0 C) = of (𝟙_ C) := (rfl)

/-- The computation rule for the product: the class of a tensor product is the product of the
classes. -/
@[simp]
theorem of_mul_of (X Y : C) : (of X : SplitK0 C) * of Y = of (X ⊗ Y) := by
  rw [mul_def, mulHom_of, mulLeft_of]

/-! ### The ring structure

Distributivity is additivity of `TauCeti.SplitK0.mulHom` in each variable; it already stages a
`NonUnitalNonAssocRing` structure. The remaining axioms are then equalities of the bundled maps
`AddMonoidHom.mulLeft₃`, `AddMonoidHom.mulRight₃` and `AddMonoidHom.mul`, so
`TauCeti.SplitK0.hom_ext` reduces them to the classes of objects. -/

/-- Split `K₀` with the multiplication descended from the tensor product, before associativity and
the unit are available: each field is additivity of `TauCeti.SplitK0.mulHom` in one of its two
variables. This staging structure is what makes Mathlib's bundled multiplications
`AddMonoidHom.mulLeft₃`, `AddMonoidHom.mulRight₃` and `AddMonoidHom.mul` applicable, so that the
remaining ring axioms become equalities of additive maps. It is private, and the `Ring` instance
below therefore repeats its four one-line field proofs rather than extending it: the module system
exposes the value of an instance, which a private declaration may not enter. -/
@[reducible]
private noncomputable def nonUnitalNonAssocRing : NonUnitalNonAssocRing (SplitK0 C) where
  left_distrib a b c := map_add (mulHom C a) b c
  right_distrib a b c := by rw [mul_def, mul_def, mul_def, map_add, AddMonoidHom.add_apply]
  zero_mul a := by rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero a := map_zero (mulHom C a)

section Associativity

attribute [local instance] nonUnitalNonAssocRing

/-- Associativity of the tensor multiplication, as the equality of the two bundled triple products:
this is the associator of `C`, and `TauCeti.SplitK0.hom_ext` reduces the equality to the classes of
objects. -/
private theorem mulLeft₃_eq_mulRight₃ :
    (AddMonoidHom.mulLeft₃ : SplitK0 C →+ _) = AddMonoidHom.mulRight₃ := by
  refine hom_ext fun X => hom_ext fun Y => hom_ext fun Z => ?_
  simp only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply, of_mul_of]
  exact of_congr (α_ X Y Z)

end Associativity

/-- The tensor product makes the split Grothendieck group of a monoidal additive category a ring,
with `[X] * [Y] = [X ⊗ Y]` and unit the class of the tensor unit: associativity is the associator
of `C`, and the unit laws are its unitors. -/
noncomputable instance instRing : Ring (SplitK0 C) where
  __ := (inferInstance : AddCommGroup (SplitK0 C))
  left_distrib a b c := map_add (mulHom C a) b c
  right_distrib a b c := by rw [mul_def, mul_def, mul_def, map_add, AddMonoidHom.add_apply]
  zero_mul a := by rw [mul_def, map_zero, AddMonoidHom.zero_apply]
  mul_zero a := map_zero (mulHom C a)
  mul_assoc a b c := by
    simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun mulLeft₃_eq_mulRight₃ a) b) c
  one_mul a := by
    suffices h : mulHom C 1 = AddMonoidHom.id (SplitK0 C) by
      rw [mul_def, h, AddMonoidHom.id_apply]
    refine hom_ext fun X => ?_
    rw [one_def, mulHom_of, mulLeft_of, AddMonoidHom.id_apply]
    exact of_congr (λ_ X)
  mul_one a := by
    suffices h : (mulHom C).flip 1 = AddMonoidHom.id (SplitK0 C) by
      rw [mul_def, ← AddMonoidHom.flip_apply, h, AddMonoidHom.id_apply]
    refine hom_ext fun X => ?_
    rw [AddMonoidHom.flip_apply, one_def, mulHom_of, mulLeft_of, AddMonoidHom.id_apply]
    exact of_congr (ρ_ X)

/-- Two ring homomorphisms out of split `K₀` agreeing on the classes of objects are equal. The
target is a ring rather than a semiring: split `K₀` is generated by the classes of objects as a
*group*, so agreeing on them forces agreement on the negatives only when the target has them. -/
@[ext]
theorem ringHom_ext {R : Type*} [NonAssocRing R] {f g : SplitK0 C →+* R}
    (h : ∀ X : C, f (of X) = g (of X)) : f = g := by
  have hfg : (f : SplitK0 C →+ R) = (g : SplitK0 C →+ R) := hom_ext h
  exact RingHom.coe_addMonoidHom_injective hfg

section Lift

variable {R : Type*} [NonAssocRing R] (a : AdditiveInvariant C R) (hone : a.obj (𝟙_ C) = 1)
  (hmul : ∀ X Y : C, a.obj (X ⊗ Y) = a.obj X * a.obj Y)

/-- The ring homomorphism out of split `K₀` induced by a biproduct-additive invariant which sends
the tensor unit to `1` and is multiplicative on tensor products. With
`TauCeti.SplitK0.ringHom_ext` for uniqueness, this is the universal property of split `K₀` as a
ring: it is what promotes a multiplicative invariant, such as a character, to a ring homomorphism.
The target is a ring rather than a semiring because a `TauCeti.SplitK0.AdditiveInvariant` takes
values in an additive *group*. -/
noncomputable def liftRingHom : SplitK0 C →+* R where
  toFun := lift a
  map_zero' := map_zero (lift a)
  map_add' := map_add (lift a)
  map_one' := by
    rw [one_def, lift_of]
    exact hone
  map_mul' := by
    rw [AddMonoidHom.map_mul_iff]
    refine hom_ext fun X => hom_ext fun Y => ?_
    simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply, AddMonoidHom.compl₂_apply,
      AddMonoidHom.comp_apply, of_mul_of, lift_of]
    exact hmul X Y

/-- The induced ring homomorphism takes the class of an object to the value of the invariant. -/
@[simp]
lemma liftRingHom_of (X : C) : liftRingHom a hone hmul (of X) = a.obj X :=
  lift_of a X

/-- The additive homomorphism underlying `TauCeti.SplitK0.liftRingHom` is the additive lift of the
invariant. -/
@[simp]
lemma liftRingHom_toAddMonoidHom :
    ((liftRingHom a hone hmul : SplitK0 C →+* R) : SplitK0 C →+ R) = lift a :=
  hom_ext fun X => by rw [AddMonoidHom.coe_coe, liftRingHom_of, lift_of]

end Lift

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- For a braided monoidal additive category the ring structure on split `K₀` is commutative:
`[X] * [Y] = [X ⊗ Y] = [Y ⊗ X] = [Y] * [X]` by the braiding of `C`. -/
noncomputable instance instCommRing : CommRing (SplitK0 C) where
  __ := instRing
  mul_comm a b := by
    suffices h : (AddMonoidHom.mul : SplitK0 C →+ SplitK0 C →+ SplitK0 C) = AddMonoidHom.mul.flip by
      simpa only [AddMonoidHom.flip_apply, AddMonoidHom.mul_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun h a) b
    refine hom_ext fun X => hom_ext fun Y => ?_
    rw [AddMonoidHom.flip_apply, AddMonoidHom.mul_apply, AddMonoidHom.mul_apply, of_mul_of,
      of_mul_of]
    exact of_congr (β_ X Y)

end CommRing

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [MonoidalCategory D]
  [MonoidalPreadditive D] [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

/-- The ring homomorphism of split Grothendieck groups induced by a monoidal additive functor:
the functorial map `TauCeti.SplitK0.map`, read through the universal property as the invariant
`X ↦ [F.obj X]`, which the comparison isomorphisms of `F` make unit-preserving and multiplicative
on tensor products. -/
noncomputable def mapRingHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    SplitK0 C →+* SplitK0 D :=
  liftRingHom ((liftEquiv (C := C) (G := SplitK0 D)).symm (map F))
    (by
      simp only [liftEquiv_symm_apply_obj, one_def, map_of]
      exact of_congr (Functor.Monoidal.εIso F).symm)
    fun X Y => by
      simp only [liftEquiv_symm_apply_obj, map_of, of_mul_of]
      exact of_congr (Functor.Monoidal.μIso F X Y).symm

/-- The additive homomorphism underlying `TauCeti.SplitK0.mapRingHom` is the functorial map. -/
@[simp]
lemma mapRingHom_toAddMonoidHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    ((mapRingHom F : SplitK0 C →+* SplitK0 D) : SplitK0 C →+ SplitK0 D) = map F := by
  rw [mapRingHom, liftRingHom_toAddMonoidHom, ← liftEquiv_apply, Equiv.apply_symm_apply]

/-- The induced ring homomorphism takes the class of an object to the class of its image. -/
@[simp]
lemma mapRingHom_of (F : C ⥤ D) [F.Additive] [F.Monoidal] (X : C) :
    mapRingHom F (of X : SplitK0 C) = of (F.obj X) := by
  rw [← AddMonoidHom.coe_coe, mapRingHom_toAddMonoidHom, map_of]

/-- `TauCeti.SplitK0.mapRingHom` sends the identity functor to the identity ring homomorphism. -/
@[simp]
lemma mapRingHom_id : mapRingHom (𝟭 C) = RingHom.id (SplitK0 C) :=
  ringHom_ext fun X => by rw [mapRingHom_of, RingHom.id_apply, Functor.id_obj]

/-- `TauCeti.SplitK0.mapRingHom` sends a composite of monoidal additive functors to the composite
ring homomorphism. -/
@[simp]
lemma mapRingHom_comp {E : Type u''} [Category.{v''} E] [Preadditive E] [MonoidalCategory E]
    [MonoidalPreadditive E] [HasBinaryBiproducts E] [EssentiallySmall.{w''} E] (F : C ⥤ D)
    (G : D ⥤ E) [F.Additive] [G.Additive] [F.Monoidal] [G.Monoidal] :
    mapRingHom (F ⋙ G) = (mapRingHom G).comp (mapRingHom F) :=
  ringHom_ext fun X => by
    rw [mapRingHom_of, RingHom.coe_comp, Function.comp_apply, mapRingHom_of, mapRingHom_of,
      Functor.comp_obj]

/-- Objectwise isomorphic monoidal additive functors induce the same ring homomorphism; in
particular naturally isomorphic ones do. -/
lemma mapRingHom_congr {F G : C ⥤ D} [F.Additive] [G.Additive] [F.Monoidal] [G.Monoidal]
    (h : ∀ X : C, Nonempty (F.obj X ≅ G.obj X)) : mapRingHom F = mapRingHom G :=
  ringHom_ext fun X => by rw [mapRingHom_of, mapRingHom_of, of_congr (h X).some]

end Functoriality

end SplitK0

end TauCeti
