/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
`TauCeti.SplitK0.map` turns it into an endomorphism `TauCeti.SplitK0.mulLeft X` of the group.
Sending `X` to that endomorphism is itself an isomorphism-invariant, biproduct-additive function
of `X` -- additivity in `X` is `TauCeti.SplitK0.map` applied to tensoring on the *right* -- so it
descends to `TauCeti.SplitK0.mulHom`, a biadditive multiplication with
`[X] * [Y] = [X ⊗ Y]`. Distributivity is then automatic, and the remaining ring axioms are the
associator, the unitors, and the braiding, checked on classes of objects by
`TauCeti.SplitK0.induction_on`.

The multiplication is *not* obtained by a second presentation: no new relation is imposed, and the
underlying additive group is unchanged. In particular a biproduct-additive invariant into a ring
becomes a ring homomorphism exactly when it is multiplicative on classes of objects, which is how
character-style invariants are recognized.

This is the ring structure the representation ring `R(G)` of a finite group carries. Split `K₀`
is the right home for it: the Grothendieck group of a semisimple category, such as the
finite-dimensional representations of a finite group over a field of characteristic zero, has no
relations beyond the biproduct ones, so the split group *is* the representation ring there.
Producing that instantiation additionally needs the smallness of the representation category,
which is a separate matter and is not proved here; nothing below assumes semisimplicity.

## Main definitions

* `TauCeti.SplitK0.mulLeft X`: tensoring on the left by `X`, as an endomorphism of split `K₀`.
* `TauCeti.SplitK0.mulHom C`: multiplication on split `K₀`, as a biadditive map.
* `TauCeti.SplitK0.instRing` and `TauCeti.SplitK0.instCommRing`: the ring structure, commutative
  for a braided category.
* `TauCeti.SplitK0.mapRingHom`: the ring homomorphism induced by a monoidal additive functor.

## Main results

* `TauCeti.SplitK0.of_mul_of`: the computation rule `[X] * [Y] = [X ⊗ Y]`, and
  `TauCeti.SplitK0.one_def`: the unit is the class of the tensor unit.
* `TauCeti.SplitK0.ringHom_ext`: two ring homomorphisms out of split `K₀` agreeing on the classes
  of objects are equal.

## Implementation notes

`TauCeti.SplitK0.mulHom` is stated as a bundled `SplitK0 C →+ SplitK0 C →+ SplitK0 C` rather than
as a bare function, because biadditivity is exactly what makes the ring axioms checkable on the
classes of objects: each of associativity, commutativity, and multiplicativity of an induced map
is proved by `TauCeti.SplitK0.induction_on` in each variable in turn, the additive steps being
handled by the two distributive laws.

The `Mul` and `One` instances are installed before the `Ring` instance so that the axioms can be
stated in the usual notation; the `Ring` instance reuses them rather than introducing new
operations. The axioms themselves are therefore stated and proved before the `Ring` instance
exists, which is why they are `protected` declarations named after the ring axioms they discharge:
once the instance is in place the general lemmas `mul_assoc`, `one_mul`, ... are the ones to use,
and the `TauCeti.SplitK0`-qualified names are only the input to the instance.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for the product on `K₀` of a symmetric monoidal category.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 4b, whose representation ring `R(G)` -- the Grothendieck ring of `FDRep k G` with addition
  from `⊕` and multiplication from `⊗` -- is the motivating instance of this ring structure.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w w' v v' u u'

namespace SplitK0

section Ring

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- Tensoring on the left by `X`, as an endomorphism of split `K₀`. -/
noncomputable def mulLeft (X : C) : SplitK0 C →+ SplitK0 C :=
  map (tensorLeft X)

/-- Tensoring on the left by `X` sends the class of `Y` to the class of `X ⊗ Y`. -/
@[simp]
lemma mulLeft_of (X Y : C) : mulLeft X (of Y) = (of (X ⊗ Y) : SplitK0 C) :=
  map_of (tensorLeft X) Y

/-- Isomorphic objects tensor on the left to the same endomorphism of split `K₀`. -/
lemma mulLeft_congr {X Y : C} (e : X ≅ Y) :
    (mulLeft X : SplitK0 C →+ SplitK0 C) = mulLeft Y :=
  map_congr fun Z => ⟨whiskerRightIso e Z⟩

/-- Tensoring on the left by a biproduct is the sum of tensoring on the left by each summand;
this is tensoring on the *right* applied to the defining relation of split `K₀`. -/
lemma mulLeft_biprod (X Y : C) :
    (mulLeft (X ⊞ Y) : SplitK0 C →+ SplitK0 C) = mulLeft X + mulLeft Y := by
  refine hom_ext fun Z => ?_
  have h := congrArg (map (tensorRight Z)) (of_biprod X Y)
  simp only [map_add, map_of] at h
  simpa using h

variable (C) in
/-- Tensoring on the left is a biproduct-additive invariant of the left factor: this is the datum
that descends the tensor product to a multiplication on split `K₀`. -/
noncomputable def mulInvariant : AdditiveInvariant C (SplitK0 C →+ SplitK0 C) where
  obj := mulLeft
  map_iso _ _ e := mulLeft_congr e
  map_biprod := mulLeft_biprod

/-- The invariant `TauCeti.SplitK0.mulInvariant` takes an object to tensoring on the left by it. -/
@[simp]
lemma mulInvariant_obj (X : C) : (mulInvariant C).obj X = mulLeft X := (rfl)

variable (C) in
/-- Multiplication on split `K₀`, as a biadditive map. -/
noncomputable def mulHom : SplitK0 C →+ SplitK0 C →+ SplitK0 C :=
  lift (mulInvariant C)

/-- Multiplication by the class of an object is tensoring on the left by that object. -/
@[simp]
lemma mulHom_of (X : C) : mulHom C (of X) = mulLeft X := by
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

/-! ### The ring axioms

Distributivity is additivity of `TauCeti.SplitK0.mulHom` in each variable; the remaining axioms
are proved on the classes of objects and propagated by it. -/

/-- The product distributes over sums in the right factor. -/
protected theorem mul_add (a b c : SplitK0 C) : a * (b + c) = a * b + a * c :=
  map_add (mulHom C a) b c

/-- The product distributes over sums in the left factor. -/
protected theorem add_mul (a b c : SplitK0 C) : (a + b) * c = a * c + b * c := by
  rw [mul_def, mul_def, mul_def, map_add]
  rfl

/-- Negating the right factor negates the product. -/
protected theorem mul_neg (a b : SplitK0 C) : a * -b = -(a * b) :=
  map_neg (mulHom C a) b

/-- Negating the left factor negates the product. -/
protected theorem neg_mul (a b : SplitK0 C) : -a * b = -(a * b) := by
  rw [mul_def, mul_def, map_neg]
  rfl

/-- The product with `0` on the right vanishes. -/
protected theorem mul_zero (a : SplitK0 C) : a * 0 = 0 :=
  map_zero (mulHom C a)

/-- The product with `0` on the left vanishes. -/
protected theorem zero_mul (a : SplitK0 C) : 0 * a = 0 := by
  rw [mul_def, map_zero]
  rfl

private theorem mul_assoc_of_of (X Y : C) (c : SplitK0 C) :
    (of X : SplitK0 C) * of Y * c = of X * (of Y * c) := by
  induction c using SplitK0.induction_on with
  | zero => simp only [SplitK0.mul_zero]
  | of Z => rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, of_congr (α_ X Y Z)]
  | add p q hp hq => rw [SplitK0.mul_add, SplitK0.mul_add, SplitK0.mul_add, hp, hq]
  | neg p hp => rw [SplitK0.mul_neg, SplitK0.mul_neg, SplitK0.mul_neg, hp]

private theorem mul_assoc_of (X : C) (b c : SplitK0 C) :
    (of X : SplitK0 C) * b * c = of X * (b * c) := by
  induction b using SplitK0.induction_on with
  | zero => simp only [SplitK0.mul_zero, SplitK0.zero_mul]
  | of Y => exact mul_assoc_of_of X Y c
  | add p q hp hq =>
      rw [SplitK0.mul_add, SplitK0.add_mul, SplitK0.add_mul, hp, hq, SplitK0.mul_add]
  | neg p hp => rw [SplitK0.mul_neg, SplitK0.neg_mul, SplitK0.neg_mul, hp, SplitK0.mul_neg]

/-- The product is associative; this is the associator of `C`, propagated by biadditivity. -/
protected theorem mul_assoc (a b c : SplitK0 C) : a * b * c = a * (b * c) := by
  induction a using SplitK0.induction_on with
  | zero => simp only [SplitK0.zero_mul]
  | of X => exact mul_assoc_of X b c
  | add p q hp hq => rw [SplitK0.add_mul, SplitK0.add_mul, SplitK0.add_mul, hp, hq]
  | neg p hp => rw [SplitK0.neg_mul, SplitK0.neg_mul, SplitK0.neg_mul, hp]

/-- The class of the tensor unit is a left unit; this is the left unitor of `C`. -/
protected theorem one_mul (a : SplitK0 C) : 1 * a = a := by
  induction a using SplitK0.induction_on with
  | zero => simp only [SplitK0.mul_zero]
  | of X => rw [one_def, of_mul_of, of_congr (λ_ X)]
  | add p q hp hq => rw [SplitK0.mul_add, hp, hq]
  | neg p hp => rw [SplitK0.mul_neg, hp]

/-- The class of the tensor unit is a right unit; this is the right unitor of `C`. -/
protected theorem mul_one (a : SplitK0 C) : a * 1 = a := by
  induction a using SplitK0.induction_on with
  | zero => simp only [SplitK0.zero_mul]
  | of X => rw [one_def, of_mul_of, of_congr (ρ_ X)]
  | add p q hp hq => rw [SplitK0.add_mul, hp, hq]
  | neg p hp => rw [SplitK0.neg_mul, hp]

/-- The tensor product makes the split Grothendieck group of a monoidal additive category a ring,
with `[X] * [Y] = [X ⊗ Y]` and unit the class of the tensor unit. -/
noncomputable instance instRing : Ring (SplitK0 C) where
  __ := (inferInstance : AddCommGroup (SplitK0 C))
  mul a b := a * b
  one := 1
  left_distrib := SplitK0.mul_add
  right_distrib := SplitK0.add_mul
  zero_mul := SplitK0.zero_mul
  mul_zero := SplitK0.mul_zero
  mul_assoc := SplitK0.mul_assoc
  one_mul := SplitK0.one_mul
  mul_one := SplitK0.mul_one

/-- Two ring homomorphisms out of split `K₀` agreeing on the classes of objects are equal. The
target is a ring rather than a semiring: split `K₀` is generated by the classes of objects as a
*group*, so agreeing on them forces agreement on the negatives only when the target has them. -/
@[ext]
theorem ringHom_ext {R : Type*} [NonAssocRing R] {f g : SplitK0 C →+* R}
    (h : ∀ X : C, f (of X) = g (of X)) : f = g := by
  have hfg : (f : SplitK0 C →+ R) = (g : SplitK0 C →+ R) := hom_ext h
  exact RingHom.coe_addMonoidHom_injective hfg

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

private theorem mul_comm_of (X : C) (b : SplitK0 C) :
    (of X : SplitK0 C) * b = b * of X := by
  induction b using SplitK0.induction_on with
  | zero => simp only [SplitK0.mul_zero, SplitK0.zero_mul]
  | of Y => rw [of_mul_of, of_mul_of, of_congr (β_ X Y)]
  | add p q hp hq => rw [SplitK0.mul_add, SplitK0.add_mul, hp, hq]
  | neg p hp => rw [SplitK0.mul_neg, SplitK0.neg_mul, hp]

/-- The product is commutative; this is the braiding of `C`, propagated by biadditivity. -/
protected theorem mul_comm (a b : SplitK0 C) : a * b = b * a := by
  induction a using SplitK0.induction_on with
  | zero => simp only [SplitK0.zero_mul, SplitK0.mul_zero]
  | of X => exact mul_comm_of X b
  | add p q hp hq => rw [SplitK0.add_mul, SplitK0.mul_add, hp, hq]
  | neg p hp => rw [SplitK0.neg_mul, SplitK0.mul_neg, hp]

/-- For a braided monoidal additive category the ring structure on split `K₀` is commutative. -/
noncomputable instance instCommRing : CommRing (SplitK0 C) where
  __ := instRing
  mul_comm := SplitK0.mul_comm

end CommRing

section Functoriality

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [MonoidalCategory D]
  [MonoidalPreadditive D] [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

private theorem map_mul_of_of (F : C ⥤ D) [F.Additive] [F.Monoidal] (X Y : C) :
    map F ((of X : SplitK0 C) * of Y) = map F (of X) * map F (of Y) := by
  rw [of_mul_of, map_of, map_of, map_of, of_mul_of, of_congr (Functor.Monoidal.μIso F X Y)]

private theorem map_mul_of (F : C ⥤ D) [F.Additive] [F.Monoidal] (X : C) (b : SplitK0 C) :
    map F ((of X : SplitK0 C) * b) = map F (of X) * map F b := by
  induction b using SplitK0.induction_on with
  | zero => simp only [SplitK0.mul_zero, map_zero]
  | of Y => exact map_mul_of_of F X Y
  | add p q hp hq => rw [SplitK0.mul_add, map_add, hp, hq, map_add, SplitK0.mul_add]
  | neg p hp => rw [SplitK0.mul_neg, map_neg, hp, map_neg, SplitK0.mul_neg]

private theorem map_mul' (F : C ⥤ D) [F.Additive] [F.Monoidal] (a b : SplitK0 C) :
    map F (a * b) = map F a * map F b := by
  induction a using SplitK0.induction_on with
  | zero => simp only [SplitK0.zero_mul, map_zero]
  | of X => exact map_mul_of F X b
  | add p q hp hq => rw [SplitK0.add_mul, map_add, hp, hq, map_add, SplitK0.add_mul]
  | neg p hp => rw [SplitK0.neg_mul, map_neg, hp, map_neg, SplitK0.neg_mul]

/-- The ring homomorphism of split Grothendieck groups induced by a monoidal additive functor. -/
noncomputable def mapRingHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    SplitK0 C →+* SplitK0 D where
  toFun := map F
  map_zero' := map_zero (map F)
  map_add' := map_add (map F)
  map_one' := by
    rw [one_def, map_of, one_def]
    exact of_congr (Functor.Monoidal.εIso F).symm
  map_mul' := map_mul' F

/-- The induced ring homomorphism takes the class of an object to the class of its image. -/
@[simp]
lemma mapRingHom_of (F : C ⥤ D) [F.Additive] [F.Monoidal] (X : C) :
    mapRingHom F (of X : SplitK0 C) = of (F.obj X) :=
  map_of F X

/-- The additive homomorphism underlying `TauCeti.SplitK0.mapRingHom` is the functorial map. -/
@[simp]
lemma mapRingHom_toAddMonoidHom (F : C ⥤ D) [F.Additive] [F.Monoidal] :
    ((mapRingHom F : SplitK0 C →+* SplitK0 D) : SplitK0 C →+ SplitK0 D) = map F :=
  (rfl)

end Functoriality

end SplitK0

end TauCeti
