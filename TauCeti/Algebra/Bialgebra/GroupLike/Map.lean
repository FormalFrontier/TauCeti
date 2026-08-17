/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.GroupLike.Map

/-!
# Functoriality of group-like elements

A bialgebra morphism sends group-like elements to group-like elements and respects their
multiplication. This file bundles that operation as a monoid homomorphism and records that a
bialgebra equivalence induces a multiplicative equivalence of group-like elements.

## Main declarations

* `TauCeti.GroupLike.map`: the homomorphism on group-like elements induced by a bialgebra map.
* `TauCeti.GroupLike.mapEquiv`: the equivalence induced by a bialgebra equivalence.
-/

public section

namespace TauCeti

universe u v w

namespace GroupLike

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Bialgebra R A] [Bialgebra R B]

/-- A bialgebra morphism induces a monoid homomorphism on group-like elements. -/
def map (f : A →ₐc[R] B) : _root_.GroupLike R A →* _root_.GroupLike R B where
  toFun x := ⟨f x.val, x.isGroupLikeElem_val.map f⟩
  map_one' := _root_.GroupLike.val_injective (map_one f)
  map_mul' x y := _root_.GroupLike.val_injective (map_mul f x.val y.val)

/-- The underlying value of the image of a group-like element is its image under the bialgebra
morphism. -/
@[simp]
theorem val_map (f : A →ₐc[R] B) (x : _root_.GroupLike R A) :
    (map f x).val = f x.val :=
  (rfl)

/-- Mapping group-like elements respects identity bialgebra morphisms. -/
@[simp]
theorem map_id : map (_root_.BialgHom.id R A) = MonoidHom.id (_root_.GroupLike R A) := by
  ext x
  rfl

/-- Mapping group-like elements respects composition of bialgebra morphisms. -/
@[simp]
theorem map_comp {C : Type*} [Semiring C] [Bialgebra R C]
    (g : B →ₐc[R] C) (f : A →ₐc[R] B) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  rfl

/-- A bialgebra equivalence induces a multiplicative equivalence of group-like elements. -/
def mapEquiv (e : A ≃ₐc[R] B) :
    _root_.GroupLike R A ≃* _root_.GroupLike R B where
  __ := equivOfCoalgEquiv e.toCoalgEquiv
  map_mul' x y := by
    apply _root_.GroupLike.val_injective
    simp only [Equiv.toFun_as_coe, val_equivOfCoalgEquiv, _root_.GroupLike.val_mul]
    rw [_root_.BialgEquiv.toCoalgEquiv_eq_coe]
    exact map_mul e x.val y.val

/-- The underlying value of `mapEquiv` is the original bialgebra equivalence. -/
@[simp]
theorem val_mapEquiv (e : A ≃ₐc[R] B) (x : _root_.GroupLike R A) :
    (mapEquiv e x).val = e x.val :=
  val_equivOfCoalgEquiv e.toCoalgEquiv x

/-- Mapping group-like elements along the identity equivalence is the identity equivalence. -/
@[simp]
theorem mapEquiv_refl : mapEquiv (_root_.BialgEquiv.refl R A) = MulEquiv.refl _ := by
  ext x
  simp

/-- Mapping group-like elements along a composite equivalence is the composite of the maps. -/
@[simp]
theorem mapEquiv_trans {C : Type*} [Semiring C] [Bialgebra R C]
    (e : A ≃ₐc[R] B) (f : B ≃ₐc[R] C) :
    mapEquiv (e.trans f) = (mapEquiv e).trans (mapEquiv f) := by
  ext x
  calc
    (mapEquiv (e.trans f) x).val = (e.trans f) x.val := val_mapEquiv (e.trans f) x
    _ = f (e x.val) := BialgEquiv.trans_apply e f x.val
    _ = f (mapEquiv e x).val := congrArg f (val_mapEquiv e x).symm
    _ = (mapEquiv f (mapEquiv e x)).val := (val_mapEquiv f (mapEquiv e x)).symm

/-- The inverse of the induced equivalence is induced by the inverse equivalence. -/
@[simp]
theorem mapEquiv_symm (e : A ≃ₐc[R] B) :
    (mapEquiv e).symm = mapEquiv e.symm := by
  ext x
  apply e.injective
  calc
    e ((mapEquiv e).symm x).val = (mapEquiv e ((mapEquiv e).symm x)).val :=
      (val_mapEquiv e _).symm
    _ = x.val := congrArg _ ((mapEquiv e).apply_symm_apply x)
    _ = e (e.symm x.val) := (e.apply_symm_apply x.val).symm
    _ = e (mapEquiv e.symm x).val := congrArg e (val_mapEquiv e.symm x).symm

end GroupLike

end TauCeti
