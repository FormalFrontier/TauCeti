/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# The zero comodule

This file adds the zero object for right comodules over a coalgebra. This is Layer 1
infrastructure for the reductive-groups roadmap target "Comodules over a coalgebra/Hopf
algebra": before the finite-dimensional comodule category can be used as the additive
representation category, it needs the standard zero object compatible with the existing zero
morphisms.

The zero comodule is implemented by the unique coaction on `PUnit`. The bundled API exposes
the named zero objects through their `IsZero` characterizations, rather than through the
concrete carrier.

## Main declarations

* `TauCeti.ComoduleCat.zero`: the bundled zero comodule.
* `TauCeti.ComoduleCat.subsingleton_zero`: the bundled zero comodule has subsingleton carrier.
* `TauCeti.ComoduleCat.isZero_zero`: `ComoduleCat.zero` is a zero object.
* `HasZeroObject (ComoduleCat R C)`.

## References

The construction is the standard zero object in the category of comodules; see Sweedler,
*Hopf Algebras*, Chapter 2. It supplies an additive-category prerequisite for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1, "Comodules over a coalgebra/Hopf
algebra". The proof that a subsingleton bundled comodule is zero follows Mathlib's
`SemimoduleCat.isZero_of_subsingleton` / `ModuleCat.isZero_of_subsingleton` pattern.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

variable (R : Type u) (C : Type v)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The unique right-comodule structure on the zero module `PUnit`. -/
instance instPUnit : Comodule R C PUnit where
  coact := 0
  coassoc := by
    ext x
    exact Subsingleton.elim _ _
  lTensor_counit_comp_coact := by
    ext x
    exact Subsingleton.elim _ _

end Comodule

namespace ComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The bundled zero right comodule. -/
@[expose] def zero : ComoduleCat.{u, v, w} R C :=
  of R C PUnit.{w + 1}

/-- The named zero comodule has subsingleton carrier. -/
theorem subsingleton_zero : Subsingleton (zero R C : ComoduleCat.{u, v, w} R C) := by
  rw [zero]
  infer_instance

/-- A comodule whose underlying type is subsingleton is a zero object. -/
theorem isZero_of_subsingleton (M : ComoduleCat.{u, v, w} R C) [Subsingleton M] : IsZero M where
  unique_to N :=
    ⟨{ default := (0 : M ⟶ N)
       uniq := by
        intro f
        ext m
        rw [Subsingleton.elim m (0 : M)]
        exact map_zero f.toLinearMap }⟩
  unique_from N :=
    ⟨{ default := (0 : N ⟶ M)
       uniq := by
        intro f
        ext m
        subsingleton }⟩

/-- The named zero comodule is a zero object. -/
theorem isZero_zero : IsZero (zero R C : ComoduleCat.{u, v, w} R C) := by
  have := subsingleton_zero (R := R) (C := C)
  exact isZero_of_subsingleton (R := R) (C := C) (zero R C)

/-- Any morphism from the named zero comodule is zero. -/
theorem zero_hom_eq_zero (M : ComoduleCat.{u, v, w} R C) (f : zero R C ⟶ M) : f = 0 :=
  (isZero_zero (R := R) (C := C)).eq_of_src f 0

/-- Any morphism to the named zero comodule is zero. -/
theorem hom_zero_eq_zero (M : ComoduleCat.{u, v, w} R C) (f : M ⟶ zero R C) : f = 0 :=
  (isZero_zero (R := R) (C := C)).eq_of_tgt f 0

/-- The canonical morphism out of the named zero comodule is the zero morphism. -/
@[simp]
theorem isZero_zero_to (M : ComoduleCat.{u, v, w} R C) :
    (isZero_zero (R := R) (C := C)).to_ M = 0 :=
  zero_hom_eq_zero (R := R) (C := C) M _

/-- The canonical morphism into the named zero comodule is the zero morphism. -/
@[simp]
theorem isZero_zero_from (M : ComoduleCat.{u, v, w} R C) :
    (isZero_zero (R := R) (C := C)).from_ M = 0 :=
  hom_zero_eq_zero (R := R) (C := C) M _

/-- Morphisms from the named zero comodule are unique. -/
@[ext]
theorem zero_hom_ext {M : ComoduleCat.{u, v, w} R C} (f g : zero R C ⟶ M) : f = g :=
  (isZero_zero (R := R) (C := C)).eq_of_src f g

/-- Morphisms to the named zero comodule are unique. -/
@[ext]
theorem hom_zero_ext {M : ComoduleCat.{u, v, w} R C} (f g : M ⟶ zero R C) : f = g :=
  (isZero_zero (R := R) (C := C)).eq_of_tgt f g

/-- The category of right comodules has a zero object. -/
instance hasZeroObject : HasZeroObject (ComoduleCat.{u, v, w} R C) :=
  ⟨⟨zero R C, isZero_zero R C⟩⟩

end ComoduleCat

end TauCeti
