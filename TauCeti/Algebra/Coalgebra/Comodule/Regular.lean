/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# The regular comodule

This file packages the regular right comodule of a coalgebra as a bundled object of
`ComoduleCat`, and, when the coalgebra is finitely generated as a module, as an object of
`FGComoduleCat`. It also records the canonical morphism from the group-like comodule on
the rank-one free module `R` into the regular comodule.

This is Layer 1 infrastructure for the Tau Ceti reductive-groups roadmap target
"Comodules over a coalgebra/Hopf algebra", specifically the regular-representation part of
the finitely generated comodule category.

## Main definitions

* `TauCeti.ComoduleCat.regular`: the bundled regular right comodule.
* `TauCeti.Comodule.Hom.groupLikeToRegular`: the map `r ↦ r • g` from the group-like
  comodule on `R` into the regular comodule.
* `TauCeti.Comodule.Hom.trivialToRegular`: the bialgebraic special case `g = 1`.
* `TauCeti.FGComoduleCat.regular`: the regular comodule as a finitely generated comodule,
  when the underlying coalgebra is finitely generated as an `R`-module.

## References

This is the standard regular right comodule of a coalgebra; see Sweedler, *Hopf Algebras*,
Chapter 2. It reuses Mathlib's `GroupLike` API from
`Mathlib.RingTheory.Bialgebra.GroupLike`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

namespace Comodule

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Hom

/-- The canonical morphism from the group-like comodule on `R` attached to `g` into the
regular comodule, sending `r` to `r • g`. -/
@[expose] def groupLikeToRegular (g : GroupLike R C) :
    letI : Comodule R C R := groupLike (R := R) (C := C) (M := R) g
    Hom R C R C := by
  letI : Comodule R C R := groupLike (R := R) (C := C) (M := R) g
  exact
    { toLinearMap := LinearMap.toSpanSingleton R C (g : C)
      map_coact := by
        apply LinearMap.ext
        intro r
        simp [LinearMap.toSpanSingleton_apply, TensorProduct.smul_tmul] }

/-- The underlying linear map of `groupLikeToRegular g` sends `r` to `r • g`. -/
@[simp]
theorem groupLikeToRegular_toLinearMap (g : GroupLike R C) :
    letI : Comodule R C R := groupLike (R := R) (C := C) (M := R) g
    (groupLikeToRegular (R := R) (C := C) g).toLinearMap =
      LinearMap.toSpanSingleton R C (g : C) :=
  rfl

/-- The morphism `groupLikeToRegular g` sends `r` to `r • g`. -/
@[simp]
theorem groupLikeToRegular_apply (g : GroupLike R C) (r : R) :
    letI : Comodule R C R := groupLike (R := R) (C := C) (M := R) g
    groupLikeToRegular (R := R) (C := C) g r = r • (g : C) :=
  rfl

end Hom

end Comodule

namespace Comodule

namespace Hom

section Bialgebra

variable {R : Type u} {C : Type v} [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The canonical morphism from the trivial comodule on `R` to the regular comodule
of a bialgebra, induced by the unit map `R → C`. -/
def trivialToRegular :
    letI : Comodule R C R := trivial (R := R) (C := C) (M := R)
    Hom R C R C :=
  groupLikeToRegular (R := R) (C := C) (1 : GroupLike R C)

/-- The underlying linear map of `trivialToRegular` is `Algebra.linearMap R C`. -/
@[simp]
theorem trivialToRegular_toLinearMap :
    letI : Comodule R C R := trivial (R := R) (C := C) (M := R)
    (trivialToRegular (R := R) (C := C)).toLinearMap = Algebra.linearMap R C := by
  rw [trivialToRegular, groupLikeToRegular_toLinearMap]
  exact LinearMap.toSpanSingleton_one_eq_algebraLinearMap

/-- The morphism `trivialToRegular` sends `r` to `algebraMap R C r`. -/
@[simp]
theorem trivialToRegular_apply (r : R) :
    letI : Comodule R C R := trivial (R := R) (C := C) (M := R)
    trivialToRegular (R := R) (C := C) r = algebraMap R C r :=
  by
    letI : Comodule R C R := trivial (R := R) (C := C) (M := R)
    rw [← Algebra.linearMap_apply R C r]
    exact LinearMap.congr_fun (trivialToRegular_toLinearMap (R := R) (C := C)) r

end Bialgebra

end Hom

end Comodule

namespace ComoduleCat

section Regular

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The regular right comodule, bundled as an object of `ComoduleCat`. -/
abbrev regular : ComoduleCat.{u, v, v} R C :=
  of R C C

/-- The underlying type of the bundled regular comodule is the coalgebra itself. -/
@[simp]
theorem regular_toSemimoduleCat : (regular R C).toSemimoduleCat = SemimoduleCat.of R C :=
  rfl

/-- The coaction on the bundled regular comodule is the coalgebra comultiplication. -/
@[simp]
theorem regular_coact :
    Comodule.coact (R := R) (C := C) (M := regular R C) = Coalgebra.comul :=
  rfl

end Regular

section GroupLike

variable {R C : Type u} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The categorical morphism from the group-like comodule on `R` into the regular comodule. -/
abbrev groupLikeToRegular (g : GroupLike R C) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    of R C R ⟶ regular R C :=
  Comodule.Hom.groupLikeToRegular (R := R) (C := C) g

/-- The bundled morphism `groupLikeToRegular g` sends `r` to `r • g`. -/
@[simp]
theorem groupLikeToRegular_apply (g : GroupLike R C) (r : R) :
    letI : Comodule R C R := Comodule.groupLike (R := R) (C := C) (M := R) g
    groupLikeToRegular (R := R) (C := C) g r = r • (g : C) :=
  rfl

end GroupLike

section Bialgebra

variable {R C : Type u} [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The categorical morphism from the bundled trivial comodule into the regular comodule. -/
abbrev trivialToRegular : trivial R C ⟶ regular R C :=
  Comodule.Hom.trivialToRegular (R := R) (C := C)

/-- The bundled morphism `trivialToRegular` sends `r` to `algebraMap R C r`. -/
theorem trivialToRegular_apply (r : R) :
    trivialToRegular (R := R) (C := C) r = algebraMap R C r :=
  Comodule.Hom.trivialToRegular_apply (R := R) (C := C) r

end Bialgebra

end ComoduleCat

namespace FGComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Finite R C]

/-- The regular right comodule, bundled as a finitely generated comodule when the coalgebra is
finitely generated as an `R`-module. -/
abbrev regular : FGComoduleCat.{u, v, v} R C :=
  of (R := R) (C := C) C

/-- The ambient comodule underlying the finitely generated regular comodule is the regular
comodule. -/
@[simp]
theorem regular_obj : (regular R C : FGComoduleCat.{u, v, v} R C).obj = ComoduleCat.regular R C :=
  rfl

/-- The coaction on the finitely generated regular comodule is the coalgebra comultiplication. -/
@[simp]
theorem regular_coact :
    Comodule.coact (R := R) (C := C) (M := regular R C) = Coalgebra.comul :=
  rfl

end FGComoduleCat

end TauCeti
