/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Trivial comodules

For a coalgebra `C` over `R` and a group-like element `g : GroupLike R C`, every `R`-module
`M` has a right `C`-comodule structure with coaction `m ↦ m ⊗ g`. In a bialgebra, taking
`g = 1` gives the trivial comodule. This is the comodule-theoretic analogue of the trivial
representation, and the tensor-unit ingredient for the monoidal category of comodules over a
Hopf algebra.

The main definitions are intentionally explicit named comodule structures, not global
instances: many modules carry nontrivial coactions, and typeclass search should not silently
choose the trivial one.

## Main definitions

* `TauCeti.Comodule.groupLike`: the right comodule on any `R`-module with coaction
  `m ↦ m ⊗ g`, for a group-like element `g`.
* `TauCeti.Comodule.trivial`: the bialgebraic trivial right comodule on an `R`-module.
* `TauCeti.Comodule.Hom.ofGroupLike`: any linear map is a comodule morphism between
  comodules attached to the same group-like element.
* `TauCeti.Comodule.Hom.groupLikeEquiv`: these comodule morphisms are equivalent to ordinary
  linear maps.
* `TauCeti.Comodule.Hom.ofTrivial`: any linear map is a comodule morphism between trivial
  comodules.
* `TauCeti.Comodule.Hom.trivialEquiv`: these comodule morphisms are equivalent to ordinary
  linear maps.
* `TauCeti.ComoduleCat.trivial`: the bundled tensor-unit comodule over a bialgebra.

## References

This supplies a small prerequisite for the Tau Ceti reductive-groups roadmap,
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target "Comodules over a coalgebra/Hopf
algebra", specifically the tensor-unit side of the requested tensor-product and rigid
monoidal comodule category. It uses Mathlib's bialgebra API from
`Mathlib.RingTheory.Bialgebra.GroupLike`.
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section GroupLikeDef

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The map `m ↦ m ⊗ g` attached to a group-like element `g : GroupLike R C`, as an
`R`-linear map `M →ₗ[R] M ⊗[R] C`. It serves as the coaction of the comodule structure
`Comodule.groupLike g`. -/
def groupLikeCoact (g : GroupLike R C) : M →ₗ[R] M ⊗[R] C :=
  (TensorProduct.mk R M C).flip (g : C)

/-- The right `C`-comodule structure on an `R`-module attached to a group-like element
`g : GroupLike R C`, with coaction `m ↦ m ⊗ g`.

This is not registered as a global instance: an `R`-module can carry many coactions, and the
group-like coaction should be selected explicitly with `Comodule.groupLike`. -/
@[implicit_reducible]
def groupLike (g : GroupLike R C) : Comodule R C M where
  coact := groupLikeCoact (R := R) (C := C) (M := M) g
  coassoc := by
    ext m
    simp [groupLikeCoact]
  lTensor_counit_comp_coact := by
    ext m
    simp [groupLikeCoact]

/-- The coaction attached to a group-like element sends `m` to `m ⊗ g`. -/
@[simp]
theorem groupLike_coact_apply (g : GroupLike R C) (m : M) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) :=
  rfl

/-- The coaction attached to a group-like element is the map `m ↦ m ⊗ g`. -/
@[simp]
theorem groupLike_coact (g : GroupLike R C) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    coact (R := R) (C := C) (M := M) = (TensorProduct.mk R M C).flip (g : C) :=
  rfl

/-- A linear map is automatically a comodule morphism between the comodules attached to
the same group-like element. -/
def Hom.ofGroupLike (g : GroupLike R C) (f : M →ₗ[R] N) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    Hom R C M N := by
  letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
  letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
  exact
    { toLinearMap := f
      map_coact := by
        ext m
        simp }

namespace Hom

/-- The underlying linear map of `Hom.ofGroupLike g f` is `f`. -/
@[simp]
theorem ofGroupLike_toLinearMap (g : GroupLike R C) (f : M →ₗ[R] N) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    (ofGroupLike (R := R) (C := C) g f).toLinearMap = f :=
  rfl

/-- The comodule morphism induced by a linear map between group-like comodules applies as
that linear map. -/
@[simp]
theorem ofGroupLike_apply (g : GroupLike R C) (f : M →ₗ[R] N) (m : M) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    ofGroupLike (R := R) (C := C) g f m = f m :=
  rfl

/-- The comodule morphism induced by the identity linear map between group-like comodules is
the identity comodule morphism. -/
@[simp]
theorem ofGroupLike_id (g : GroupLike R C) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    ofGroupLike (R := R) (C := C) (M := M) g LinearMap.id = Comodule.Hom.id R C M :=
  by
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    ext m
    rfl

/-- The comodule morphism induced by a composite linear map between group-like comodules is
the composite of the induced comodule morphisms. -/
@[simp]
theorem ofGroupLike_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : GroupLike R C) (h : N →ₗ[R] P) (f : M →ₗ[R] N) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    letI : Comodule R C P := groupLike (R := R) (C := C) (M := P) g
    ofGroupLike (R := R) (C := C) g (h.comp f) =
      comp (ofGroupLike (R := R) (C := C) g h) (ofGroupLike (R := R) (C := C) g f) :=
  by
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    letI : Comodule R C P := groupLike (R := R) (C := C) (M := P) g
    ext m
    simp

/-- Comodule morphisms between comodules attached to the same group-like element are exactly
ordinary linear maps. -/
def groupLikeEquiv (g : GroupLike R C) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    Hom R C M N ≃ (M →ₗ[R] N) := by
  letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
  letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
  exact
    { toFun f := f.toLinearMap
      invFun f := ofGroupLike (R := R) (C := C) g f
      left_inv f := by
        ext m
        rfl
      right_inv f := rfl }

/-- Applying `groupLikeEquiv` returns the underlying linear map. -/
@[simp]
theorem groupLikeEquiv_apply (g : GroupLike R C) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    ∀ f : Hom R C M N,
      groupLikeEquiv (R := R) (C := C) (M := M) (N := N) g f = f.toLinearMap := by
  letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
  letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
  intro f
  rfl

/-- The inverse of `groupLikeEquiv` sends a linear map to the corresponding morphism of
group-like comodules. -/
@[simp]
theorem groupLikeEquiv_symm_apply (g : GroupLike R C) (f : M →ₗ[R] N) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    (groupLikeEquiv (R := R) (C := C) (M := M) (N := N) g).symm f =
      ofGroupLike (R := R) (C := C) g f :=
  rfl

/-- Pointwise form of `groupLikeEquiv_symm_apply`. -/
@[simp]
theorem groupLikeEquiv_symm_apply_apply (g : GroupLike R C) (f : M →ₗ[R] N) (m : M) :
    letI : Comodule R C M := groupLike (R := R) (C := C) (M := M) g
    letI : Comodule R C N := groupLike (R := R) (C := C) (M := N) g
    (groupLikeEquiv (R := R) (C := C) (M := M) (N := N) g).symm f m = f m :=
  rfl

end Hom

end GroupLikeDef

section TrivialDef

variable [Semiring C] [Bialgebra R C]

/-- The trivial right `C`-comodule structure on an `R`-module.

This is not registered as a global instance: an `R`-module can carry many coactions, and the
trivial one should be selected explicitly with `Comodule.trivial`. -/
@[implicit_reducible]
def trivial : Comodule R C M :=
  groupLike (R := R) (C := C) (M := M) (1 : GroupLike R C)

section Trivial

attribute [local instance] trivial

/-- The coaction of the trivial right comodule sends `m` to `m ⊗ 1`. -/
@[simp]
theorem trivial_coact_apply (m : M) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  rfl

/-- The coaction of the trivial right comodule is the map `m ↦ m ⊗ 1`. -/
@[simp]
theorem trivial_coact :
    coact (R := R) (C := C) (M := M) = (TensorProduct.mk R M C).flip (1 : C) :=
  rfl

/-- A linear map between trivial comodules is automatically a comodule morphism. -/
def Hom.ofTrivial (f : M →ₗ[R] N) : Hom R C M N :=
  Hom.ofGroupLike (R := R) (C := C) (M := M) (N := N) (1 : GroupLike R C) f

namespace Hom

/-- The underlying linear map of `Hom.ofTrivial f` is `f`. -/
@[simp]
theorem ofTrivial_toLinearMap (f : M →ₗ[R] N) : (ofTrivial (R := R) (C := C) f).toLinearMap = f :=
  ofGroupLike_toLinearMap (R := R) (C := C) (1 : GroupLike R C) f

/-- The comodule morphism induced by a linear map between trivial comodules applies as that
linear map. -/
@[simp]
theorem ofTrivial_apply (f : M →ₗ[R] N) (m : M) :
    ofTrivial (R := R) (C := C) f m = f m :=
  ofGroupLike_apply (R := R) (C := C) (1 : GroupLike R C) f m

/-- The comodule morphism induced by the identity linear map between trivial comodules is
the identity comodule morphism. -/
@[simp]
theorem ofTrivial_id :
    ofTrivial (R := R) (C := C) (M := M) LinearMap.id = Comodule.Hom.id R C M :=
  ofGroupLike_id (R := R) (C := C) (M := M) (1 : GroupLike R C)

/-- The comodule morphism induced by a composite linear map between trivial comodules is the
composite of the induced comodule morphisms. -/
@[simp]
theorem ofTrivial_comp {P : Type*} [AddCommMonoid P] [Module R P] (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ofTrivial (R := R) (C := C) (g.comp f) =
      comp (ofTrivial (R := R) (C := C) g) (ofTrivial (R := R) (C := C) f) :=
  ofGroupLike_comp (R := R) (C := C) (1 : GroupLike R C) g f

/-- Comodule morphisms between trivial comodules are exactly ordinary linear maps. -/
def trivialEquiv : Hom R C M N ≃ (M →ₗ[R] N) :=
  groupLikeEquiv (R := R) (C := C) (M := M) (N := N) (1 : GroupLike R C)

/-- Applying `trivialEquiv` returns the underlying linear map. -/
@[simp]
theorem trivialEquiv_apply (f : Hom R C M N) :
    trivialEquiv (R := R) (C := C) (M := M) (N := N) f = f.toLinearMap :=
  rfl

/-- The inverse of `trivialEquiv` sends a linear map to the corresponding morphism of
trivial comodules. -/
@[simp]
theorem trivialEquiv_symm_apply (f : M →ₗ[R] N) :
    (trivialEquiv (R := R) (C := C) (M := M) (N := N)).symm f =
      ofTrivial (R := R) (C := C) f :=
  rfl

/-- Pointwise form of `trivialEquiv_symm_apply`. -/
theorem trivialEquiv_symm_apply_apply (f : M →ₗ[R] N) (m : M) :
    (trivialEquiv (R := R) (C := C) (M := M) (N := N)).symm f m = f m :=
  rfl

end Hom

end Trivial

end TrivialDef

end Comodule

namespace ComoduleCat

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The bundled trivial right comodule over a bialgebra.

This is the tensor-unit candidate for the monoidal category of right comodules: its
underlying `R`-module is `R`, and its coaction is `r ↦ r ⊗ 1`. -/
abbrev trivial : ComoduleCat.{u, v, u} R C :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  of R C R

end ComoduleCat

end TauCeti
