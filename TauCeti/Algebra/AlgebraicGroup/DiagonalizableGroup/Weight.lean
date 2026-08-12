/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra

/-!
# Weights of a representation along a homomorphism from a diagonalizable group

A homomorphism of affine group schemes `D(X) → G` is a morphism `π : H → R[X]` of the coordinate
bialgebras, and a representation of `G` is a right `H`-comodule `V`. Restricting the
representation along `π` corestricts the comodule along `π`, and the resulting `R[X]`-comodule
decomposes into the weight submodules of
`TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra`. This file names that decomposition:

`TauCeti.DiagonalizableGroup.weightSpace V π x` is the submodule of `V` on which `D(X)` acts
through the character `x`, and `V` is the internal direct sum of these submodules.

Only the coalgebra structure of `π` enters the decomposition, so the definition and the
decomposition theorems take a `CoalgHom`. The statement identifying the action of a point of
`D(X)` as multiplication by the value of the character does use that `π` is a morphism of
bialgebras, since it speaks about points, and takes a `BialgHom`.

## Main definitions

* `TauCeti.DiagonalizableGroup.weightSpace`: the `x`-weight submodule of a representation of `G`
  restricted along a homomorphism `D(X) → G`.

## Main results

* `TauCeti.DiagonalizableGroup.isInternal_weightSpace`: **a representation restricted along a
  homomorphism from a diagonalizable group is the internal direct sum of its weight submodules.**
* `TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot`: a representation that is finitely
  generated as a module has finitely many weights.
* `TauCeti.DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace`: a point of `D(X)` acts on the
  `x`-weight submodule by multiplication by the value of the character `x` at that point.

## Roadmap

This is the restriction step that Layer 7 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for
in its split root-datum target: the roots of a split pair `(G, T)` are the nonzero weights of the
adjoint representation of `G` restricted along the split maximal torus `T`. This file supplies
that restriction for an arbitrary homomorphism from a diagonalizable group, carrying no torus,
maximality or closed-immersion hypotheses;
`TauCeti/Algebra/AlgebraicGroup/Tangent/RootSpace.lean` performs the specialization to the
adjoint representation.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c and §21.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace DiagonalizableGroup

attribute [local instance] Classical.decEq

section Decomposition

variable {R : Type*} [CommSemiring R]
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {X : Type*}
variable (V : Type*) [AddCommMonoid V] [Module R V] [Comodule R C V]

/-- The `x`-weight submodule of a right `C`-comodule `V` along a coalgebra morphism
`π : C →ₗc[R] R[X]`.

Geometrically `π` is the coordinate morphism of a homomorphism `D(X) → G` of affine group schemes
and `V` is a representation of `G`; this is the submodule on which `D(X)` acts through the
character `x`. -/
noncomputable def weightSpace (π : C →ₗc[R] MonoidAlgebra R X) (x : X) :
    Submodule R V :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.weightSpace R X V x

variable {V}

/-- Membership in the `x`-weight submodule, in terms of the coaction of the original comodule:
pushing the coaction of `v` through `π` must give `v ⊗ x`. -/
theorem mem_weightSpace {π : C →ₗc[R] MonoidAlgebra R X} {x : X} {v : V} :
    v ∈ weightSpace V π x ↔
      TensorProduct.map LinearMap.id π.toLinearMap
          (Comodule.coact (R := R) (C := C) (M := V) v) =
        v ⊗ₜ[R] MonoidAlgebra.single x (1 : R) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.mem_weightSpace

variable (V)

/-- **A representation restricted along a homomorphism from a diagonalizable group is the internal
direct sum of its weight submodules.** -/
theorem isInternal_weightSpace (π : C →ₗc[R] MonoidAlgebra R X) :
    DirectSum.IsInternal (weightSpace V π) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.isInternal_weightSpace R X V

/-- **A representation that is finitely generated as a module has only finitely many weights.** -/
theorem finite_setOf_weightSpace_ne_bot [Module.Finite R V] (π : C →ₗc[R] MonoidAlgebra R X) :
    {x : X | weightSpace V π x ≠ ⊥}.Finite :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.finite_setOf_weightSpace_ne_bot R X V

end Decomposition

section Points

variable {R : Type*} [CommSemiring R]
variable {C : Type*} [Semiring C] [Bialgebra R C]
variable {X : Type*} [Monoid X]
variable (V : Type*) [AddCommMonoid V] [Module R V] [Comodule R C V]
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- **A point of `D(X)` acts on the `x`-weight submodule by the value of the character `x`.**

The point of `G` in question is the composite of the homomorphism `D(X) → G` with the given point
of `D(X)`, whose coordinate morphism is `f ∘ π`. -/
theorem endOfPoint_tmul_of_mem_weightSpace (π : C →ₐc[R] MonoidAlgebra R X)
    (f : MonoidAlgebra R X →ₐ[R] A) (a : A) {x : X} {v : V}
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) x) :
    Comodule.endOfPoint V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)) (a ⊗ₜ[R] v) =
      (a * f (MonoidAlgebra.single x (1 : R))) ⊗ₜ[R] v := by
  have hmap : ∀ t : V ⊗[R] C,
      LinearMap.lTensor V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)).toLinearMap t =
        LinearMap.lTensor V f.toLinearMap
          (TensorProduct.map LinearMap.id (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v' c => simp
    | add s t hs ht => simp only [map_add, hs, ht]
  rw [Comodule.endOfPoint_tmul, hmap, mem_weightSpace.mp hv]
  simp [TensorProduct.smul_tmul']

end Points

end DiagonalizableGroup

end TauCeti
