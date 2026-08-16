/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Weight spaces by corestriction to a monoid algebra

Given a right `C`-comodule `V` and a coalgebra morphism `π : C → R[X]`, corestriction along `π`
makes `V` an `R[X]`-comodule. The resulting comodule decomposes into the weight submodules of
`TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic`. This file names that decomposition:

`TauCeti.DiagonalizableGroup.weightSpace V π x` is the `x`-weight submodule of the corestricted
comodule, and `V` is the internal direct sum of these submodules.

When `X` is a commutative group, `C` is the coordinate bialgebra of an affine group scheme `G`,
and `π` underlies a bialgebra morphism, it is the coordinate morphism of a homomorphism
`D(X) → G`, and these are the weight spaces of a representation restricted along that
homomorphism. The statement identifying the action of a point of `D(X)` as multiplication by the
value of the character therefore takes a `BialgHom`.

## Main definitions

* `TauCeti.DiagonalizableGroup.weightSpace`: the `x`-weight submodule after corestricting a
  comodule along a coalgebra morphism to `R[X]`.

## Main results

* `TauCeti.DiagonalizableGroup.isInternal_weightSpace`: **the corestricted comodule is the internal
  direct sum of its weight submodules.**
* `TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot`: a comodule that is finitely
  generated as a module has finitely many nonzero weight submodules after corestriction.
* `TauCeti.DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace`: a monoid-algebra point acts on
  the `x`-weight submodule by multiplication by its value on `x`; for a commutative group `X`,
  this is the corresponding action of a point of `D(X)`.

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

/-- The `x`-weight submodule obtained by corestricting a right `C`-comodule `V` along a coalgebra
morphism `π : C →ₗc[R] R[X]`.

If `X` is a commutative group, `π` underlies the coordinate-bialgebra morphism of a homomorphism
`D(X) → G`, and `V` is a representation of `G`, this is the submodule on which `D(X)` acts
through the character `x`. -/
noncomputable def weightSpace (π : C →ₗc[R] MonoidAlgebra R X) (x : X) :
    Submodule R V :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.weightSpace R X V x

variable {V}

/-- Membership in the `x`-weight submodule, in terms of the coaction of the original comodule:
pushing the coaction of `v` through `π` must give `v ⊗ x`. -/
@[simp]
theorem mem_weightSpace {π : C →ₗc[R] MonoidAlgebra R X} {x : X} {v : V} :
    v ∈ weightSpace V π x ↔
      TensorProduct.map LinearMap.id π.toLinearMap
          (Comodule.coact (R := R) (C := C) (M := V) v) =
        v ⊗ₜ[R] MonoidAlgebra.single x (1 : R) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.mem_weightSpace

variable (V)

/-- **A comodule corestricted along a coalgebra morphism to `R[X]` is the internal direct sum of
its weight submodules.** -/
theorem isInternal_weightSpace (π : C →ₗc[R] MonoidAlgebra R X) :
    DirectSum.IsInternal (weightSpace V π) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.isInternal_weightSpace R X V

/-- **A comodule that is finitely generated as a module has only finitely many nonzero weight
submodules after corestriction.** -/
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

/-- Acting through a composite point agrees on pure tensors with first corestricting the coaction
along the bialgebra morphism and then applying the point. -/
theorem endOfPoint_tmul_comp (π : C →ₐc[R] MonoidAlgebra R X)
    (f : MonoidAlgebra R X →ₐ[R] A) (a : A) (v : V) :
    Comodule.endOfPoint V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)) (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A
        (LinearMap.lTensor V f.toLinearMap
          (TensorProduct.map LinearMap.id (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap
            (Comodule.coact (R := R) (C := C) (M := V) v))) := by
  have hπ : (π : C →ₐ[R] MonoidAlgebra R X).toLinearMap =
      (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_coe]
    exact BialgHom.toAlgHom_toLinearMap π
  rw [Comodule.endOfPoint_tmul]
  congr 2
  rw [LinearMap.lTensor_map, AlgHom.comp_toLinearMap, hπ, LinearMap.lTensor_def]

/-- **A monoid-algebra point acts on the `x`-weight submodule by its value on `x`.**

When `X` is a commutative group and the bialgebras are coordinate rings, the point of `G` in
question is the composite of the homomorphism `D(X) → G` with the given point of `D(X)`, whose
coordinate morphism is `f ∘ π`. -/
theorem endOfPoint_tmul_of_mem_weightSpace (π : C →ₐc[R] MonoidAlgebra R X)
    (f : MonoidAlgebra R X →ₐ[R] A) (a : A) {x : X} {v : V}
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) x) :
    Comodule.endOfPoint V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)) (a ⊗ₜ[R] v) =
      (a * f (MonoidAlgebra.single x (1 : R))) ⊗ₜ[R] v := by
  rw [endOfPoint_tmul_comp, mem_weightSpace.mp hv]
  simp [TensorProduct.smul_tmul']

end Points

end DiagonalizableGroup

end TauCeti
