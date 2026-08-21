/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal

/-!
# Local functionals from tensor automorphisms

Let `H` be a bialgebra over a commutative semiring `k`, and let `A` be a commutative
`k`-algebra. A tensor automorphism `η` of scalar extension on the finitely generated
`H`-comodules acts, in particular, on every finite subcomodule `N` of the regular comodule `H`.
Applying that component to `1 ⊗ n` and then applying the counit to the `N`-factor gives a linear
functional

```text
g_{η,N} : N → A.
```

Naturality of `η` under inclusions of finite subcomodules makes these functionals compatible.
They therefore form exactly the local data needed to reconstruct one linear map `H → A` from
the directed union of the finite subcomodules. The separate directed-union construction can then
glue them; tensor and unit compatibility will supply the algebra-map laws.

## Main declarations

* `TauCeti.Tannaka.counitEvaluation`: counit evaluation after scalar extension on a regular
  subcomodule.
* `TauCeti.Tannaka.localFunctional`: the functional extracted from one finite subcomodule.
* `TauCeti.Tannaka.localFunctional_eq_comp_inclusion`: compatibility under inclusion.
* `TauCeti.Tannaka.localFunctional_fgPointTensorIso`: a point recovers its restriction to every
  finite subcomodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
* `Mathlib/RepresentationTheory/Tannaka.lean`: the naturality and monoidal-transport pattern is
  adapted here from the proof of `map_mul_toRightFDRepComp`.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v w

section FiniteRegularObject

variable (k H : Type u) [CommSemiring k] [Semiring H] [Bialgebra k H] [Module.Flat k H]

/-- A finite subcomodule of the regular comodule, bundled as an object of the finite comodule
category. -/
noncomputable abbrev finiteRegularObject
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    FGComoduleCat.{u, u, u} k H :=
  ⟨ComoduleCat.of k H N.1, Subcomodule.mem_finiteSubcomodules.mp N.2⟩

end FiniteRegularObject

section CounitEvaluation

variable (k : Type u) [CommSemiring k]
variable (H : Type v) [AddCommMonoid H] [Module k H] [Coalgebra k H]
variable (A : Type w) [CommSemiring A] [Algebra k A]

/-- Evaluation after scalar extension by applying the counit on a regular subcomodule. -/
noncomputable def counitEvaluation (N : Subcomodule k H H) : A ⊗[k] N →ₗ[A] A :=
  TauCeti.Module.Dual.baseChangeEvaluation (R := k) (M := N) (A := A)
    (1 ⊗ₜ[k] ((Coalgebra.counit (R := k) (A := H)).comp
      (SMulMemClass.subtype N)))

/-- Counit evaluation on a pure scalar-extension tensor. -/
@[simp]
theorem counitEvaluation_tmul (N : Subcomodule k H H) (a : A) (n : N) :
    counitEvaluation k H A N (a ⊗ₜ[k] n) =
      a * algebraMap k A (Coalgebra.counit (R := k) (A := H) (n : H)) := by
  simp [counitEvaluation]

/-- Counit evaluation is the base change of the counit restricted to the regular
subcomodule. -/
theorem counitEvaluation_apply (N : Subcomodule k H H) (z : A ⊗[k] N) :
    counitEvaluation k H A N z =
      (TensorProduct.AlgebraTensorModule.rid k A A)
        (((Coalgebra.counit (R := k) (A := H)).comp
          (SMulMemClass.subtype N)).baseChange A z) := by
  simp only [counitEvaluation, TauCeti.Module.Dual.baseChangeEvaluation_one_tmul,
    Module.Dual.baseChange,
    LinearMap.compRight_apply, LinearMap.baseChangeHom_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe]

end CounitEvaluation

section LocalFunctional

variable (k H A : Type u) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [Module.Flat k H] [CommSemiring A] [Algebra k A]

/-- Inclusion of finite regular subcomodules as a morphism in the finite comodule category. -/
noncomputable def regularInclusion
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) :
    finiteRegularObject k H N ⟶ finiteRegularObject k H Q := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  letI : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  refine FGComoduleCat.ofHom (R := k) (C := H)
    { toLinearMap := Submodule.inclusion hNQ
      map_coact := ?_ }
  apply LinearMap.ext
  intro n
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (SMulMemClass.subtype Q.1) Subtype.val_injective
  have hcomp : (SMulMemClass.subtype Q.1).comp (Submodule.inclusion hNQ) =
      SMulMemClass.subtype N.1 := by
    ext
    rfl
  calc
    (SMulMemClass.subtype Q.1).rTensor H
        (TensorProduct.map (Submodule.inclusion hNQ) LinearMap.id
          (Comodule.coact (R := k) (C := H) (M := N.1) n)) =
        (SMulMemClass.subtype N.1).rTensor H
          (Comodule.coact (R := k) (C := H) (M := N.1) n) := by
      rw [LinearMap.rTensor_def, LinearMap.rTensor_def, TensorProduct.map_map,
        LinearMap.comp_id, hcomp]
    _ = Comodule.coact (R := k) (C := H) (M := H) n :=
      Subcomodule.subtype_rTensor_coact N.1 n
    _ = (SMulMemClass.subtype Q.1).rTensor H
        (Comodule.coact (R := k) (C := H) (M := Q.1)
          (Submodule.inclusion hNQ n)) :=
      (Subcomodule.subtype_rTensor_coact Q.1 (Submodule.inclusion hNQ n)).symm

/-- The inclusion of finite regular subcomodules is the ordinary subtype inclusion. -/
@[simp]
theorem regularInclusion_apply
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) (n : N.1) :
    regularInclusion k H hNQ n = ⟨n, hNQ n.2⟩ :=
  by
    unfold regularInclusion
    rfl

/-- The linear map underlying inclusion of finite regular subcomodules is the ordinary submodule
inclusion. -/
@[simp]
theorem regularInclusion_toLinearMap
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) :
    (regularInclusion k H hNQ).hom.toLinearMap = Submodule.inclusion hNQ := by
  unfold regularInclusion
  rfl

/-- The linear functional on a finite subcomodule of the regular comodule extracted from a
tensor automorphism. It applies the automorphism to `1 ⊗ n` and then evaluates the regular
coordinate by the counit. -/
noncomputable def localFunctional
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    N.1 →ₗ[k] A := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  exact ((counitEvaluation k H A N.1).restrictScalars k).comp <|
    ((scalarExtensionComponent k H A η
      (finiteRegularObject k H N)).restrictScalars k).comp
      (TensorProduct.mk k A N.1 (1 : A))

/-- Evaluation formula for the functional extracted from a finite regular subcomodule. -/
@[simp]
theorem localFunctional_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A η N n =
      counitEvaluation k H A N.1
        (scalarExtensionComponent k H A η (finiteRegularObject k H N) (1 ⊗ₜ[k] n)) :=
  by
    unfold localFunctional
    rfl

/-- The local functionals extracted from a tensor automorphism agree under inclusion of finite
subcomodules. -/
theorem localFunctional_eq_comp_inclusion
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hNQ : N.1 ≤ Q.1) :
    localFunctional k H A η N =
      (localFunctional k H A η Q).comp (Submodule.inclusion hNQ) := by
  apply LinearMap.ext
  intro n
  rw [LinearMap.comp_apply, localFunctional_apply, localFunctional_apply]
  have happ := LinearMap.congr_fun
    (scalarExtensionComponent_natural k H A η (regularInclusion k H hNQ)) (1 ⊗ₜ[k] n)
  simp only [regularInclusion_toLinearMap, LinearMap.comp_apply,
    LinearMap.baseChange_tmul] at happ
  rw [← happ]
  have hcounit (x : A ⊗[k] N.1) :
      counitEvaluation k H A Q.1 ((Submodule.inclusion hNQ).baseChange A x) =
        counitEvaluation k H A N.1 x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul a m =>
        rw [LinearMap.baseChange_tmul,
          counitEvaluation_tmul k H A Q.1 a (Submodule.inclusion hNQ m),
          counitEvaluation_tmul k H A N.1 a m]
        rfl
  exact (hcounit _).symm

end LocalFunctional

section Point

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- For a tensor automorphism induced by an algebra-valued point `g`, the local functional is
the restriction of `g` to the chosen finite subcomodule of the regular comodule. -/
@[simp]
theorem localFunctional_fgPointTensorIso
    (g : WithConv (H →ₐ[k] A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A (fgPointTensorIso k H A g) N n = g.ofConv n := by
  rw [← fgPointTensorIsoHom_apply]
  rw [localFunctional_apply, fgPointTensorIsoHom_apply,
    scalarExtensionComponent_fgPointTensorIso]
  rw [Comodule.pointsAction_toLinearMap]
  unfold counitEvaluation
  let φ : Module.Dual k N.1 :=
    (Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N.1)
  have hcoeff : Comodule.matrixCoefficient (R := k) (C := H) φ n = (n : H) := by
    simpa only [φ] using Comodule.matrixCoefficient_counit_comp_subtype
      (R := k) (C := H) N.1 n
  simpa only [φ, one_mul, hcoeff] using
    Comodule.baseChangeEvaluation_endOfPoint_tmul g.ofConv (1 : A) (1 : A) φ n

end Point

end TauCeti.Tannaka
