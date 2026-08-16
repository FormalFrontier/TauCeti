/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.LocalFunctional
public import TauCeti.Algebra.Coalgebra.Subcomodule.Multiplication

/-!
# Multiplicativity of Tannakian local functionals

Let `H` be a bialgebra over a commutative semiring `k`, let `A` be a commutative `k`-algebra,
and let `η` be a tensor automorphism of scalar extension on finitely generated `H`-comodules.
The functional extracted from `η` on a finite subcomodule of the regular comodule is compatible
with multiplication.

More precisely, if finite regular subcomodules `N` and `P` have all their pairwise products in a
third finite regular subcomodule `Q`, then

```text
g_{η,Q}(n * p) = g_{η,N}(n) * g_{η,P}(p).
```

The proof applies naturality to the corestricted regular-comodule multiplication
`Subcomodule.mulHom` and applies the tensor law for `η` to `1 ⊗ n` and `1 ⊗ p`.
Evaluation by the counit turns multiplication in the regular comodule into multiplication in
`A`. Together with the gluing construction and a unit law still to be developed, this supplies
the algebra-map law needed to reconstruct an `A`-valued point from a tensor automorphism.

## Main declarations

* `TauCeti.Tannaka.regularMulHom`: multiplication of two finite regular subcomodules, corestricted
  to a finite regular subcomodule containing their products and packaged in `FGComoduleCat`.
* `TauCeti.Tannaka.localFunctional_mul`: the extracted local functionals preserve these products.

## References

* J. S. Milne, *Algebraic Groups* (2017), section 9.4.
* `Mathlib/RepresentationTheory/Tannaka.lean`: `mulRepHom` and
  `map_mul_toRightFDRepComp` supply the formal pattern of a categorical multiplication morphism
  followed by naturality and the monoidal tensor law, adapted here to comodules.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

attribute [local instance] Comodule.tensor

section RegularMulHom

variable (k H : Type u) [CommSemiring k] [Semiring H] [Bialgebra k H] [Module.Flat k H]

/-- Multiplication of two finite regular subcomodules, corestricted to a finite regular
subcomodule containing all their pairwise products. -/
noncomputable def regularMulHom
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1) :
    finiteRegularObject k H N ⊗ finiteRegularObject k H P ⟶ finiteRegularObject k H Q := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  letI : Module.Finite k P.1 := Subcomodule.mem_finiteSubcomodules.mp P.2
  letI : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  exact FGComoduleCat.ofHom (Subcomodule.mulHom N.1 P.1 Q.1 h)

/-- The linear map underlying corestricted multiplication of finite regular subcomodules is the
one underlying `Subcomodule.mulHom`. -/
@[simp]
theorem regularMulHom_toLinearMap
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1) :
    (regularMulHom k H N P Q h).hom.toLinearMap =
      (Subcomodule.mulHom N.1 P.1 Q.1 h).toLinearMap := by
  rfl

end RegularMulHom

section LocalMultiplicativity

variable (k H A : Type u) [CommSemiring k] [Semiring H] [Bialgebra k H]
  [Module.Flat k H] [CommSemiring A] [Algebra k A]

private theorem counitEvaluation_mul
    (N P Q : Subcomodule k H H)
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q)
    (x : A ⊗[k] N) (y : A ⊗[k] P) :
    counitEvaluation k H A Q
        ((Subcomodule.mulHom N P Q h).toLinearMap.baseChange A
          ((TensorProduct.AlgebraTensorModule.distribBaseChange k A N P).symm
            (x ⊗ₜ[A] y))) =
      counitEvaluation k H A N x * counitEvaluation k H A P y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, hx, hx', map_add, add_mul]
  | tmul a n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hy', map_add, mul_add]
      | tmul b p =>
          rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
            LinearMap.baseChange_tmul]
          have hcoe : (Subcomodule.mulHom N P Q h).toLinearMap (n ⊗ₜ[k] p) =
              Subcomodule.mulHom N P Q h (n ⊗ₜ[k] p) :=
            congrFun (Comodule.Hom.coe_toLinearMap (Subcomodule.mulHom N P Q h)) _
          rw [hcoe]
          rw [counitEvaluation_tmul, counitEvaluation_tmul, counitEvaluation_tmul]
          have hmul : ((Subcomodule.mulHom N P Q h (n ⊗ₜ[k] p) : Q) : H) =
              (n : H) * (p : H) := by
            exact Subcomodule.mulHom_tmul N P Q h n p
          rw [hmul]
          rw [Bialgebra.counit_mul, map_mul]
          ring

/-- Local functionals extracted from a tensor automorphism preserve products whenever the
products of the two source subcomodules lie in the chosen target subcomodule. -/
@[simp high]
theorem localFunctional_mul
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1)
    (n : N.1) (p : P.1) :
    localFunctional k H A η Q ⟨(n : H) * (p : H), h n p⟩ =
      localFunctional k H A η N n * localFunctional k H A η P p := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  let _ : Module.Finite k P.1 := Subcomodule.mem_finiteSubcomodules.mp P.2
  let _ : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  let q : Q.1 := ⟨(n : H) * (p : H), h n p⟩
  have hq : (regularMulHom k H N P Q h).hom.toLinearMap (n ⊗ₜ[k] p) = q := by
    rw [regularMulHom_toLinearMap]
    apply Subtype.ext
    exact Subcomodule.mulHom_tmul N.1 P.1 Q.1 h n p
  have hnat := LinearMap.congr_fun
    (scalarExtensionComponent_natural k H A η (regularMulHom k H N P Q h))
      (1 ⊗ₜ[k] (n ⊗ₜ[k] p))
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at hnat
  rw [hq] at hnat
  have htensor := scalarExtensionComponent_tensor k H A η
    (finiteRegularObject k H N) (finiteRegularObject k H P)
      (1 ⊗ₜ[k] n) (1 ⊗ₜ[k] p)
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul] at htensor
  rw [localFunctional_apply, localFunctional_apply, localFunctional_apply]
  rw [← hnat, htensor, regularMulHom_toLinearMap]
  exact counitEvaluation_mul k H A N.1 P.1 Q.1 h _ _

end LocalMultiplicativity

end TauCeti.Tannaka
