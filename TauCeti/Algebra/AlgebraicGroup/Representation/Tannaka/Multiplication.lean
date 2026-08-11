/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.LocalFunctional
public import TauCeti.Algebra.Coalgebra.Subcomodule.Multiplication

/-!
# Multiplicativity of Tannakian local functionals

Let `H` be a commutative Hopf algebra over a field `k`, let `A` be a commutative `k`-algebra,
and let `η` be a tensor automorphism of scalar extension on finite-dimensional `H`-comodules.
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
`A`. Together with the separately developed unit law and gluing construction, this is the
algebra-map law needed to reconstruct an `A`-valued point from a tensor automorphism.

## Main declarations

* `TauCeti.Tannaka.regularMul`: multiplication of two finite regular subcomodules, corestricted
  to a finite regular subcomodule containing their products.
* `TauCeti.Tannaka.localFunctional_mul`: the extracted local functionals preserve these products.

## References

* J. S. Milne, *Algebraic Groups* (2017), section 9.4.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

attribute [local instance] Comodule.tensor

/-- Multiplication of two finite regular subcomodules, corestricted to a finite regular
subcomodule containing all their pairwise products. -/
noncomputable def regularMul
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1) :
    finiteRegularObject k H N ⊗ finiteRegularObject k H P ⟶ finiteRegularObject k H Q := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  letI : Module.Finite k P.1 := Subcomodule.mem_finiteSubcomodules.mp P.2
  letI : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  exact FGComoduleCat.ofHom (Subcomodule.mulHom N.1 P.1 Q.1 h)

/-- Corestricted multiplication of finite regular subcomodules sends a pure tensor to the
product of its factors. -/
@[simp]
theorem regularMul_tmul
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1)
    (n : N.1) (p : P.1) :
    ((regularMul k H N P Q h (n ⊗ₜ[k] p) : Q.1) : H) = (n : H) * (p : H) := by
  exact Subcomodule.mulHom_tmul N.1 P.1 Q.1 h n p

/-- The underlying linear map of corestricted multiplication is the base map used by scalar
extension. -/
@[simp]
theorem regularMul_toLinearMap
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1) :
    (regularMul k H N P Q h).hom.toLinearMap =
      (Subcomodule.mulHom N.1 P.1 Q.1 h).toLinearMap := by
  rfl

private noncomputable def counitEvaluation
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    A ⊗[k] N.1 →ₗ[A] A :=
  TauCeti.Module.Dual.baseChangeEvaluation (R := k) (M := N.1) (A := A)
    (1 ⊗ₜ[k] ((Coalgebra.counit (R := k) (A := H)).comp
      (SMulMemClass.subtype N.1)))

@[simp]
private theorem counitEvaluation_tmul
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (a : A) (n : N.1) :
    counitEvaluation k H A N (a ⊗ₜ[k] n) =
      a * algebraMap k A (Coalgebra.counit (R := k) (A := H) (n : H)) := by
  simp [counitEvaluation]

private theorem counitEvaluation_mul
    (N P Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (h : ∀ (n : N.1) (p : P.1), (n : H) * (p : H) ∈ Q.1)
    (x : A ⊗[k] N.1) (y : A ⊗[k] P.1) :
    counitEvaluation k H A Q
        ((Subcomodule.mulHom N.1 P.1 Q.1 h).toLinearMap.baseChange A
          ((TensorProduct.AlgebraTensorModule.distribBaseChange k A N.1 P.1).symm
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
          change counitEvaluation k H A Q
              ((a * b) ⊗ₜ[k] Subcomodule.mulHom N.1 P.1 Q.1 h (n ⊗ₜ[k] p)) = _
          rw [counitEvaluation_tmul, counitEvaluation_tmul, counitEvaluation_tmul]
          rw [show Coalgebra.counit (R := k) (A := H)
              ((Subcomodule.mulHom N.1 P.1 Q.1 h (n ⊗ₜ[k] p) : Q.1) : H) =
                Coalgebra.counit (R := k) (A := H) ((n : H) * (p : H)) by
            rw [Subcomodule.mulHom_tmul]]
          rw [Bialgebra.counit_mul, map_mul]
          ring

/-- Local functionals extracted from a tensor automorphism preserve products whenever the
products of the two source subcomodules lie in the chosen target subcomodule. -/
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
  have hq : (regularMul k H N P Q h).hom.toLinearMap (n ⊗ₜ[k] p) = q := by
    apply Subtype.ext
    exact regularMul_tmul k H N P Q h n p
  have hnat := LinearMap.congr_fun
    (scalarExtensionComponent_natural k H A η (regularMul k H N P Q h))
      (1 ⊗ₜ[k] (n ⊗ₜ[k] p))
  change (regularMul k H N P Q h).hom.toLinearMap.baseChange A
      (scalarExtensionComponent k H A η
        (finiteRegularObject k H N ⊗ finiteRegularObject k H P)
          (1 ⊗ₜ[k] (n ⊗ₜ[k] p))) =
    scalarExtensionComponent k H A η (finiteRegularObject k H Q)
      ((regularMul k H N P Q h).hom.toLinearMap.baseChange A
        (1 ⊗ₜ[k] (n ⊗ₜ[k] p))) at hnat
  rw [LinearMap.baseChange_tmul, hq] at hnat
  have htensor := scalarExtensionComponent_tensor k H A η
    (finiteRegularObject k H N) (finiteRegularObject k H P)
      (1 ⊗ₜ[k] n) (1 ⊗ₜ[k] p)
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul] at htensor
  rw [localFunctional_apply, localFunctional_apply, localFunctional_apply]
  change counitEvaluation k H A Q
      (finiteRegularComponent k H A η Q
        (1 ⊗ₜ[k] (⟨(n : H) * (p : H), h n p⟩ : Q.1))) =
    counitEvaluation k H A N
        (finiteRegularComponent k H A η N (1 ⊗ₜ[k] n)) *
      counitEvaluation k H A P
        (finiteRegularComponent k H A η P (1 ⊗ₜ[k] p))
  rw [show (⟨(n : H) * (p : H), h n p⟩ : Q.1) = q by rfl]
  simp only [finiteRegularComponent]
  change counitEvaluation k H A Q
      (scalarExtensionComponent k H A η (finiteRegularObject k H Q)
        (1 ⊗ₜ[k] q)) =
    counitEvaluation k H A N
        (scalarExtensionComponent k H A η (finiteRegularObject k H N) (1 ⊗ₜ[k] n)) *
      counitEvaluation k H A P
        (scalarExtensionComponent k H A η (finiteRegularObject k H P) (1 ⊗ₜ[k] p))
  rw [← hnat, htensor, regularMul_toLinearMap]
  exact counitEvaluation_mul k H A N P Q h _ _

end TauCeti.Tannaka
