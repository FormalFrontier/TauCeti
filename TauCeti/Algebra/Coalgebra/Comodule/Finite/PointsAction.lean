/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Tensor compatibility of point actions on finite comodules

Let `H` be a bialgebra over a commutative semiring `R`, and let `A` be a commutative
`R`-algebra. The scalar-extension assignment sends a finitely generated `H`-comodule `M` to
`A ⊗[R] M`.

Every algebra homomorphism `g : H →ₐ[R] A` acts naturally on each scalar extension. This file
specializes the general comodule tensor identity to the monoidal category of finitely generated
comodules. Together with the general simplification theorem `Comodule.endOfPoint_trivial`, it
shows that the actions preserve the canonical tensor comparison and act identically on the tensor
unit.

These are the two nontrivial monoidal identities needed for the intended later packaging of a
point as a tensor automorphism. This file does not construct a fiber functor or prove the
reconstruction theorem.

## Main declarations

* `TauCeti.Tannaka.endOfPoint_tensor`: the action preserves tensor products under the canonical
  scalar-extension comparison.
* `TauCeti.Comodule.endOfPoint_trivial`: the action is the identity on every trivial comodule.

## References

These identities are the forward-direction monoidal compatibility in Tannakian reconstruction for
affine group schemes; see J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4. This advances
Layer 1, "Tannakian reconstruction", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- A point action on finitely generated comodules preserves tensor products. -/
theorem endOfPoint_tensor (g : H →ₐ[R] A) (M N : FGComoduleCat.{u, v, u} R H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ∘ₗ
        TensorProduct.map (Comodule.endOfPoint M g) (Comodule.endOfPoint N g) =
      Comodule.endOfPoint (M ⊗ N : FGComoduleCat.{u, v, u} R H) g ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
  let _ : Comodule R H (M ⊗[R] N) :=
    inferInstanceAs (Comodule R H (M ⊗ N : FGComoduleCat.{u, v, u} R H))
  exact Comodule.endOfPoint_tensor_of_coact_eq (FGComoduleCat.tensor_coact R H M N) g

end TauCeti.Tannaka
