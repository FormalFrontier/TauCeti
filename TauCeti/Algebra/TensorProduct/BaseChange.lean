/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: `Mathlib.RingTheory.TensorProduct.Basic` carries the `L`-algebra structure
-- `Algebra.TensorProduct.leftAlgebra` on `L ⊗[K] A`, which occurs in both types below.
-- `Mathlib.LinearAlgebra.TensorProduct.Opposite` carries the algebra structures on `Aᵐᵒᵖ` and
-- `(L ⊗[K] A)ᵐᵒᵖ` in the type of `baseChangeOpAlgEquiv`, and the compiler needs
-- `Algebra.TensorProduct.opAlgEquiv`, used in its body, to be public.
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic
-- Non-public: neither appears in the type of an exported declaration. Mathlib's
-- `distribBaseChange`, `cancelBaseChange`, `algEquivOfLinearEquivTensorProduct` and `congr` are
-- used only inside definition bodies and proofs, and no definition below is `@[expose]`d.
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change is compatible with `⊗`, with `ᵐᵒᵖ`, and with itself

Scalar extension along a commutative `K`-algebra `L` distributes over the tensor product, commutes
with passing to the opposite algebra, and composes in stages:

* `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`:
  `L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B)`;
* `TauCeti.Algebra.TensorProduct.baseChangeOpAlgEquiv`: `L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ`;
* `TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`:
  `M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A` for a tower `K → L → M`.

None is reproved from scratch: the first and third upgrade Mathlib's linear equivalences
`TensorProduct.AlgebraTensorModule.distribBaseChange` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` to algebra equivalences, and the second
composes `AlgEquiv.toOpposite` with Mathlib's `Algebra.TensorProduct.opAlgEquiv`.

## Implementation notes

All three equivalences are opaque: their bodies are not `@[expose]`d, and the `_tmul` and
`_symm_tmul` simp lemmas below are the whole public interface, in both directions.

Mathlib's `Algebra.TensorProduct.cancelBaseChange` is the third equivalence for a **commutative**
algebra being extended; the algebras this file exists to serve are central simple, so they are not
commutative in general, and the hypothesis has to go along with the chance to reuse that
definition.

These are statements about scalar extension as such, with no central-simplicity hypotheses. Their
first consumer is `TauCeti/Algebra/CentralSimple/BaseChange.lean`, which re-exports them for
`TauCeti/Algebra/BrauerGroup/BaseChange.lean`, where they are what makes base change respect the
multiplication and the inversion of Brauer classes and compose along a tower of fields.

## References

These are the compatibilities asked for by the **Base change preserves central simplicity, then
is a homomorphism** bullet of Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- **Base change distributes over the tensor product**: extending `A ⊗[K] B` to `L` is the same as
extending each factor and tensoring over `L`.

This is Mathlib's linear equivalence `TensorProduct.AlgebraTensorModule.distribBaseChange` upgraded
to an algebra equivalence; the multiplicativity is checked on pure tensors, where both sides are
`(l₁ * l₂) ⊗ₜ (a₁ * a₂)` tensored with `1 ⊗ₜ (b₁ * b₂)`. Nothing beyond the displayed
commutative-semiring and algebra hypotheses on `K`, `L`, `A` and `B` is assumed: in particular
neither factor has to be central or simple. -/
def baseChangeTensorAlgEquiv :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K L A B)
    (fun l₁ l₂ z₁ z₂ => by
      induction z₁ using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [TensorProduct.tmul_add, add_mul, hx, hy]
      | tmul a₁ b₁ =>
        induction z₂ using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [TensorProduct.tmul_add, mul_add, hx, hy]
        | tmul a₂ b₂ => simp [Algebra.TensorProduct.tmul_mul_tmul])
    (by simp [Algebra.TensorProduct.one_def])

@[simp]
theorem baseChangeTensorAlgEquiv_tmul (l : L) (a : A) (b : B) :
    baseChangeTensorAlgEquiv K L A B (l ⊗ₜ[K] (a ⊗ₜ[K] b)) = (l ⊗ₜ[K] a) ⊗ₜ[L] (1 ⊗ₜ[K] b) :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply _ _ _ _).trans
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul ..)

@[simp]
theorem baseChangeTensorAlgEquiv_symm_tmul (l₁ l₂ : L) (a : A) (b : B) :
    (baseChangeTensorAlgEquiv K L A B).symm ((l₁ ⊗ₜ[K] a) ⊗ₜ[L] (l₂ ⊗ₜ[K] b)) =
      (l₁ * l₂) ⊗ₜ[K] (a ⊗ₜ[K] b) := by
  refine (baseChangeTensorAlgEquiv K L A B).symm_apply_eq.mpr <|
    Eq.trans ?_ (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply _ _ _ _).symm
  exact (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange K L A B).symm_apply_eq.mp
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul ..)

/-- **Base change commutes with passing to the opposite algebra.** Together with
`TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` this is what makes base change respect both
the multiplication and the inversion of Brauer classes. -/
def baseChangeOpAlgEquiv : L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ :=
  (Algebra.TensorProduct.congr (AlgEquiv.toOpposite L L)
      (AlgEquiv.refl (R := K) (A₁ := Aᵐᵒᵖ))).trans (Algebra.TensorProduct.opAlgEquiv K L L A)

@[simp]
theorem baseChangeOpAlgEquiv_tmul (l : L) (a : Aᵐᵒᵖ) :
    baseChangeOpAlgEquiv K L A (l ⊗ₜ[K] a) = MulOpposite.op (l ⊗ₜ[K] a.unop) := by
  simp [baseChangeOpAlgEquiv]

@[simp]
theorem baseChangeOpAlgEquiv_symm_tmul (l : L) (a : A) :
    (baseChangeOpAlgEquiv K L A).symm (MulOpposite.op (l ⊗ₜ[K] a)) =
      l ⊗ₜ[K] MulOpposite.op a :=
  (baseChangeOpAlgEquiv K L A).symm_apply_eq.mpr <| by
    rw [baseChangeOpAlgEquiv_tmul, MulOpposite.unop_op]

/-! ### Base change in stages -/

section Tower

variable (M : Type*) [CommSemiring M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **Base change composes in stages**: for a tower `K → L → M`, extending `A` first to `L` and
then to `M` is extending it to `M` in one step, `M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A`.

The underlying map is Mathlib's linear equivalence
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which absorbs `L` into `M`; the content added
here is that it is multiplicative, checked on pure tensors, where it comes down to
`(l₁ • m₁) * (l₂ • m₂) = (l₁ * l₂) • (m₁ * m₂)` in the commutative `L`-algebra `M`.

Mathlib's `Algebra.TensorProduct.cancelBaseChange` is this equivalence under the extra hypothesis
that `A` is commutative, which the central simple algebras this serves are not. -/
def baseChangeTowerAlgEquiv : M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M A)
    (fun m₁ m₂ z₁ z₂ => by
      induction z₁ using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [add_mul, TensorProduct.tmul_add, hx, hy]
      | tmul l₁ a₁ =>
        induction z₂ using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [mul_add, TensorProduct.tmul_add, hx, hy]
        | tmul l₂ a₂ =>
          simp [Algebra.TensorProduct.tmul_mul_tmul, smul_smul, mul_comm l₁ l₂])
    (by simp [Algebra.TensorProduct.one_def])

@[simp]
theorem baseChangeTowerAlgEquiv_tmul (m : M) (l : L) (a : A) :
    baseChangeTowerAlgEquiv K L A M (m ⊗ₜ[L] (l ⊗ₜ[K] a)) = (l • m) ⊗ₜ[K] a :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply _ _ _ _).trans
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul ..)

@[simp]
theorem baseChangeTowerAlgEquiv_symm_tmul (m : M) (a : A) :
    (baseChangeTowerAlgEquiv K L A M).symm (m ⊗ₜ[K] a) = m ⊗ₜ[L] (1 ⊗ₜ[K] a) :=
  (baseChangeTowerAlgEquiv K L A M).symm_apply_eq.mpr <| by
    rw [baseChangeTowerAlgEquiv_tmul, one_smul]

end Tower

end Algebra.TensorProduct

end TauCeti
