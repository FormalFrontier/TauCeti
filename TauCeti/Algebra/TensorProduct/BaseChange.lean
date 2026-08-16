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
-- Non-public: the declarations from `Tower` appear only inside definition bodies and proofs,
-- and no definition below is `@[expose]`d.
import Mathlib.LinearAlgebra.TensorProduct.Tower
-- Public: `Algebra.TensorProduct.congr` supplies the scalar-automorphism action exported below,
-- and `TensorProduct.map` occurs in the type of `ScalarAut.comul_smul` downstream.
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change is compatible with `⊗`, with `ᵐᵒᵖ`, and with itself

Scalar extension along a commutative `K`-algebra `L` distributes over the tensor product, commutes
with passing to the opposite algebra, and composes in stages:

* `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv`:
  `L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B)`;
* `TauCeti.Algebra.TensorProduct.baseChangeOpAlgEquiv`: `L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] (L ⊗[K] A)ᵐᵒᵖ`;
* `TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`:
  `M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A` for a tower `K → L → M`.
* `TauCeti.Algebra.TensorProduct.baseChangeTowerRingEquiv`: the same tower comparison with tensor
  factors in coordinate-ring order, `(L ⊗[K] A) ⊗[L] M ≃+* A ⊗[K] M`.
* `TauCeti.ScalarAut.instMulSemiringAction`: scalar automorphisms act on a scalar extension
  through its scalar factor.
* `TauCeti.ScalarAut.baseChangeMap_smul`: scalar extension of an algebra map is equivariant for
  scalar automorphisms.

None is reproved from scratch: the first and third upgrade Mathlib's linear equivalences
`TensorProduct.AlgebraTensorModule.distribBaseChange` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` to algebra equivalences, and the second
composes `AlgEquiv.toOpposite` with Mathlib's `Algebra.TensorProduct.opAlgEquiv`. The fourth
reorders the factors of the third using `Algebra.TensorProduct.comm`.

## Implementation notes

All four equivalences are opaque: their bodies are not `@[expose]`d, and the `_tmul` and
`_symm_tmul` simp lemmas below are the whole public interface, in both directions.

Mathlib's `Algebra.TensorProduct.cancelBaseChange` is the third equivalence for a **commutative**
algebra being extended; the algebras this file exists to serve are central simple, so they are not
commutative in general, and the hypothesis has to go along with the chance to reuse that
definition.

These are statements about scalar extension as such, with no central-simplicity hypotheses. The
first three are consumed by `TauCeti/Algebra/CentralSimple/BaseChange.lean`, which re-exports them
for `TauCeti/Algebra/BrauerGroup/BaseChange.lean`. The coordinate-ring-order comparison is consumed
by the geometric connectedness and reducedness base-change modules.

## References

The first three are the compatibilities asked for by the **Base change preserves central
simplicity, then is a homomorphism** bullet of Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2. The final
comparison supplies base-change infrastructure for the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u v w x

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
here is that it is multiplicative. That is checked in the easy direction, on the inverse
`M ⊗[K] A → M ⊗[L] (L ⊗[K] A)`, whose pure tensors are the `m ⊗ₜ[K] a` with `a` in `A` itself, so
that `LinearMap.map_mul_of_map_mul_tmul` reduces it to `simp`; this is how Mathlib's
`Algebra.TensorProduct.cancelBaseChange` is built.

That equivalence of Mathlib's is this one under the extra hypothesis that `A` is commutative, which
the central simple algebras this serves are not. -/
def baseChangeTowerAlgEquiv : M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A :=
  (AlgEquiv.ofLinearEquiv (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M A).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ ↦ by simp)).symm

@[simp]
theorem baseChangeTowerAlgEquiv_tmul (m : M) (l : L) (a : A) :
    baseChangeTowerAlgEquiv K L A M (m ⊗ₜ[L] (l ⊗ₜ[K] a)) = (l • m) ⊗ₜ[K] a :=
  _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul K L M m a l

@[simp]
theorem baseChangeTowerAlgEquiv_symm_tmul (m : M) (a : A) :
    (baseChangeTowerAlgEquiv K L A M).symm (m ⊗ₜ[K] a) = m ⊗ₜ[L] (1 ⊗ₜ[K] a) :=
  (baseChangeTowerAlgEquiv K L A M).symm_apply_eq.mpr <| by
    rw [baseChangeTowerAlgEquiv_tmul, one_smul]

end Tower

section CommTower

variable (K L A M : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L]
  [CommSemiring A] [Algebra K A] [CommSemiring M] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- Successive scalar extension, with tensor factors in coordinate-ring order, agrees with direct
scalar extension. -/
noncomputable def baseChangeTowerRingEquiv :
    ((L ⊗[K] A) ⊗[L] M) ≃+* (A ⊗[K] M) :=
  (Algebra.TensorProduct.comm L (L ⊗[K] A) M).toRingEquiv.trans
    ((baseChangeTowerAlgEquiv K L A M).toRingEquiv.trans
      (Algebra.TensorProduct.comm K M A).toRingEquiv)

/-- The coordinate-ring-order tower comparison sends nested pure tensors to pure tensors. -/
@[simp]
theorem baseChangeTowerRingEquiv_tmul_tmul (l : L) (a : A) (m : M) :
    baseChangeTowerRingEquiv K L A M ((l ⊗ₜ[K] a) ⊗ₜ[L] m) = a ⊗ₜ[K] (l • m) := by
  simp [baseChangeTowerRingEquiv]

/-- The inverse coordinate-ring-order tower comparison sends pure tensors to nested pure
tensors. -/
@[simp]
theorem baseChangeTowerRingEquiv_symm_tmul (a : A) (m : M) :
    (baseChangeTowerRingEquiv K L A M).symm (a ⊗ₜ[K] m) =
      (1 ⊗ₜ[K] a) ⊗ₜ[L] m := by
  simp [baseChangeTowerRingEquiv]

end CommTower

end Algebra.TensorProduct

namespace ScalarAut

variable {K L A : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- Scalar automorphisms act on a scalar extension through the scalar factor. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction (L ≃ₐ[K] L) (L ⊗[K] A) :=
  let congrHom : (L ≃ₐ[K] L) →* (L ⊗[K] A ≃ₐ[K] L ⊗[K] A) :=
    { toFun σ := Algebra.TensorProduct.congr σ .refl
      map_one' := Algebra.TensorProduct.congr_refl
      map_mul' σ τ := by
        -- Multiplication of algebra equivalences is composition in the opposite textual order;
        -- expose that representation so `congr_trans` can state the required compatibility.
        change Algebra.TensorProduct.congr (τ.trans σ) .refl =
          (Algebra.TensorProduct.congr τ (.refl : A ≃ₐ[K] A)).trans
            (Algebra.TensorProduct.congr σ .refl)
        convert Algebra.TensorProduct.congr_trans τ σ (.refl : A ≃ₐ[K] A) .refl using 1
        ext
        rfl }
  MulSemiringAction.compHom _ congrHom

/-- Scalar multiplication on a base change is the tensor-product congruence. -/
@[simp]
theorem smul_def (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    σ • x = Algebra.TensorProduct.congr σ (.refl : A ≃ₐ[K] A) x :=
  rfl

/-- Scalar multiplication on a pure tensor acts through the first factor. -/
@[simp]
theorem smul_tmul (σ : L ≃ₐ[K] L) (a : L) (x : A) :
    σ • (a ⊗ₜ[K] x) = σ a ⊗ₜ[K] x := by
  simp [smul_def]

/-- Scalar extension of an algebra morphism commutes with the scalar-factor action. -/
@[simp]
theorem baseChangeMap_smul {B : Type*} [Semiring B] [Algebra K B] (f : A →ₐ[K] B)
    (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    Algebra.TensorProduct.map (AlgHom.id K L) f
        (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A) x) =
      σ • Algebra.TensorProduct.map (AlgHom.id K L) f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a x =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, smul_tmul]
      rfl

/-- The scalar-factor action is semilinear for the corresponding automorphism of `L`. -/
theorem smul_smulₛₗ (σ : L ≃ₐ[K] L) (a : L) (x : L ⊗[K] A) :
    σ • (a • x) = σ a • σ • x := by
  simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]

/-- The scalar action as a semilinear map over `L`. -/
noncomputable def semilinearMap (σ : L ≃ₐ[K] L) :
    L ⊗[K] A →ₛₗ[σ.toRingHom] L ⊗[K] A where
  toFun x := σ • x
  map_add' := smul_add σ
  map_smul' := smul_smulₛₗ (A := A) σ

/-- The semilinear scalar map agrees pointwise with the scalar action. -/
@[simp]
theorem semilinearMap_apply (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    semilinearMap (A := A) σ x = σ • x :=
  by
    -- Exported semilinear-map application unfolds to `TensorProduct.map`, whereas the action
    -- unfolds to `TensorProduct.congr`; expose both representations before comparing them.
    change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) x = σ • x
    rw [smul_def, Algebra.TensorProduct.congr_apply]
    rw [AlgEquiv.refl_toAlgHom]

end ScalarAut

end TauCeti
