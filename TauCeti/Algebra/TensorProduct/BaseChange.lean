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
-- `distribBaseChange`, `cancelBaseChange`, `algEquivOfLinearEquivTensorProduct`,
-- `LinearMap.map_mul_of_map_mul_tmul` and `congr` are used only inside definition bodies and
-- proofs, and no definition below is `@[expose]`d.
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Nontrivial
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
* `TauCeti.Algebra.TensorProduct.commonOverfield`: a common overfield of two field extensions,
  together with the canonical comparison and injective scalar-extension maps.

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

universe u v w x

/-! ### Common overfields -/

/-- A common overfield of two extensions `K / k` and `L / k`.

The `K`-algebra structure on `Ω` is compatible with its `k`-algebra structure, while `right`
embeds `L` into `Ω` as a `k`-algebra. -/
structure CommonOverfield (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] where
  /-- The common overfield. -/
  Ω : Type (max v w)
  /-- The field structure on the common overfield. -/
  [fieldΩ : Field Ω]
  /-- The common overfield as a `k`-algebra. -/
  [algebraOmega : Algebra k Ω]
  /-- The common overfield as a `K`-algebra. -/
  [algebraKΩ : Algebra K Ω]
  [isScalarTower : IsScalarTower k K Ω]
  /-- The embedding of the second field extension into the common overfield. -/
  right : L →ₐ[k] Ω

/-- Construct a common overfield of two extensions of a field. -/
noncomputable def commonOverfield (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] :
    CommonOverfield k K L := by
  let R := K ⊗[k] L
  letI : Nontrivial R :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K L
      (algebraMap k K).injective (algebraMap k L).injective
  let P := Classical.choose (Ideal.exists_maximal R)
  have hP : P.IsMaximal := Classical.choose_spec (Ideal.exists_maximal R)
  letI : P.IsMaximal := hP
  let Ω := P.ResidueField
  let iK : K →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeLeft
  let iL : L →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeRight
  letI : Algebra K Ω := iK.toRingHom.toAlgebra
  letI : IsScalarTower k K Ω := IsScalarTower.of_algHom iK
  exact
    { Ω := Ω
      fieldΩ := inferInstance
      algebraOmega := inferInstance
      algebraKΩ := inferInstance
      isScalarTower := inferInstance
      right := iL }

namespace CommonOverfield

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

attribute [local instance] fieldΩ algebraOmega algebraKΩ isScalarTower

/-- Successive scalar extension through `K` agrees with direct scalar extension to a common
overfield. -/
noncomputable def comparison (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] :
    ((K ⊗[k] A) ⊗[K] d.Ω) ≃+* (A ⊗[k] d.Ω) :=
  let _ := d.fieldΩ
  let _ := d.algebraOmega
  let _ := d.algebraKΩ
  let _ := d.isScalarTower
  (Algebra.TensorProduct.comm K (K ⊗[k] A) d.Ω).toRingEquiv |>.trans
    ((Algebra.TensorProduct.cancelBaseChange k K d.Ω d.Ω A).toRingEquiv.trans
      (Algebra.TensorProduct.comm k d.Ω A).toRingEquiv)

/-- The common-overfield comparison sends nested pure tensors to pure tensors. -/
@[simp]
theorem comparison_tmul_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] (x : K) (a : A) (ω : d.Ω) :
    d.comparison A ((x ⊗ₜ[k] a) ⊗ₜ[K] ω) = a ⊗ₜ[k] (x • ω) := by
  simp [comparison]

/-- The inverse common-overfield comparison sends pure tensors to nested pure tensors. -/
@[simp]
theorem comparison_symm_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] (a : A) (ω : d.Ω) :
    (d.comparison A).symm (a ⊗ₜ[k] ω) = (1 ⊗ₜ[k] a) ⊗ₜ[K] ω := by
  simp [comparison]

/-- Scalar extension along the embedding of `L` into a common overfield. -/
noncomputable def map (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] :
    A ⊗[k] L →ₐ[k] A ⊗[k] d.Ω :=
  let _ := d.fieldΩ
  let _ := d.algebraOmega
  Algebra.TensorProduct.map (AlgHom.id k A) d.right

/-- Scalar extension to a common overfield maps each pure tensor componentwise. -/
@[simp]
theorem map_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] (a : A) (l : L) :
    d.map A (a ⊗ₜ[k] l) = a ⊗ₜ[k] d.right l := by
  simp [map]

/-- Scalar extension from `L` to a common overfield is injective. -/
theorem map_injective (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] : Function.Injective (d.map A) :=
  let _ := d.fieldΩ
  let _ := d.algebraOmega
  Module.Flat.lTensor_preserves_injective_linearMap d.right.toLinearMap
    (RingHom.injective d.right.toRingHom)

end CommonOverfield

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

end Algebra.TensorProduct

end TauCeti
