/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Lie.TensorProduct
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality

/-!
# Universal enveloping algebras of products

The universal enveloping algebra of a product of Lie algebras is the tensor product of their
universal enveloping algebras. The equivalence sends a canonical generator `(x, y)` to
`ι(x) ⊗ 1 + 1 ⊗ ι(y)`. Its inverse sends a pure tensor to the product of the two canonical
inclusions.

This construction uses only the universal properties of enveloping algebras and tensor products;
it does not require a Poincare--Birkhoff--Witt theorem or any freeness hypothesis.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor`: the algebra equivalence
  `U(L × M) ≃ₐ[R] U(L) ⊗[R] U(M)`.
* `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor_ι`: its value on a canonical generator.
* `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor_map_inl` and `prodEquivTensor_map_inr`:
  its values on the canonical factor inclusions.
* `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor_naturality`: compatibility with maps of
  both Lie-algebra factors.
* `TauCeti.UniversalEnvelopingAlgebra.prodEquivTensor_symm_tmul`: the inverse on a pure tensor.

## Roadmap

This supplies the direct-sum functoriality used in Layer 3 of the LieHighestWeight roadmap.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2, no. 2, Proposition 2, for the
  enveloping algebra of a product and its tensor-product description.
* Mathlib's product-equivalence proof architecture in
  `Mathlib.LinearAlgebra.CliffordAlgebra.Prod`, adapted here to ordinary tensor products and
  universal enveloping algebras.
* The tensor-lift, commuting-factor induction, and inverse-composition proof pattern in
  `TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product`, adapted here to universal enveloping algebras.
* Mathlib's `UniversalEnvelopingAlgebra.lift` in `Mathlib.Algebra.Lie.UniversalEnveloping`.
* Mathlib's `Algebra.TensorProduct.lift` in `Mathlib.RingTheory.TensorProduct.Maps`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]

local notation "UL" => _root_.UniversalEnvelopingAlgebra R L
local notation "UM" => _root_.UniversalEnvelopingAlgebra R M
local notation "UP" => _root_.UniversalEnvelopingAlgebra R (L × M)

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def toTensor : UP →ₐ[R] UL ⊗[R] UM :=
  _root_.UniversalEnvelopingAlgebra.lift R
    (LieHom.prodToTensor (_root_.UniversalEnvelopingAlgebra.ι R)
      (_root_.UniversalEnvelopingAlgebra.ι R))

private noncomputable def fromLeft : UL →ₐ[R] UP :=
  map R (LieHom.inl R L M)

private noncomputable def fromRight : UM →ₐ[R] UP :=
  map R (LieHom.inr R L M)

private theorem from_commute (x : UL) (y : UM) :
    Commute (fromLeft R L M x) (fromRight R L M y) := by
  induction x using induction_ι with
  | ι a =>
      induction y using induction_ι with
      | ι b =>
          simp only [fromLeft, fromRight, map_ι]
          simpa only [AlgHom.id_apply, LieHom.inl_apply, LieHom.inr_apply] using
            commute_of_lie_eq_zero
              (AlgHom.id R UP) (a := (a, 0)) (b := (0, b)) (by simp)
      | algebraMap s =>
          rw [AlgHom.commutes]
          exact Algebra.commute_algebraMap_right _ _
      | add y z hy hz =>
          simpa only [map_add] using hy.add_right hz
      | mul y z hy hz =>
          simpa only [map_mul] using hy.mul_right hz
  | algebraMap r =>
      rw [AlgHom.commutes]
      exact Algebra.commute_algebraMap_left _ _
  | add x z hx hz =>
      simpa only [map_add] using hx.add_left hz
  | mul x z hx hz =>
      simpa only [map_mul] using hx.mul_left hz

private noncomputable def fromTensor : UL ⊗[R] UM →ₐ[R] UP :=
  Algebra.TensorProduct.lift (fromLeft R L M) (fromRight R L M) (from_commute R L M)

private theorem toTensor_ι (x : L × M) :
    toTensor R L M (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (_root_.UniversalEnvelopingAlgebra.ι R x.1) ⊗ₜ[R] (1 : UM) +
        (1 : UL) ⊗ₜ[R] (_root_.UniversalEnvelopingAlgebra.ι R x.2) := by
  rw [toTensor, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact LieHom.prodToTensor_apply _ _ x

private theorem toTensor_comp_fromLeft :
    (toTensor R L M).comp (fromLeft R L M) =
      (Algebra.TensorProduct.includeLeft : UL →ₐ[R] UL ⊗[R] UM) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.comp_apply,
    fromLeft, map_ι, toTensor_ι, LieHom.inl_apply,
    Algebra.TensorProduct.includeLeft_apply, map_zero, TensorProduct.tmul_zero, add_zero]

private theorem toTensor_comp_fromRight :
    (toTensor R L M).comp (fromRight R L M) =
      (Algebra.TensorProduct.includeRight : UM →ₐ[R] UL ⊗[R] UM) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro y
  simp only [AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.comp_apply,
    fromRight, map_ι, toTensor_ι, LieHom.inr_apply,
    Algebra.TensorProduct.includeRight_apply, map_zero, TensorProduct.zero_tmul, zero_add]

private theorem toTensor_comp_fromTensor :
    (toTensor R L M).comp (fromTensor R L M) =
      AlgHom.id R (UL ⊗[R] UM) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [fromTensor, Algebra.TensorProduct.lift_tmul, map_mul]
  have hx := AlgHom.congr_fun (toTensor_comp_fromLeft R L M) x
  have hy := AlgHom.congr_fun (toTensor_comp_fromRight R L M) y
  simp only [AlgHom.comp_apply] at hx hy
  rw [hx, hy]
  simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem fromTensor_comp_toTensor :
    (fromTensor R L M).comp (toTensor R L M) = AlgHom.id R UP := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.comp_apply,
    toTensor_ι, map_add, fromTensor, Algebra.TensorProduct.lift_tmul,
    fromLeft, fromRight, map_ι, LieHom.inl_apply, LieHom.inr_apply,
    map_one, mul_one, one_mul, AlgHom.id_apply]
  rw [← map_add]
  exact congrArg _ (Prod.ext (by simp) (by simp))

/-- The universal enveloping algebra of a product of Lie algebras is the tensor product of their
universal enveloping algebras. -/
noncomputable def prodEquivTensor : UP ≃ₐ[R] UL ⊗[R] UM :=
  AlgEquiv.ofAlgHom (toTensor R L M) (fromTensor R L M)
    (toTensor_comp_fromTensor R L M) (fromTensor_comp_toTensor R L M)

/-- The product-to-tensor equivalence sends a canonical generator `x` to
`ι(x.1) ⊗ 1 + 1 ⊗ ι(x.2)`. -/
theorem prodEquivTensor_ι (x : L × M) :
    prodEquivTensor R L M (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (_root_.UniversalEnvelopingAlgebra.ι R x.1) ⊗ₜ[R] (1 : UM) +
        (1 : UL) ⊗ₜ[R] (_root_.UniversalEnvelopingAlgebra.ι R x.2) := by
  rw [prodEquivTensor, AlgEquiv.ofAlgHom_apply, toTensor_ι]

/-- The `simp`-normal form of `prodEquivTensor_ι`, stated for the canonical generators as `simp`
writes them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem prodEquivTensor_ι' (x : L × M) :
    prodEquivTensor R L M
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R (L × M) (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x.1) ⊗ₜ[R] (1 : UM) +
        (1 : UL) ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.mkAlgHom R M (TensorAlgebra.ι R x.2) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using prodEquivTensor_ι R L M x

/-- On the left canonical factor, the product-to-tensor equivalence is tensoring with one. -/
@[simp]
theorem prodEquivTensor_map_inl (x : UL) :
    prodEquivTensor R L M (map R (LieHom.inl R L M) x) = x ⊗ₜ[R] (1 : UM) := by
  rw [prodEquivTensor, AlgEquiv.ofAlgHom_apply]
  simpa only [fromLeft, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply] using
    AlgHom.congr_fun (toTensor_comp_fromLeft R L M) x

/-- On the right canonical factor, the product-to-tensor equivalence is tensoring one with it. -/
@[simp]
theorem prodEquivTensor_map_inr (y : UM) :
    prodEquivTensor R L M (map R (LieHom.inr R L M) y) = (1 : UL) ⊗ₜ[R] y := by
  rw [prodEquivTensor, AlgEquiv.ofAlgHom_apply]
  simpa only [fromRight, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using
    AlgHom.congr_fun (toTensor_comp_fromRight R L M) y

/-- The product-to-tensor equivalence is natural in both Lie-algebra factors. -/
theorem prodEquivTensor_naturality
    {L' : Type*} {M' : Type*} [LieRing L'] [LieAlgebra R L'] [LieRing M'] [LieAlgebra R M']
    (f : LieHom R L L') (g : LieHom R M M') :
    (Algebra.TensorProduct.map (map R f) (map R g)).comp
        (prodEquivTensor R L M).toAlgHom =
      (prodEquivTensor R L' M').toAlgHom.comp (map R (f.prodMap g)) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  rintro ⟨x, y⟩
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, map_ι,
    LieHom.prodMap_apply]
  simp only [AlgEquiv.coe_toAlgHom]
  rw [prodEquivTensor_ι R L M (x, y),
    prodEquivTensor_ι R L' M' (f x, g y), map_add]
  simp only [Algebra.TensorProduct.map_tmul, map_ι, map_one]

/-- The inverse product-to-tensor equivalence sends a pure tensor to the product of the two
canonical inclusions. -/
@[simp]
theorem prodEquivTensor_symm_tmul (x : UL) (y : UM) :
    (prodEquivTensor R L M).symm (x ⊗ₜ[R] y) =
      map R (LieHom.inl R L M) x * map R (LieHom.inr R L M) y :=
  by
    rw [prodEquivTensor, AlgEquiv.ofAlgHom_symm]
    rw [AlgEquiv.ofAlgHom_apply, fromTensor, Algebra.TensorProduct.lift_tmul, fromLeft, fromRight]

end TauCeti.UniversalEnvelopingAlgebra
