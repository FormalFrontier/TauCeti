/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# The tensor product of comodules over a bialgebra

This file constructs the tensor product of two right comodules over a bialgebra `C`. If `M`
and `N` are right `C`-comodules, the coaction on `M ⊗ N` is the usual diagonal formula

`m ⊗ n ↦ m₀ ⊗ n₀ ⊗ m₁ n₁`,

which multiplies the two coefficient factors in `C`. The file first builds this map
(`tensorCombine`, `tensorCoact`), then verifies the coassociativity and counit laws and
packages them as `Comodule.tensor`, and finally makes the construction functorial in both
arguments (`Comodule.Hom.tensorMap`).

Both laws come from the same source: the bialgebra axioms say that the comultiplication and
the counit of `C` are *algebra* homomorphisms, hence commute with the multiplication that
`tensorCombine` performs. That single observation is isolated as
`lTensor_comp_tensorCombine`, and instantiating it at `Bialgebra.comulAlgHom` and
`Bialgebra.counitAlgHom` supplies the coefficient half of each law; the remaining half is the
coefficient-free reassociation bookkeeping in
`assoc_comp_tensorCombine_rTensor_comp_tensorCombine`.

Following `Comodule.cofree`, `Comodule.tensor` is not a global instance: an `R`-module can
carry many coactions, so a global instance on a tensor product would make `Comodule`
resolution non-confluent.

## Main declarations

* `TauCeti.Comodule.tensorCombine`: combines two coacted tensor factors.
* `TauCeti.Comodule.tensorCoact`: the diagonal coaction on `M ⊗ N`.
* `TauCeti.Comodule.tensorCombine_natural`: naturality of the combining map in the two
  comodule carriers.
* `TauCeti.Comodule.tensorCombine_assoc`, `tensorCombine_lid`, and `tensorCombine_rid`:
  compatibility of coefficient combination with the tensor associator and unitors.
* `TauCeti.Comodule.tensorCoact_natural`: the diagonal coaction commutes with tensoring
  comodule morphisms.
* `TauCeti.Comodule.lTensor_comp_tensorCombine`: an algebra homomorphism on the coefficients
  passes through the combining map.
* `TauCeti.Comodule.tensorCoact_coassoc` and `TauCeti.Comodule.tensorCoact_counit`:
  the two comodule laws for the diagonal coaction.
* `TauCeti.Comodule.tensor`: the right `C`-comodule structure on `M ⊗[R] N`.
* `TauCeti.Comodule.Hom.tensorMap`: the tensor product of two comodule morphisms, with
  `tensorMap_id` and `tensorMap_comp`.

## References

This is the standard tensor product of right comodules over a bialgebra; see Sweedler, *Hopf
Algebras*, Chapter 2. It advances the Layer 1 target "Comodules over a coalgebra/Hopf algebra
... tensor products, duals, the regular representation" of the Tau Ceti reductive-groups
roadmap, `ReductiveGroups/README.md` in TauCetiRoadmap, which asks for the rigid monoidal
category of finite-dimensional comodules; the tensor product built here is its underlying
bifunctor.
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y z

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]

section Combine

variable [NonUnitalNonAssocSemiring C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Combine two coacted tensor factors by shuffling the middle factors together and multiplying
the two `C`-components.

On pure tensors it sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
noncomputable def tensorCombine :
    (M ⊗[R] C) ⊗[R] (N ⊗[R] C) →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap

/-- Unfold `tensorCombine` to its defining composition. Kept `private`: the map's body is
deliberately not exposed to downstream modules (the module system hides non-`@[expose]`d
definition bodies), so this equation is an in-file helper for the lemmas below. -/
private theorem tensorCombine_def :
    tensorCombine (R := R) (C := C) (M := M) (N := N) =
      TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap :=
  rfl

/-- `tensorCombine` sends `(m ⊗ c) ⊗ (n ⊗ d)` to `(m ⊗ n) ⊗ cd`. -/
@[simp]
theorem tensorCombine_tmul_tmul (m : M) (c : C) (n : N) (d : C) :
    tensorCombine (R := R) (C := C) (M := M) (N := N)
        ((m ⊗ₜ[R] c) ⊗ₜ[R] (n ⊗ₜ[R] d)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] (c * d) := by
  simp [tensorCombine_def]

variable {M' : Type y} {N' : Type z}
variable [AddCommMonoid M'] [Module R M']
variable [AddCommMonoid N'] [Module R N']

/-- The combining map is natural in the two comodule carriers. -/
theorem tensorCombine_natural (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    TensorProduct.map (TensorProduct.map f g) (LinearMap.id : C →ₗ[R] C) ∘ₗ
        tensorCombine (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := C) (M := M') (N := N') ∘ₗ
        TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
          (TensorProduct.map g (LinearMap.id : C →ₗ[R] C)) := by
  rw [tensorCombine_def, tensorCombine_def]
  have h := TensorProduct.tensorTensorTensorComm_comp_map (R := R) (M := M) (N := C)
    (P := N) (Q := C) (S := M') (T := C) (V := N') (W := C) f
    (LinearMap.id : C →ₗ[R] C) g (LinearMap.id : C →ₗ[R] C)
  calc
    TensorProduct.map (TensorProduct.map f g) (LinearMap.id : C →ₗ[R] C) ∘ₗ
        (TensorProduct.map (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N)
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap) =
        (TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
            (LinearMap.mul' R C) ∘ₗ
          TensorProduct.map (TensorProduct.map f g)
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) LinearMap.id)) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap := by
      rw [LinearMap.comp_assoc]
      apply TensorProduct.ext'
      intro x y
      simp [TensorProduct.map_map]
    _ = TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.map (TensorProduct.map f g)
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) LinearMap.id) ∘ₗ
          (TensorProduct.tensorTensorTensorComm R M C N C).toLinearMap) := by
      rw [LinearMap.comp_assoc]
    _ = TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        ((TensorProduct.tensorTensorTensorComm R M' C N' C).toLinearMap ∘ₗ
          TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
            (TensorProduct.map g (LinearMap.id : C →ₗ[R] C))) := by
      rw [← h]
    _ = (TensorProduct.map (LinearMap.id : M' ⊗[R] N' →ₗ[R] M' ⊗[R] N')
          (LinearMap.mul' R C) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R M' C N' C).toLinearMap) ∘ₗ
          TensorProduct.map (TensorProduct.map f (LinearMap.id : C →ₗ[R] C))
            (TensorProduct.map g (LinearMap.id : C →ₗ[R] C)) := by
      rw [LinearMap.comp_assoc]

end Combine

section Coherence

variable {P : Type*}
variable [Semiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Combining three coacted factors is compatible with reassociation. The two sides multiply
the coefficient factors as `(c * d) * e` and `c * (d * e)`, respectively. -/
theorem tensorCombine_assoc (x : M ⊗[R] C) (y : N ⊗[R] C) (z : P ⊗[R] C) :
    TensorProduct.map (TensorProduct.assoc R M N P).toLinearMap LinearMap.id
        (tensorCombine (R := R) (C := C) (M := M ⊗[R] N) (N := P)
          (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      tensorCombine (R := R) (C := C) (M := M) (N := N ⊗[R] P)
        (x ⊗ₜ[R] tensorCombine (R := R) (C := C) (M := N) (N := P) (y ⊗ₜ[R] z)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simpa only [add_tmul, LinearMap.map_add] using congrArg₂ (· + ·) hx₁ hx₂
  | tmul m c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simpa only [tmul_add, add_tmul, LinearMap.map_add] using congrArg₂ (· + ·) hy₁ hy₂
    | tmul n d =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
        simpa only [tmul_add, LinearMap.map_add] using congrArg₂ (· + ·) hz₁ hz₂
      | tmul p e => simp [mul_assoc]

/-- The inverse associator is compatible with combining three coacted factors. -/
theorem tensorCombine_assoc_symm (x : M ⊗[R] C) (y : N ⊗[R] C) (z : P ⊗[R] C) :
    TensorProduct.map (TensorProduct.assoc R M N P).symm.toLinearMap LinearMap.id
        (tensorCombine (R := R) (C := C) (M := M) (N := N ⊗[R] P)
          (x ⊗ₜ[R] tensorCombine (R := R) (C := C) (M := N) (N := P) (y ⊗ₜ[R] z))) =
      tensorCombine (R := R) (C := C) (M := M ⊗[R] N) (N := P)
        (tensorCombine (R := R) (C := C) (M := M) (N := N) (x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simpa only [add_tmul, LinearMap.map_add] using congrArg₂ (· + ·) hx₁ hx₂
  | tmul m c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simpa only [tmul_add, add_tmul, LinearMap.map_add] using congrArg₂ (· + ·) hy₁ hy₂
    | tmul n d =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
        simpa only [tmul_add, LinearMap.map_add] using congrArg₂ (· + ·) hz₁ hz₂
      | tmul p e => simp [mul_assoc]

/-- Combining the trivial coefficient `1` on the left and applying the left tensor unitor
scales a coacted vector by the scalar in the trivial factor. -/
theorem tensorCombine_lid (r : R) (x : M ⊗[R] C) :
    TensorProduct.map (TensorProduct.lid R M).toLinearMap LinearMap.id
        (tensorCombine (R := R) (C := C) (M := R) (N := M)
          ((r ⊗ₜ[R] (1 : C)) ⊗ₜ[R] x)) =
      r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simpa only [tmul_add, LinearMap.map_add, smul_add] using congrArg₂ (· + ·) hx hy
  | tmul m c =>
    simpa using (smul_tmul' r m c).symm

/-- Combining the trivial coefficient `1` on the left agrees with applying the inverse left
tensor unitor to the carrier factor. -/
theorem tensorCombine_lid_symm (x : M ⊗[R] C) :
    tensorCombine (R := R) (C := C) (M := R) (N := M)
        (((1 : R) ⊗ₜ[R] (1 : C)) ⊗ₜ[R] x) =
      TensorProduct.map (TensorProduct.lid R M).symm.toLinearMap LinearMap.id x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simpa only [tmul_add, LinearMap.map_add] using congrArg₂ (· + ·) hx hy
  | tmul m c => simp

/-- Combining the trivial coefficient `1` on the right and applying the right tensor unitor
scales a coacted vector by the scalar in the trivial factor. -/
theorem tensorCombine_rid (x : M ⊗[R] C) (r : R) :
    TensorProduct.map (TensorProduct.rid R M).toLinearMap LinearMap.id
        (tensorCombine (R := R) (C := C) (M := M) (N := R)
          (x ⊗ₜ[R] (r ⊗ₜ[R] (1 : C)))) =
      r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simpa only [add_tmul, LinearMap.map_add, smul_add] using congrArg₂ (· + ·) hx hy
  | tmul m c =>
    simpa using (smul_tmul' r m c).symm

/-- Combining the trivial coefficient `1` on the right agrees with applying the inverse right
tensor unitor to the carrier factor. -/
theorem tensorCombine_rid_symm (x : M ⊗[R] C) :
    tensorCombine (R := R) (C := C) (M := M) (N := R)
        (x ⊗ₜ[R] ((1 : R) ⊗ₜ[R] (1 : C))) =
      TensorProduct.map (TensorProduct.rid R M).symm.toLinearMap LinearMap.id x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simpa only [add_tmul, LinearMap.map_add] using congrArg₂ (· + ·) hx hy
  | tmul m c => simp

end Coherence

section Coact

/-- The diagonal coaction map on the tensor product of two right comodules over a bialgebra.

The later full tensor-product comodule structure uses this map as its coaction. -/
noncomputable def tensorCoact [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    M ⊗[R] N →ₗ[R] (M ⊗[R] N) ⊗[R] C :=
  tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
    TensorProduct.map (coact (R := R) (C := C) (M := M))
      (coact (R := R) (C := C) (M := N))

/-- Unfold `tensorCoact` to the combining map applied to the two component coactions. Kept
`private` for the same reason as `tensorCombine_def`: the coaction's body is not exposed
downstream, so this equation only serves the lemmas in this file. -/
private theorem tensorCoact_def [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] :
    tensorCoact (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := C) (M := M) (N := N) ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M))
          (coact (R := R) (C := C) (M := N)) :=
  rfl

/-- The tensor-product coaction, before expanding the two component coactions. -/
@[simp]
theorem tensorCoact_tmul [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (m : M) (n : N) :
    tensorCoact (R := R) (C := C) (M := M) (N := N) (m ⊗ₜ[R] n) =
      tensorCombine (R := R) (C := C) (M := M) (N := N)
        (coact (R := R) (C := C) (M := M) m ⊗ₜ[R]
          coact (R := R) (C := C) (M := N) n) := by
  simp [tensorCoact_def (R := R) (C := C) (M := M) (N := N)]

variable {M' : Type y} {N' : Type z}

/-- The diagonal tensor coaction is natural under tensor products of comodule morphisms. -/
theorem tensorCoact_natural [Semiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid M'] [Module R M'] [Comodule R C M']
    [AddCommMonoid N'] [Module R N'] [Comodule R C N']
    (f : Hom R C M M') (g : Hom R C N N') :
    TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap)
        (LinearMap.id : C →ₗ[R] C) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) =
        tensorCoact (R := R) (C := C) (M := M') (N := N') ∘ₗ
        TensorProduct.map f.toLinearMap g.toLinearMap := by
  apply TensorProduct.ext'
  intro m n
  have hcombine := LinearMap.congr_fun
    (tensorCombine_natural (R := R) (C := C) (M := M) (N := N)
      (M' := M') (N' := N') f.toLinearMap g.toLinearMap)
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R] coact (R := R) (C := C) (M := N) n)
  simpa [tensorCoact_tmul, Hom.map_coact_apply] using hcombine

end Coact

section Slot

variable {D : Type y}
variable [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- An `R`-algebra homomorphism `φ : C →ₐ[R] D` may be pushed through the combining map:
`tensorCombine` multiplies the two coefficient factors, and `φ` is multiplicative.

Taking `φ` to be the comultiplication and the counit of a bialgebra gives precisely the two
compatibilities that make `tensorCoact` a coaction. -/
theorem lTensor_comp_tensorCombine (φ : C →ₐ[R] D) :
    φ.toLinearMap.lTensor (M ⊗[R] N) ∘ₗ tensorCombine (R := R) (C := C) (M := M) (N := N) =
      tensorCombine (R := R) (C := D) (M := M) (N := N) ∘ₗ
        TensorProduct.map (φ.toLinearMap.lTensor M) (φ.toLinearMap.lTensor N) := by
  refine TensorProduct.ext' fun x y => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
  | tmul m c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
    | tmul n d => simp

end Slot

section Reassociate

variable [Semiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Combining twice and then reassociating agrees with reassociating each factor first and
then combining once over `C ⊗[R] C`.

This is pure bookkeeping about `tensorCombine` — it uses no coalgebra structure — and it is
what turns the coassociativity of the two factors into the coassociativity of `tensorCoact`. -/
theorem assoc_comp_tensorCombine_rTensor_comp_tensorCombine :
    TensorProduct.assoc R (M ⊗[R] N) C C ∘ₗ
        (tensorCombine (R := R) (C := C) (M := M) (N := N)).rTensor C ∘ₗ
          tensorCombine (R := R) (C := C) (M := M ⊗[R] C) (N := N ⊗[R] C) =
      tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N) ∘ₗ
        TensorProduct.map (TensorProduct.assoc R M C C).toLinearMap
          (TensorProduct.assoc R N C C).toLinearMap := by
  refine TensorProduct.ext_fourfold' fun w x y z => ?_
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
  | tmul m a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [add_tmul, tmul_add, map_add, hp, hq]
    | tmul n b => simp [Algebra.TensorProduct.tmul_mul_tmul]

end Reassociate

section Structure

variable [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The diagonal coaction on `M ⊗[R] N` is coassociative.

Coassociativity of the two factors puts the doubly coacted vectors into the form
`m₀ ⊗ Δ(m₁)`, and the comultiplication of `C` is an algebra homomorphism, so it commutes with
the multiplication that `tensorCombine` performs on the coefficients. -/
theorem tensorCoact_coassoc :
    TensorProduct.assoc R (M ⊗[R] N) C C ∘ₗ
        (tensorCoact (R := R) (C := C) (M := M) (N := N)).rTensor C ∘ₗ
          tensorCoact (R := R) (C := C) (M := M) (N := N) =
      Coalgebra.comul.lTensor (M ⊗[R] N) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) := by
  -- `tensorCombine` is natural in the two carriers, here applied to the two coactions
  -- themselves; `LinearMap.rTensor` is by definition `TensorProduct.map · LinearMap.id`.
  have hnat :
      (TensorProduct.map (coact (R := R) (C := C) (M := M))
            (coact (R := R) (C := C) (M := N))).rTensor C ∘ₗ
          tensorCombine (R := R) (C := C) (M := M) (N := N) =
        tensorCombine (R := R) (C := C) (M := M ⊗[R] C) (N := N ⊗[R] C) ∘ₗ
          TensorProduct.map ((coact (R := R) (C := C) (M := M)).rTensor C)
            ((coact (R := R) (C := C) (M := N)).rTensor C) :=
    tensorCombine_natural _ _
  -- The comultiplication of `C`, an algebra homomorphism, passes through `tensorCombine`.
  have hslot :
      (Coalgebra.comul (R := R) (A := C)).lTensor (M ⊗[R] N) ∘ₗ
          tensorCombine (R := R) (C := C) (M := M) (N := N) =
        tensorCombine (R := R) (C := C ⊗[R] C) (M := M) (N := N) ∘ₗ
          TensorProduct.map ((Coalgebra.comul (R := R) (A := C)).lTensor M)
            ((Coalgebra.comul (R := R) (A := C)).lTensor N) :=
    lTensor_comp_tensorCombine (Bialgebra.comulAlgHom R C)
  refine TensorProduct.ext' fun m n => ?_
  have hsplit : ∀ z : (M ⊗[R] N) ⊗[R] C,
      (tensorCoact (R := R) (C := C) (M := M) (N := N)).rTensor C z =
        (tensorCombine (R := R) (C := C) (M := M) (N := N)).rTensor C
          ((TensorProduct.map (coact (R := R) (C := C) (M := M))
            (coact (R := R) (C := C) (M := N))).rTensor C z) := by
    intro z
    rw [tensorCoact_def, LinearMap.rTensor_comp]
    rfl
  have h1 := LinearMap.congr_fun hnat
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R] coact (R := R) (C := C) (M := N) n)
  have h2 := LinearMap.congr_fun
    (assoc_comp_tensorCombine_rTensor_comp_tensorCombine (R := R) (C := C) (M := M) (N := N))
    ((coact (R := R) (C := C) (M := M)).rTensor C (coact (R := R) (C := C) (M := M) m) ⊗ₜ[R]
      (coact (R := R) (C := C) (M := N)).rTensor C (coact (R := R) (C := C) (M := N) n))
  have h3 := LinearMap.congr_fun hslot
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R] coact (R := R) (C := C) (M := N) n)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe] at h1 h2 h3 ⊢
  rw [tensorCoact_tmul, hsplit, h1, h2, coassoc_apply, coassoc_apply, h3]

/-- The diagonal coaction on `M ⊗[R] N` satisfies the counit law: the counit of `C` is an
algebra homomorphism, so it turns the product of the two coefficients into the product of
their counits, which is `1`. -/
theorem tensorCoact_counit :
    Coalgebra.counit.lTensor (M ⊗[R] N) ∘ₗ
        tensorCoact (R := R) (C := C) (M := M) (N := N) =
      (TensorProduct.mk R (M ⊗[R] N) R).flip 1 := by
  have hslot :
      (Coalgebra.counit (R := R) (A := C)).lTensor (M ⊗[R] N) ∘ₗ
          tensorCombine (R := R) (C := C) (M := M) (N := N) =
        tensorCombine (R := R) (C := R) (M := M) (N := N) ∘ₗ
          TensorProduct.map ((Coalgebra.counit (R := R) (A := C)).lTensor M)
            ((Coalgebra.counit (R := R) (A := C)).lTensor N) :=
    lTensor_comp_tensorCombine (Bialgebra.counitAlgHom R C)
  refine TensorProduct.ext' fun m n => ?_
  have h := LinearMap.congr_fun hslot
    (coact (R := R) (C := C) (M := M) m ⊗ₜ[R] coact (R := R) (C := C) (M := N) n)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at h ⊢
  rw [tensorCoact_tmul, h, lTensor_counit_coact, lTensor_counit_coact]
  simp

variable (R C M N) in
/-- The tensor product of two right `C`-comodules over a bialgebra, with the diagonal coaction
`m ⊗ n ↦ (m₀ ⊗ n₀) ⊗ m₁ n₁`.

Following `Comodule.cofree`, this is deliberately *not* a global instance: an `R`-module can
carry many coactions, so a global instance on a tensor product would make `Comodule`
resolution non-confluent. Select it explicitly, or register it as a local instance. -/
@[expose, implicit_reducible]
noncomputable def tensor : Comodule R C (M ⊗[R] N) where
  coact := tensorCoact
  coassoc := tensorCoact_coassoc
  lTensor_counit_comp_coact := tensorCoact_counit

-- Register `tensor` as a local instance for the rest of this file, so that the diagonal
-- comodule on `M ⊗[R] N` resolves automatically instead of being threaded through every
-- statement with `letI`. It is deliberately *not* a global instance; see `Comodule.tensor`.
attribute [local instance] tensor

/-- The coaction of the tensor-product comodule is the diagonal coaction `tensorCoact`. -/
@[simp]
theorem tensor_coact :
    coact (R := R) (C := C) (M := M ⊗[R] N) =
      tensorCoact (R := R) (C := C) (M := M) (N := N) :=
  rfl

namespace Hom

variable {M' : Type y} {N' : Type z}
variable [AddCommMonoid M'] [Module R M'] [Comodule R C M']
variable [AddCommMonoid N'] [Module R N'] [Comodule R C N']

/-- The tensor product of two comodule morphisms, as a morphism of tensor-product comodules.

Both source and target carry the diagonal coaction of `Comodule.tensor`; the required
compatibility is `Comodule.tensorCoact_natural`. -/
@[expose]
noncomputable def tensorMap (f : Hom R C M M') (g : Hom R C N N') :
    Hom R C (M ⊗[R] N) (M' ⊗[R] N') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_coact := tensorCoact_natural f g

/-- The underlying linear map of `tensorMap f g` is the tensor product of the two underlying
linear maps. -/
@[simp]
theorem tensorMap_toLinearMap (f : Hom R C M M') (g : Hom R C N N') :
    (tensorMap f g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap :=
  rfl

/-- `tensorMap f g` acts as `f ⊗ g`. -/
@[simp]
theorem tensorMap_apply (f : Hom R C M M') (g : Hom R C N N') (x : M ⊗[R] N) :
    tensorMap f g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

/-- `tensorMap` acts on a simple tensor as the pair of component morphisms. -/
@[simp]
theorem tensorMap_tmul (f : Hom R C M M') (g : Hom R C N N') (m : M) (n : N) :
    tensorMap f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  rfl

/-- The tensor product of two identity morphisms is the identity morphism.

This is not a `simp` lemma: its left-hand side is not in `simp`-normal form, because the `@[simp]`
lemma `ComoduleCat.ofHom_id` rewrites each `Comodule.Hom.id R C _` to the categorical identity
`𝟙 (ComoduleCat.of R C _)`. This fires even though no `ComoduleCat.ofHom` appears syntactically in
the left-hand side: `ofHom` is a reducible `abbrev` for the identity coercion (a categorical
morphism `of R C M ⟶ of R C N` just *is* a `Comodule.Hom R C M N`), so `simp` unifies `ofHom_id`'s
left-hand side `ofHom (Comodule.Hom.id R C _)` with a bare `Comodule.Hom.id R C _`. Tagging this
lemma `@[simp]` therefore fails the `simpNF` linter. (Contrast `cofreeMap_id`, whose left-hand side
`cofreeMap LinearMap.id` carries no bare `Comodule.Hom.id` and so stays normal.) -/
theorem tensorMap_id : tensorMap (id R C M) (id R C N) = id R C (M ⊗[R] N) := by
  refine Comodule.Hom.ext fun x => ?_
  rw [tensorMap_apply, id_toLinearMap, id_toLinearMap, TensorProduct.map_id]
  rfl

variable {M'' : Type*} {N'' : Type*}
variable [AddCommMonoid M''] [Module R M''] [Comodule R C M'']
variable [AddCommMonoid N''] [Module R N''] [Comodule R C N'']

/-- The tensor product of morphisms is compatible with composition. -/
@[simp]
theorem tensorMap_comp (f : Hom R C M M') (f' : Hom R C M' M'')
    (g : Hom R C N N') (g' : Hom R C N' N'') :
    tensorMap (f'.comp f) (g'.comp g) = (tensorMap f' g').comp (tensorMap f g) := by
  refine Comodule.Hom.ext fun x => ?_
  rw [Comodule.Hom.comp_apply, tensorMap_apply, tensorMap_apply, tensorMap_apply,
    comp_toLinearMap, comp_toLinearMap, TensorProduct.map_comp, LinearMap.comp_apply]

end Hom

end Structure

end Comodule

end TauCeti
