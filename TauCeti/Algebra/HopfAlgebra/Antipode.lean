/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Antipode identities for Hopf algebras

The antipode of a Hopf algebra is an antihomomorphism for both its algebra and coalgebra
structures. Mathlib already proves the multiplicative statement directly, as
`HopfAlgebra.antipode_mul_antidistrib`. This file records the coalgebraic statement: applying
the antipode before comultiplication is the same as comultiplying, swapping the two tensor
factors, and applying the antipode to each factor.

For a commutative Hopf algebra, the antipode is involutive, hence defines an algebra
automorphism. These facts are also recorded here in the commutative case.

## Main declarations

* `TauCeti.HopfAlgebra.antipode_comul_antidistrib`: the identity as an equality of linear maps.
* `TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply`: the pointwise form.
* `TauCeti.HopfAlgebra.antipode_antipode`: the antipode of a commutative Hopf algebra is
  involutive.
* `TauCeti.HopfAlgebra.antipodeAlgEquiv`: the antipode as an algebra equivalence in the
  commutative case.
* `TauCeti.HopfAlgebra.antipodeAlgEquiv_toAlgHom`: the underlying algebra homomorphism is
  Mathlib's antipode algebra homomorphism.
* `TauCeti.HopfAlgebra.antipodeAlgEquiv_symm`: the antipode equivalence is its own inverse.

## Implementation notes

The proof of `antipode_comul_antidistrib` takes place in the convolution monoid of linear maps
from the Hopf algebra to its tensor square. Comultiplication factors as the convolution product
of the two canonical tensor inclusions, and postcomposing Mathlib's antipode convolution
identity `LinearMap.antipode_mul_id` with those inclusions exhibits the proposed opposite
comultiplication as a left inverse of comultiplication. Mathlib's
`LinearMap.comul_right_inv` supplies the matching right inverse, so uniqueness of inverses
finishes the proof.

The involutivity proof uses `inv_inv` in Mathlib's convolution group on algebra maps. The private
lemma `ofConv_inv` isolates the single definitional unfolding of `AlgHom.convInv` needed to read
that group identity as the pointwise equation `S (S x) = x`.

## References

The anti-coalgebra identity and involutivity in the commutative case are standard; see Sweedler,
*Hopf Algebras*, Chapter 4, Proposition 4.0.1 for the anti-(co)algebra identity and Proposition
4.0.6 for involutivity. Mathlib formalizes these results for Hopf objects in a braided monoidal
category as `CategoryTheory.HopfObj.antipode_comul` and
`CategoryTheory.HopfObj.antipode_antipode`. The proofs below are ring-level analogues, stated for
`HopfAlgebra R C` and `HopfAlgebra R A` so they apply directly to the bundled ring-theoretic
antipode APIs.
-/

public section

open HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [Semiring C] [_root_.HopfAlgebra R C]

noncomputable section

section Commutative

variable {A : Type v} [CommSemiring A] [_root_.HopfAlgebra R A]

/-- By the definition of `AlgHom.convInv`, convolution inversion composes an algebra map with
the antipode. This isolates the definitional unfolding used in `antipode_antipode`. -/
private lemma ofConv_inv (f : WithConv (A →ₐ[R] A)) :
    (f⁻¹).ofConv = f.ofConv.comp (_root_.HopfAlgebra.antipodeAlgHom R A) :=
  rfl

/-- In a commutative Hopf algebra, applying the antipode twice is the identity. -/
@[simp]
theorem antipode_antipode (x : A) :
    HopfAlgebraStruct.antipode R (HopfAlgebraStruct.antipode R x) = x := by
  have h := congrArg WithConv.ofConv (inv_inv (WithConv.toConv (AlgHom.id R A)))
  rw [ofConv_inv, ofConv_inv] at h
  simpa only [AlgHom.comp_apply, WithConv.ofConv_toConv, AlgHom.id_apply,
    _root_.HopfAlgebra.antipodeAlgHom_apply] using
    DFunLike.congr_fun h x

/-- The antipode of a commutative Hopf algebra as an involutive algebra equivalence. -/
noncomputable def antipodeAlgEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (_root_.HopfAlgebra.antipodeAlgHom R A)
    (_root_.HopfAlgebra.antipodeAlgHom R A)
    (AlgHom.ext fun x ↦ antipode_antipode x)
    (AlgHom.ext fun x ↦ antipode_antipode x)

/-- The antipode algebra equivalence acts by the antipode. -/
@[simp]
theorem antipodeAlgEquiv_apply (x : A) :
    antipodeAlgEquiv (R := R) (A := A) x = HopfAlgebraStruct.antipode R x :=
  by
    rw [antipodeAlgEquiv, AlgEquiv.ofAlgHom_apply,
      _root_.HopfAlgebra.antipodeAlgHom_apply]

/-- The algebra homomorphism underlying the antipode equivalence is Mathlib's antipode algebra
homomorphism. -/
@[simp]
theorem antipodeAlgEquiv_toAlgHom :
    ((antipodeAlgEquiv (R := R) (A := A)) : A →ₐ[R] A) =
      _root_.HopfAlgebra.antipodeAlgHom R A := by
  rw [antipodeAlgEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The ring homomorphism underlying the antipode equivalence is Mathlib's antipode algebra
homomorphism viewed as a ring homomorphism. -/
@[simp]
theorem antipodeAlgEquiv_toRingHom :
    (antipodeAlgEquiv (R := R) (A := A) : A →+* A) =
      (_root_.HopfAlgebra.antipodeAlgHom R A : A →+* A) := by
  exact congrArg AlgHom.toRingHom (antipodeAlgEquiv_toAlgHom (R := R) (A := A))

/-- The antipode algebra equivalence is its own inverse. -/
@[simp]
theorem antipodeAlgEquiv_symm :
    (antipodeAlgEquiv (R := R) (A := A)).symm = antipodeAlgEquiv :=
  by rw [antipodeAlgEquiv, AlgEquiv.ofAlgHom_symm]

end Commutative

/-- Postcomposing the antipode convolution identity `LinearMap.antipode_mul_id` with an algebra
homomorphism `f`: the map `f ∘ₗ antipode` is a left convolution inverse of `f`. -/
private lemma algHom_comp_antipode_mul_self {D : Type w} [Semiring D] [Algebra R D]
    (f : C →ₐ[R] D) :
    (toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
        toConv f.toLinearMap = 1 := by
  refine WithConv.ofConv_injective ?_
  calc ((toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
        toConv f.toLinearMap).ofConv
      = f.toLinearMap ∘ₗ
          (toConv (antipode R) * toConv LinearMap.id : WithConv (C →ₗ[R] C)).ofConv := by
        rw [LinearMap.algHom_comp_convMul_distrib]
        simp
    -- `LinearMap.algHom_comp_convOne` is the last step, but it lives in
    -- `Mathlib.RingTheory.HopfAlgebra.Quotient`, whose Hopf-ideal theory is unrelated here.
    _ = (1 : WithConv (C →ₗ[R] D)).ofConv := by
        rw [LinearMap.antipode_mul_id]
        ext c
        simp

section AlgebraCoalgebra

variable {R : Type u} {C : Type v} [CommSemiring R] [Semiring C] [Algebra R C]
  [_root_.CoalgebraStruct R C]

/-- **Swapping the legs of `Δ` and applying `S` to each is the reversed convolution product.**
For any linear endomorphism `S`, precomposing the two inclusions with `S` and multiplying them in
the opposite order gives `(S ⊗ S) ∘ swap ∘ Δ`.

Nothing about `S` is assumed — the identity is natural in it — so it is stated for an arbitrary
`S : C →ₗ[R] C` and specialized to the antipode at the call site. -/
private lemma map_comp_comm_comp_comul_eq_convMul (S : C →ₗ[R] C) :
    (toConv (TensorProduct.map S S ∘ₗ
        (TensorProduct.comm R C C).toLinearMap ∘ₗ Coalgebra.comul) :
          WithConv (C →ₗ[R] C ⊗[R] C)) =
      toConv ((Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap ∘ₗ S) *
        toConv ((Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap ∘ₗ
          S) := by
  apply WithConv.ofConv_injective
  have hmul : LinearMap.mul' R (C ⊗[R] C) ∘ₗ
      TensorProduct.map
        ((Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap ∘ₗ S)
        ((Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap ∘ₗ S) =
      TensorProduct.map S S ∘ₗ (TensorProduct.comm R C C).toLinearMap := by
    apply TensorProduct.ext
    ext x y
    simp
  simp only [LinearMap.convMul_def]
  have h := congrArg (fun f => f ∘ₗ (Coalgebra.comul (R := R) (A := C))) hmul
  simpa only [LinearMap.comp_assoc] using h.symm

end AlgebraCoalgebra

/-- **The right-hand side of `antipode_comul_antidistrib` is a left convolution inverse of
comultiplication.** -/
private lemma antipode_comul_antidistrib_rhs_mul_comul :
    (toConv (TensorProduct.map (antipode R) (antipode R) ∘ₗ
        (TensorProduct.comm R C C).toLinearMap ∘ₗ Coalgebra.comul) :
          WithConv (C →ₗ[R] C ⊗[R] C)) * toConv Coalgebra.comul = 1 := by
  have hL := algHom_comp_antipode_mul_self (R := R) (C := C) (D := C ⊗[R] C)
    (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C)
  have hP := algHom_comp_antipode_mul_self (R := R) (C := C) (D := C ⊗[R] C)
    (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C)
  -- Expand both sides into convolution products of the inclusions; the inner pair cancels by
  -- `algHom_comp_antipode_mul_self`, then the outer pair does. `congrArg₂` rather than `rw`:
  -- `WithConv` is a type synonym, so rewriting under `toConv` re-wraps through `ofConv`.
  rw [congrArg₂ (· * ·) (map_comp_comm_comp_comul_eq_convMul (antipode R))
    Coalgebra.comul_eq_convMul_includeLeft_includeRight]
  set L : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap
  set P : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap
  set LS : WithConv (C →ₗ[R] C ⊗[R] C) := toConv
    ((Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap ∘ₗ antipode R)
  set PS : WithConv (C →ₗ[R] C ⊗[R] C) := toConv
    ((Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap ∘ₗ antipode R)
  calc PS * LS * (L * P) = PS * (LS * L * P) := by simp only [mul_assoc]
    _ = PS * P := by rw [hL, one_mul]
    _ = 1 := hP

/-- The antipode reverses comultiplication: after comultiplication, swap the tensor factors
and apply the antipode to each of them. This is the coalgebraic counterpart of
`HopfAlgebra.antipode_mul_antidistrib`. -/
theorem antipode_comul_antidistrib :
    Coalgebra.comul ∘ₗ antipode R =
      TensorProduct.map (antipode R) (antipode R) ∘ₗ
        (TensorProduct.comm R C C).toLinearMap ∘ₗ Coalgebra.comul :=
  (WithConv.toConv_injective
    (left_inv_eq_right_inv antipode_comul_antidistrib_rhs_mul_comul
      LinearMap.comul_right_inv)).symm

/-- Pointwise form of `antipode_comul_antidistrib`. -/
@[simp]
theorem antipode_comul_antidistrib_apply (c : C) :
    Coalgebra.comul (antipode R c) =
      TensorProduct.map (antipode R) (antipode R)
        ((TensorProduct.comm R C C) (Coalgebra.comul c)) :=
  LinearMap.congr_fun antipode_comul_antidistrib c

end

end HopfAlgebra

end TauCeti
