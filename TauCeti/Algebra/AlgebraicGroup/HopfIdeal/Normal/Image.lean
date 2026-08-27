/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel
import TauCeti.Algebra.TensorProduct.Injective

/-!
# Normal scheme-theoretic images

Let `f : H →ₐc[k] K` be a morphism of commutative Hopf algebras over a field, representing a
homomorphism from `Spec K` to `Spec H`. Its scheme-theoretic image has coordinate algebra
`H / ker f`. This file proves that the image is normal when ambient conjugation admits an
algebra-homomorphic lift along the coordinate map.

In coordinate algebras, such a lift is an algebra homomorphism

```text
α♯ : K →ₐ[k] H ⊗[k] K
```

such that `(id ⊗ f) ∘ conj♯ = α♯ ∘ f`. If `f(x) = 0`, equivariance says that
`(id ⊗ f)(conj♯(x)) = 0`. Exactness of tensoring over the ground field identifies this kernel
with `H ⊗ ker f`, which is precisely normality of the image Hopf ideal.

## Main declarations

* `TauCeti.HopfIdeal.IsNormal.comap_of_injective`: inverse image along an injective
  bialgebra morphism over a field preserves normality.
* `TauCeti.HopfIdeal.isNormal_ker_of_conjugation_equivariant`: the scheme-theoretic image of an
  equivariant affine-group homomorphism is normal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a and §10.20.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§16--17.
* The tensor-kernel identity is `ker_lTensor_eq_rightTensorIdeal` from
  `TauCeti.Algebra.HopfAlgebra.Kernel`, using Mathlib's `Module.Flat.ker_lTensor_eq`.

This is the normality prerequisite for Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. Applied to multiplication from the semidirect product of two normal closed subgroups,
the lifted action is simultaneous ambient conjugation and the image is their normal product.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {k : Type u} [Field k]
variable {H : Type v} {K : Type w}
variable [CommRing H] [CommRing K]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- Pulling a normal Hopf ideal back along an injective bialgebra morphism over a field preserves
normality.

Contravariantly, the scheme-theoretic image of a normal closed affine subgroup under a
surjective affine-group morphism is normal. Injectivity is used only to reflect vanishing after
tensoring the first coordinate map. -/
theorem IsNormal.comap_of_injective {I : HopfIdeal k K} (hI : I.IsNormal)
    (f : H →ₐc[k] K) (hf : Function.Injective f) :
    (I.comap f).IsNormal := by
  rw [isNormal_iff_conjugation_mem]
  intro x hx
  let q : K →ₐ[k] K ⧸ I.toIdeal := Ideal.Quotient.mkₐ k I.toIdeal
  let g : H →ₐ[k] K ⧸ I.toIdeal := q.comp f.toAlgHom
  have hqker : RingHom.ker q = I.toIdeal := Ideal.Quotient.mkₐ_ker k I.toIdeal
  have hconjK := hI.conjugation_mem (mem_comap.mp hx)
  -- First push conjugation-stability through the quotient of the target.
  have hzeroK :
      Algebra.TensorProduct.map (AlgHom.id k K) q
          (HopfAlgebra.conjugationAlgHom (R := k) (H := K) (f x)) = 0 := by
    rw [← RingHom.mem_ker, ker_lTensor_eq_rightTensorIdeal q]
    rw [hqker]
    exact hconjK
  have hmaps :
      Algebra.TensorProduct.map f.toAlgHom g =
        (Algebra.TensorProduct.map (AlgHom.id k K) q).comp
          (Algebra.TensorProduct.map f.toAlgHom f.toAlgHom) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
  -- Naturality then makes the conjugation image vanish in `K ⊗ (K / I)`.
  have hzero :
      Algebra.TensorProduct.map f.toAlgHom g
          (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) = 0 := by
    calc
      Algebra.TensorProduct.map f.toAlgHom g
          (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) =
          Algebra.TensorProduct.map (AlgHom.id k K) q
            (Algebra.TensorProduct.map f.toAlgHom f.toAlgHom
              (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x)) := by
            rw [hmaps, AlgHom.comp_apply]
      _ = Algebra.TensorProduct.map (AlgHom.id k K) q
          (HopfAlgebra.conjugationAlgHom (R := k) (H := K) (f x)) := by
            exact congrArg (Algebra.TensorProduct.map (AlgHom.id k K) q)
              (AlgHom.congr_fun (HopfAlgebra.tensorProduct_map_comp_conjugationAlgHom f) x)
      _ = 0 := hzeroK
  have hgker : (I.comap f).toIdeal = RingHom.ker g := by
    rw [comap_toIdeal]
    ext y
    simp [g, q, Ideal.Quotient.eq_zero_iff_mem, mem_toIdeal]
  rw [hgker, ← ker_lTensor_eq_rightTensorIdeal g, RingHom.mem_ker]
  have hmaps' :
      (Algebra.TensorProduct.map f.toAlgHom (AlgHom.id k (K ⧸ I.toIdeal))).comp
          (Algebra.TensorProduct.map (AlgHom.id k H) g) =
        Algebra.TensorProduct.map f.toAlgHom g := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]
  -- Finally reflect vanishing through the injective first tensor-factor map.
  apply Algebra.TensorProduct.map_injective_of_injective f.toAlgHom
    (AlgHom.id k (K ⧸ I.toIdeal)) hf
    Function.injective_id
  calc
    Algebra.TensorProduct.map f.toAlgHom (AlgHom.id k (K ⧸ I.toIdeal))
        (Algebra.TensorProduct.map (AlgHom.id k H) g
          (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x)) =
      Algebra.TensorProduct.map f.toAlgHom g
        (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) := by
          rw [← AlgHom.comp_apply, hmaps']
    _ = 0 := hzero
    _ = Algebra.TensorProduct.map f.toAlgHom (AlgHom.id k (K ⧸ I.toIdeal)) 0 :=
      (map_zero _).symm

/-- **An equivariant affine-group homomorphism has normal scheme-theoretic image.**

The morphism `f : H →ₐc[k] K` is contravariant: it represents a homomorphism from the
affine group with coordinate algebra `K` into the ambient group with coordinate algebra `H`.
The algebra homomorphism `conjLift` lifts ambient conjugation along `f`; no action-law hypotheses
are required. Consequently the kernel Hopf ideal, and hence the scheme-theoretic image
`Spec (H / ker f)`, is normal. -/
theorem isNormal_ker_of_conjugation_equivariant (f : H →ₐc[k] K)
    (conjLift : K →ₐ[k] H ⊗[k] K)
    (hequiv :
      (Algebra.TensorProduct.map (AlgHom.id k H) f.toAlgHom).comp
          (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) =
        conjLift.comp f.toAlgHom) :
    (ker f).IsNormal := by
  rw [isNormal_iff_conjugation_mem]
  intro x hx
  rw [ker_toIdeal]
  rw [← ker_lTensor_eq_rightTensorIdeal f.toAlgHom, RingHom.mem_ker]
  have hfx : f x = 0 := (mem_ker f).mp hx
  calc
    Algebra.TensorProduct.map (AlgHom.id k H) f.toAlgHom
        (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) =
        conjLift (f x) := AlgHom.congr_fun hequiv x
    _ = 0 := by rw [hfx, map_zero]

end HopfIdeal

end TauCeti
