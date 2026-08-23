/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel

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

## Main declaration

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
