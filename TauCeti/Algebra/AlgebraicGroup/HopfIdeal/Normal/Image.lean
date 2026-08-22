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

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field, representing a
homomorphism from `Spec K` to `Spec H`. Its scheme-theoretic image has coordinate algebra
`H / ker f`. This file proves that the image is normal when ambient conjugation admits an
algebra-homomorphic lift along the coordinate map.

In coordinate algebras, such a lift is an algebra homomorphism

```text
α♯ : K ⟶ H ⊗ K
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

/-- Tensoring on the left by an algebra over a field carries the kernel of an algebra map to
the corresponding right tensor ideal. This local form is used to detect normality from an
equivariant action. -/
private theorem ker_tensorProduct_map_id (f : H →ₐ[k] K) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k H) f) =
      rightTensorIdeal (R := k) (H := H) (RingHom.ker f) := by
  let I := RingHom.ker f
  let q : H →ₐ[k] H ⧸ I := Ideal.Quotient.mkₐ k I
  let f' : (H ⧸ I) →ₐ[k] K := Ideal.kerLiftAlg f
  have hf' : Function.Injective f' := Ideal.kerLiftAlg_injective f
  have htensor : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id k H) f') := by
    exact TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k H).toLinearMap f'.toLinearMap Function.injective_id hf'
  have hcomp :
      (Algebra.TensorProduct.map (AlgHom.id k H) f').comp
          (Algebra.TensorProduct.map (AlgHom.id k H) q) =
        Algebra.TensorProduct.map (AlgHom.id k H) f := by
    have hright : f'.comp q = f := by
      ext x
      exact Ideal.kerLiftAlg_mk f x
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hright]
  rw [← ker_tensorProduct_map_id_quotient I]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro hx
    apply htensor
    rw [map_zero]
    exact (AlgHom.congr_fun hcomp x).trans hx
  · intro hx
    have hx' : Algebra.TensorProduct.map (AlgHom.id k H) q x = 0 := by
      simpa only [AlgHom.coe_toRingHom] using hx
    rw [← AlgHom.congr_fun hcomp x]
    simp only [AlgHom.comp_apply, hx', map_zero]

/-- **An equivariant affine-group homomorphism has normal scheme-theoretic image.**

The morphism `f : H →ₐc[k] K` is contravariant: it represents a homomorphism from the
affine group with coordinate algebra `K` into the ambient group with coordinate algebra `H`.
The algebra homomorphism `action` lifts ambient conjugation along `f`; no action-law hypotheses
are required. Consequently the kernel Hopf ideal, and hence the scheme-theoretic image
`Spec (H / ker f)`, is normal. -/
theorem isNormal_ker_of_conjugation_equivariant (f : H →ₐc[k] K)
    (action : K →ₐ[k] H ⊗[k] K)
    (equivariant :
      (Algebra.TensorProduct.map (AlgHom.id k H) f.toAlgHom).comp
          (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) =
        action.comp f.toAlgHom) :
    (ker f).IsNormal := by
  rw [isNormal_iff_conjugation_mem]
  intro x hx
  rw [ker_toIdeal]
  rw [← ker_tensorProduct_map_id f.toAlgHom, RingHom.mem_ker]
  have hfx : f x = 0 := (mem_ker f).mp hx
  calc
    Algebra.TensorProduct.map (AlgHom.id k H) f.toAlgHom
        (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) =
        action (f x) := AlgHom.congr_fun equivariant x
    _ = 0 := by rw [hfx, map_zero]

end HopfIdeal

end TauCeti
