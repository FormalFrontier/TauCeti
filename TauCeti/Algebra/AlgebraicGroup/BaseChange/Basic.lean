/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of bialgebra points

This file records that the usual algebraic base-change adjunction is compatible with the
convolution monoid structure on the functor of points of a bialgebra. For a bialgebra `A` over
`k`, a `k`-algebra `K`, and a commutative `K`-algebra `R`, the `R`-points of the base-changed
bialgebra `K ⊗[k] A` over `K` are the same as `k`-algebra maps `A →ₐ[k] R`, and this
identification is a monoid isomorphism for convolution. When `A` is a Hopf algebra, these are
the convolution groups of points.

This is the algebraic-group-facing form of the ReductiveGroups roadmap item "Base change.
`K ⊗[k] A` as a Hopf algebra over `K`"; it builds on Mathlib's tensor-product bialgebra
instance, Mathlib's tensor-product Hopf algebra antipode formula, and `AlgHom.liftEquiv`.

## Main definitions

* `TauCeti.AlgHom.baseChangePointsMulEquiv`: the convolution monoid isomorphism between
  `A →ₐ[k] R` and `K ⊗[k] A →ₐ[K] R`. When `A` is a Hopf algebra these are convolution
  groups, so this is automatically an isomorphism of groups.
* `TauCeti.AlgHom.baseChangePointsMulEquiv_inv_apply_tmul` and
  `TauCeti.AlgHom.baseChangePointsMulEquiv_symm_inv_apply`: pointwise formulas for
  convolution inverses of base-changed points.

## References

The tensor-product bialgebra and Hopf-algebra structures and algebra base-change adjunction
used here are from Mathlib, respectively `Mathlib.RingTheory.Bialgebra.TensorProduct`,
`Mathlib.RingTheory.HopfAlgebra.TensorProduct`, and `AlgHom.liftEquiv`.
-/

public section

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
  [CommSemiring R] [Algebra k K] [_root_.Bialgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

private lemma liftEquiv_map_mul
    (f g : WithConv (A →ₐ[k] R)) :
    AlgHom.liftEquiv k K A R
      (WithConv.ofConv (f * g)) =
    WithConv.ofConv
      ((WithConv.toConv (AlgHom.liftEquiv k K A R f.ofConv) *
        WithConv.toConv (AlgHom.liftEquiv k K A R g.ofConv)) :
          WithConv (K ⊗[k] A →ₐ[K] R)) := by
  ext a
  suffices
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all _ _))
        (Coalgebra.comul (R := k) a) =
      (Algebra.TensorProduct.lift (AlgHom.liftEquiv k K A R f.ofConv)
        (AlgHom.liftEquiv k K A R g.ofConv) (fun _ _ => .all _ _))
        ((AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A)
          (1 ⊗ₜ[K] 1 ⊗ₜ[k] Coalgebra.comul (R := k) a)) by
    simpa only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul,
      AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using this
  induction Coalgebra.comul (R := k) a with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a₁ a₂ =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        AlgHom.liftEquiv_tmul, Algebra.smul_def, map_one, one_mul]

/-- Base change of bialgebra points is a monoid isomorphism for the convolution product.

The forward direction sends `f : A →ₐ[k] R` to `s ⊗ a ↦ s • f a`; the inverse restricts a
`K`-algebra map `K ⊗[k] A →ₐ[K] R` along `a ↦ 1 ⊗ a`. -/
@[expose] noncomputable def baseChangePointsMulEquiv :
    WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R) :=
  { WithConv.congr (AlgHom.liftEquiv k K A R) with
  map_mul' f g := by
    apply WithConv.ext
    ext a
    simp [liftEquiv_map_mul] }

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_ofConv (f : WithConv (A →ₐ[k] R)) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f).ofConv =
      AlgHom.liftEquiv k K A R f.ofConv :=
  rfl

/-- The inverse base-change convolution-monoid isomorphism is restriction along
`A → K ⊗[k] A`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_ofConv (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv =
      (AlgHom.liftEquiv k K A R).symm f.ofConv :=
  rfl

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f (s ⊗ₜ[k] a) =
      s • f.ofConv a :=
  rfl

/-- The inverse of the base-change convolution-monoid isomorphism restricts along
`a ↦ 1 ⊗ a`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv a =
      f.ofConv (1 ⊗ₜ[k] a) :=
  rfl

end AlgHom

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
  [CommSemiring R] [Algebra k K] [_root_.HopfAlgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

/-- Pointwise inverse formula after base change: on a pure tensor `s ⊗ a`, the convolution
inverse of a base-changed point has value `s • f (S a)`.

The `≃*` `AlgHom.baseChangePointsMulEquiv` is automatically a group isomorphism here, since
`A` is a Hopf algebra; this records the value of an inverse point on pure tensors. -/
@[simp]
lemma baseChangePointsMulEquiv_inv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f)⁻¹ (s ⊗ₜ[k] a) =
      s • f.ofConv (antipode k a) := by
  rw [convInv_apply]
  simp

/-- Pointwise inverse formula after restricting a base-changed point along `a ↦ 1 ⊗ a`:
the inverse of `(e.symm f)` has value `f (1 ⊗ S a)` at `a`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_inv_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    (((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f)⁻¹).ofConv a =
      f.ofConv (1 ⊗ₜ[k] antipode k a) := by
  rw [convInv_apply, baseChangePointsMulEquiv_symm_apply]

end AlgHom

end TauCeti
