/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.GlobalFunctional
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Multiplication

/-!
# Reconstructing algebra-valued points from tensor automorphisms

Let `H` be a commutative Hopf algebra over a field `k`, and let `A` be a commutative
`k`-algebra. A tensor automorphism of scalar extension on the finite-dimensional
`H`-comodules determines a linear functional `H → A`. Tensor compatibility makes this
functional multiplicative, while compatibility with the tensor unit makes it preserve one.
It therefore defines an `A`-valued point of the affine group represented by `H`.

This file packages that reconstructed point and proves that reconstructing the tensor
automorphism induced by a point returns the original point. The converse equality, that the
reconstructed point induces the original component on every finite comodule, requires the
matrix-coefficient separation argument developed separately.

## Main declarations

* `TauCeti.Tannaka.globalFunctional_mul`: the glued functional preserves multiplication.
* `TauCeti.Tannaka.reconstructedPoint`: the algebra-valued point reconstructed from a tensor
  automorphism.
* `TauCeti.Tannaka.reconstructedPoint_fgPointTensorIso`: reconstruction recovers every
  algebra-valued point.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- The global functional reconstructed from a tensor automorphism preserves multiplication. -/
@[simp high]
theorem globalFunctional_mul
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) (x y : H) :
    globalFunctional k H A η (x * y) =
      globalFunctional k H A η x * globalFunctional k H A η y := by
  obtain ⟨N, hNfinite, hx⟩ :=
    Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) x
  obtain ⟨P, hPfinite, hy⟩ :=
    Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) y
  let N' : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H) :=
    ⟨N, Subcomodule.mem_finiteSubcomodules.mpr hNfinite⟩
  let P' : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H) :=
    ⟨P, Subcomodule.mem_finiteSubcomodules.mpr hPfinite⟩
  let _ : Module.Finite k N'.1.toSubmodule :=
    Subcomodule.mem_finiteSubcomodules.mp N'.2
  let _ : Module.Finite k P'.1.toSubmodule :=
    Subcomodule.mem_finiteSubcomodules.mp P'.2
  obtain ⟨Q, hQfinite, hmul⟩ :=
    Subcomodule.exists_finite_mul_le N'.1.toSubmodule P'.1.toSubmodule
  let Q' : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H) :=
    ⟨Q, Subcomodule.mem_finiteSubcomodules.mpr hQfinite⟩
  let xn : N'.1 := ⟨x, hx⟩
  let yp : P'.1 := ⟨y, hy⟩
  have hxy : x * y ∈ Q'.1 := hmul xn yp
  have hlocal := localFunctional_mul k H A η N' P' Q' hmul xn yp
  calc
    globalFunctional k H A η (x * y) =
        globalFunctional k H A η (⟨x * y, hxy⟩ : Q'.1) :=
      congrArg (globalFunctional k H A η) (Subtype.coe_mk (x * y) hxy).symm
    _ = localFunctional k H A η Q' ⟨x * y, hxy⟩ :=
      globalFunctional_apply k H A η Q' ⟨x * y, hxy⟩
    _ = localFunctional k H A η N' xn * localFunctional k H A η P' yp :=
      by simpa only [xn, yp] using hlocal
    _ = globalFunctional k H A η x * globalFunctional k H A η y := by
      rw [← globalFunctional_apply k H A η N' xn,
        ← globalFunctional_apply k H A η P' yp]

/-- The algebra-valued point reconstructed from a tensor automorphism of finite-comodule
scalar extension. Its underlying map is the global functional extracted from the automorphism. -/
noncomputable def reconstructedPoint
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    WithConv (H →ₐ[k] A) :=
  toConv (AlgHom.ofLinearMap (globalFunctional k H A η)
    (globalFunctional_one k H A η) (globalFunctional_mul k H A η))

/-- The reconstructed point evaluates as its defining global functional. -/
@[simp]
theorem reconstructedPoint_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) (x : H) :
    (reconstructedPoint k H A η).ofConv x = globalFunctional k H A η x := by
  rw [reconstructedPoint, WithConv.ofConv_toConv, AlgHom.ofLinearMap_apply]

/-- The underlying linear map of the reconstructed point is the global functional. -/
@[simp]
theorem reconstructedPoint_toLinearMap
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    (reconstructedPoint k H A η).ofConv.toLinearMap = globalFunctional k H A η := by
  ext x
  exact reconstructedPoint_apply k H A η x

/-- Reconstructing the tensor automorphism induced by an algebra-valued point returns that
point. Thus reconstruction is a left inverse to the tensor action of points. -/
@[simp]
theorem reconstructedPoint_fgPointTensorIso (g : WithConv (H →ₐ[k] A)) :
    reconstructedPoint k H A (fgPointTensorIso k H A g) = g := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  rw [← fgPointTensorIsoHom_apply]
  rw [reconstructedPoint_toLinearMap, fgPointTensorIsoHom_apply,
    globalFunctional_fgPointTensorIso]

end TauCeti.Tannaka
