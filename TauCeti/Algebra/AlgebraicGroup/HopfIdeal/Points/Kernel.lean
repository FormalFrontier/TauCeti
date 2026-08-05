/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic

/-!
# Points of the kernel of an affine group-scheme morphism

For a morphism `f : H ⟶ K` of commutative Hopf algebras, the kernel closed subgroup
scheme `TauCeti.CommHopfAlgCat.kernelSpec f` is cut out by the kernel Hopf ideal. This
file records its kernel semantics on functors of points: for every commutative
`R`-algebra `A`, an `A`-point of the source group scheme maps to the unit point exactly
when it lies in the subgroup of points cut out by the kernel Hopf ideal — the `A`-points
of the kernel. Since this holds for all test algebras, by Yoneda the kernel closed
subgroup scheme represents the kernel of the induced morphism of group-valued points
functors.

## Main declarations

* `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff`: the points-level kernel
  property.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{u} R}

/-- Kernel semantics on functors of points: for every commutative `R`-algebra `A`, an
`A`-point of the source is sent to the unit point exactly when it lies in the subgroup of
points cut out by the kernel Hopf ideal — the `A`-points of `kernelSpec f`. This is the
universal property of the kernel tested against arbitrary algebras; by Yoneda,
`kernelSpec f` represents the kernel of the induced morphism of group-valued points
functors. -/
@[simp]
theorem mapPointsFunctor_app_eq_one_iff (f : H ⟶ K) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    toConv (g.ofConv.comp (f.hom : ↥H →ₐ[R] ↥K)) = 1 ↔
      g ∈ quotientPointsSubgroup K (kernelHopfIdeal f) A := by
  rw [← mapPointsFunctor_app_apply, mem_quotientPointsSubgroup_iff]
  have hbridge : (∀ h : ↥K, h ∈ kernelHopfIdeal f → g.ofConv h = 0) ↔
      (kernelHopfIdeal f).toIdeal ≤ RingHom.ker g.ofConv.toRingHom := by
    constructor
    · intro hg x hx
      exact RingHom.mem_ker.mpr (hg x (HopfIdeal.mem_toIdeal.mp hx))
    · intro hle x hx
      exact RingHom.mem_ker.mp (hle (HopfIdeal.mem_toIdeal.mpr hx))
  rw [hbridge, kernelHopfIdeal_toIdeal_le_ker_iff]
  constructor
  · intro h1
    ext a
    have hval := congrArg
      (fun ψ : HopfAlgebra.points (R := R) (H := H) A => ψ.ofConv a) h1
    rw [mapPointsFunctor_app_apply_apply] at hval
    simpa [Algebra.ofId_apply] using hval.trans (AlgHom.convOne_apply a)
  · intro heq
    rw [mapPointsFunctor_app_apply, heq]
    refine ofConv_injective ?_
    ext a
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply]
    exact (AlgHom.convOne_apply a).symm

end CommHopfAlgCat

end TauCeti
