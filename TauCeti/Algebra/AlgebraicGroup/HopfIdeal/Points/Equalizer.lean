/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Points of the equalizer of two homomorphisms of affine group schemes

The quotient by `TauCeti.CommHopfAlgCat.equalizerHopfIdeal` cuts out a subgroup of each point
group. This file identifies that subgroup: an `A`-point of `K` lies in it exactly when the two
morphisms induce the same map on it, which is the defining condition of the equalizer subfunctor.

## Main declarations

* `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_equalizerHopfIdeal_iff`: on points, the
  subgroup cut out by the equalizer Hopf ideal is where the two induced maps agree.

## References

The equalizer of two homomorphisms of group schemes is a closed subgroup scheme, described on
points by exactly this condition; see [Milne, *Algebraic Groups*][milne2017], §1.h, and Waterhouse,
*Introduction to Affine Group Schemes*, §15.3. It serves
`TauCetiRoadmap/ReductiveGroups/README.md`, "Hopf ideals ↔ closed subgroup schemes".
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- On points, the closed subgroup cut out by the equalizer Hopf ideal is exactly the set of
points on which the two induced maps of point groups agree. -/
theorem mem_quotientPointsSubgroup_equalizerHopfIdeal_iff (f g : H ⟶ K) (A : CommAlgCat.{w} R)
    (x : HopfAlgebra.points (R := R) (H := K) A) :
    x ∈ quotientPointsSubgroup K (equalizerHopfIdeal f g) A ↔
      AlgHom.mapDomain f.hom x = AlgHom.mapDomain g.hom x := by
  rw [mem_quotientPointsSubgroup_iff]
  have hle : ((equalizerHopfIdeal f g).toIdeal ≤
      RingHom.ker (x.ofConv : K →ₐ[R] A).toRingHom) ↔
      ∀ h : K, h ∈ equalizerHopfIdeal f g → x.ofConv h = 0 :=
    ⟨fun h _ hy => RingHom.mem_ker.1 (h (HopfIdeal.mem_toIdeal.2 hy)),
      fun h _ hy => RingHom.mem_ker.2 (h _ (HopfIdeal.mem_toIdeal.1 hy))⟩
  have hker := hle.symm.trans
    (equalizerHopfIdeal_le_ker_iff f g (x.ofConv : K →ₐ[R] A).toRingHom)
  rw [hker]
  constructor
  · intro h
    exact ofConv_injective (AlgHom.ext fun a => h a)
  · intro h a
    exact congrArg (fun m : WithConv (H →ₐ[R] A) => m.ofConv a) h

end CommHopfAlgCat

end TauCeti
