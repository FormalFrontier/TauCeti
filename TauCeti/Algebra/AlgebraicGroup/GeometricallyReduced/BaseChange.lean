/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric reducedness under base change

Geometric reducedness of a commutative Hopf algebra is preserved by extension of the base
field. If `H` is geometrically reduced over `k`, then the scalar extension `K ⊗[k] H` is
geometrically reduced over every field extension `K / k`.

## Main declaration

* `TauCeti.geometricallyReducedCommHopfAlgProperty.baseChange`: geometric reducedness is
  preserved by extension of the base field.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.of_baseChange_of_isAlgebraic`: geometric
  reducedness descends from an algebraic extension of the base field.

## References

* J. S. Milne, *Algebraic Groups* (2017), for the geometric-reducedness terminology.

The argument follows `TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange`, with reducedness
transported along the scalar-extension equivalence in place of connectedness.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-- **Geometric reducedness is preserved by extension of the base field.** -/
theorem geometricallyReducedCommHopfAlgProperty.baseChange
    {k : Type u} (K : Type (max u v)) [Field k] [Field K] [Algebra k K]
    {H : CommHopfAlgCat.{v} k}
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    geometricallyReducedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H) := by
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hH ⊢
  intro L _ _
  let _ : Algebra k L := Algebra.compHom L (algebraMap k K)
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let e := (Algebra.TensorProduct.comm K (K ⊗[k] H) L).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k K L L H).toRingEquiv.trans
      (Algebra.TensorProduct.comm k L H).toRingEquiv)
  let _ := hH L
  exact isReduced_of_injective e.toRingHom e.injective

/-- **Geometric reducedness descends from an algebraic extension of the base field.**

For a further extension `L / k`, embed the algebraic field `K` into an algebraic closure `Ω` of
`L`. Reducedness of `(K ⊗[k] H) ⊗[K] Ω` identifies with reducedness of `H ⊗[k] Ω`, which
descends to `H ⊗[k] L` along the injective scalar-extension map. -/
theorem geometricallyReducedCommHopfAlgProperty.of_baseChange_of_isAlgebraic
    {k : Type u} (K : Type (max u v)) [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyReducedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyReducedCommHopfAlgProperty k H := by
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hH ⊢
  intro L _ _
  let Ω := AlgebraicClosure L
  let i : K →ₐ[k] Ω := IsAlgClosed.lift
  let _ : Algebra K Ω := i.toRingHom.toAlgebra
  let _ : IsScalarTower k K Ω := IsScalarTower.of_algHom i
  let e := (Algebra.TensorProduct.comm K (K ⊗[k] H) Ω).toRingEquiv |>.trans
    ((Algebra.TensorProduct.cancelBaseChange k K Ω Ω H).toRingEquiv.trans
      (Algebra.TensorProduct.comm k Ω H).toRingEquiv)
  have hΩ : IsReduced ((H : Type v) ⊗[k] Ω) :=
    isReduced_of_injective e.symm.toRingHom e.symm.injective
  let g : L →ₐ[k] Ω := IsScalarTower.toAlgHom k L Ω
  let f : (H : Type v) ⊗[k] L →ₐ[k] (H : Type v) ⊗[k] Ω :=
    Algebra.TensorProduct.map (AlgHom.id k H) g
  exact isReduced_of_injective f.toRingHom
    (Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap
      (RingHom.injective g.toRingHom))

end TauCeti
