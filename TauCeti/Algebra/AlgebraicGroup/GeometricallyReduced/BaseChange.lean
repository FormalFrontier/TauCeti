/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat

/-!
# Geometric reducedness under base change

Geometric reducedness of a commutative Hopf algebra is preserved by extension of the base
field. If `H` is geometrically reduced over `k`, then the scalar extension `K ⊗[k] H` is
geometrically reduced over every field extension `K / k`.

## Main declaration

* `TauCeti.geometricallyReducedCommHopfAlgProperty.baseChange`: geometric reducedness is
  preserved by extension of the base field.

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

end TauCeti
