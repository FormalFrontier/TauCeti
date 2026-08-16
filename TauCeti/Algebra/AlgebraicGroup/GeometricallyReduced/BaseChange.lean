/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
import TauCeti.Algebra.TensorProduct.CommonOverfield

/-!
# Geometric reducedness under base change

Geometric reducedness of a commutative Hopf algebra is preserved by and descends along extension
of the base field. In particular, `H` is geometrically reduced over `k` if and only if the scalar
extension `K ⊗[k] H` is geometrically reduced over any field extension `K / k`.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlgProperty.baseChange`: geometric reducedness is
  preserved by extension of the base field.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.of_baseChange`: geometric reducedness descends
  from an extension of the base field.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.baseChange_iff`: geometric reducedness is
  equivalent before and after extension of the base field.

## References

* J. S. Milne, *Algebraic Groups* (2017), for the geometric-reducedness terminology.

For preservation, reducedness is transported along the equivalence cancelling successive scalar
extensions. For descent, the two scalar extensions are compared in a common overfield, then
reducedness descends along the resulting injective map.

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
  let _ := hH L
  exact isReduced_of_injective
    (Algebra.TensorProduct.baseChangeTowerRingEquiv k K H L).toRingHom
    (Algebra.TensorProduct.baseChangeTowerRingEquiv k K H L).injective

/-- **Geometric reducedness descends from an extension of the base field.**

If `K ⊗[k] H` is geometrically reduced over a field extension `K / k`, then `H` is geometrically
reduced over `k`. -/
theorem geometricallyReducedCommHopfAlgProperty.of_baseChange
    {k : Type u} (K : Type (max u v)) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyReducedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyReducedCommHopfAlgProperty k H := by
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hH ⊢
  intro L _ _
  let d := Algebra.TensorProduct.commonOverfield k K L
  let _ := hH d.Ω
  have hΩ : IsReduced ((H : Type v) ⊗[k] d.Ω) :=
    isReduced_of_injective (d.comparison H).symm.toRingHom (d.comparison H).symm.injective
  exact isReduced_of_injective (d.map H).toRingHom (d.map_injective H)

/-- Geometric reducedness is equivalent before and after extension of the base field. -/
theorem geometricallyReducedCommHopfAlgProperty.baseChange_iff
    {k : Type u} (K : Type (max u v)) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k) :
    geometricallyReducedCommHopfAlgProperty K
        (CommHopfAlgCat.baseChange (K := K) H) ↔
      geometricallyReducedCommHopfAlgProperty k H :=
  ⟨geometricallyReducedCommHopfAlgProperty.of_baseChange K H,
    geometricallyReducedCommHopfAlgProperty.baseChange K⟩

end TauCeti
