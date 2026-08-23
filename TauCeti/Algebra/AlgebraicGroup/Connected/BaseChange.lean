/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.TensorProduct.CommonOverfield

/-!
# Geometric connectedness under base change

Geometric connectedness of a commutative Hopf algebra is preserved by and descends along extension
of the base field. In particular, `H` is geometrically connected over `k` if and only if the scalar
extension `K ⊗[k] H` is geometrically connected over any field extension `K / k`.

Preservation compares an arbitrary further extension `L / K` with the original geometric
connectedness condition using the canonical algebra equivalence

```text
L ⊗[K] (K ⊗[k] H) ≃ L ⊗[k] H.
```

For descent, a common overfield of `K` and an algebraically closed extension of `k` compares the
two scalar extensions, after which connectedness descends along an injective map.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange`: geometric connectedness is
  preserved by extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.of_baseChange`: geometric connectedness
  descends from an extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange_iff`: geometric connectedness is
  equivalent before and after extension of the base field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is base-change infrastructure for Layer 3, "Identity component and component group", of the
ReductiveGroups roadmap: connectedness there is geometric and is therefore used after extending
the ground field.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

/-- **Geometric connectedness is preserved by extension of the base field.**

For fields `k → K`, if the spectrum of `H ⊗[k] L` is connected for every field extension
`L / k`, then the spectrum of `(K ⊗[k] H) ⊗[K] L` is connected for every field extension
`L / K`. The two rings are identified by cancellation of successive scalar extensions. -/
theorem geometricallyConnectedCommHopfAlgProperty.baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{u} k)
    (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let _ : Algebra k L := Algebra.compHom L (algebraMap k K)
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at hH
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.baseChangeTowerRingEquiv k K H L)).connectedSpace_iff.mpr (hH L)

/-- **Geometric connectedness descends from an extension of the base field.**

If `K ⊗[k] H` is geometrically connected over a field extension `K / k`, then `H` is
geometrically connected over `k`. -/
theorem geometricallyConnectedCommHopfAlgProperty.of_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{u} k)
    (hH : geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyConnectedCommHopfAlgProperty k H := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at hH
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro L _ _ _
  let d := Algebra.TensorProduct.commonOverfield k K L
  have hΩ : ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] d.Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (d.comparison H)).connectedSpace_iff.mp (hH d.Ω)
  exact connectedSpace_primeSpectrum_of_injective (d.map H).toRingHom (d.map_injective H)

/-- Geometric connectedness is equivalent before and after extension of the base field. -/
theorem geometricallyConnectedCommHopfAlgProperty.baseChange_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty K
        (CommHopfAlgCat.baseChange (K := K) H) ↔
      geometricallyConnectedCommHopfAlgProperty k H :=
  ⟨geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H,
    geometricallyConnectedCommHopfAlgProperty.baseChange k K H⟩

end TauCeti
