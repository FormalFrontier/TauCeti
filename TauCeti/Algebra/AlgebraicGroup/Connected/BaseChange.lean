/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat

/-!
# Geometric connectedness under base change

Geometric connectedness of a commutative Hopf algebra is preserved by extension of the base
field. If `H` is geometrically connected over `k`, then the scalar extension
`K ⊗[k] H` is geometrically connected over every field extension `K / k`.

The proof compares an arbitrary further extension `L / K` with the original geometric
connectedness condition using the canonical algebra equivalence

```text
L ⊗[K] (K ⊗[k] H) ≃ L ⊗[k] H.
```

## Main declaration

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange`: geometric connectedness is
  preserved by extension of the base field.

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
  let e := (Algebra.TensorProduct.comm K (K ⊗[k] H) L).toRingEquiv |>.trans
    ((Algebra.TensorProduct.cancelBaseChange k K L L H).toRingEquiv.trans
      (Algebra.TensorProduct.comm k L H).toRingEquiv)
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at hH
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr (hH L)

end TauCeti
