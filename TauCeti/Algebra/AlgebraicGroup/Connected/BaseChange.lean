/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Geometric connectedness under base change

Geometric connectedness of a commutative Hopf algebra is preserved by and descends along extension
of the base field. In particular, `H` is geometrically connected over `k` if and only if the scalar
extension `K ⊗[k] H` is geometrically connected over any field extension `K / k`.

The proof compares an arbitrary further extension `L / K` with the original geometric
connectedness condition using the canonical algebra equivalence

```text
L ⊗[K] (K ⊗[k] H) ≃ L ⊗[k] H.
```

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.baseChange`: geometric connectedness is
  preserved by extension of the base field.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.of_baseChange`: geometric connectedness
  descends from an extension of the base field.

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
  let R := K ⊗[k] L
  let _ : Nontrivial R :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K L
      (algebraMap k K).injective (algebraMap k L).injective
  obtain ⟨P, hP⟩ := Ideal.exists_maximal R
  let _ : P.IsMaximal := hP
  let Ω := P.ResidueField
  let iK : K →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeLeft
  let iL : L →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeRight
  let _ : Algebra K Ω := iK.toRingHom.toAlgebra
  let _ : IsScalarTower k K Ω := IsScalarTower.of_algHom iK
  let e := (Algebra.TensorProduct.comm K (K ⊗[k] H) Ω).toRingEquiv |>.trans
    ((Algebra.TensorProduct.cancelBaseChange k K Ω Ω H).toRingEquiv.trans
      (Algebra.TensorProduct.comm k Ω H).toRingEquiv)
  have hΩ : ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mp (hH Ω)
  let f : (H : Type u) ⊗[k] L →ₐ[k] (H : Type u) ⊗[k] Ω :=
    Algebra.TensorProduct.map (AlgHom.id k H) iL
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap iL.toLinearMap
      (RingHom.injective iL.toRingHom)
  exact connectedSpace_primeSpectrum_of_injective f.toRingHom hf

end TauCeti
