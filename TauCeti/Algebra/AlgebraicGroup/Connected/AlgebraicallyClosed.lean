/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic

/-!
# Testing geometric connectedness over algebraically closed fields

For a commutative Hopf algebra `H` over a field `k`, geometric connectedness may be tested only
after algebraically closed extensions of `k`. For an arbitrary extension `K / k`, its algebraic
closure `Ω` is again a `k`-algebra. The map

```text
H ⊗[k] K → H ⊗[k] Ω
```

is injective because `H` is flat over the field `k`. Connectedness of the target therefore
descends to the source by the idempotent characterization of connected affine spectra.

## Main declaration

* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed`:
  geometric connectedness is equivalent to connectedness after every algebraically closed field
  extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the algebraically-closed-field reduction for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap. It is the first reduction toward expressing geometric
connectedness using a chosen algebraic closure of the ground field.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

/-- **Geometric connectedness of a commutative Hopf algebra can be tested after algebraically
closed field extensions.** -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
        ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K)) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  constructor
  · intro h K _ _ _
    exact h K
  · intro h K _ _
    let Ω := AlgebraicClosure K
    let g : K →ₐ[k] Ω := IsScalarTower.toAlgHom k K Ω
    let f : (H : Type u) ⊗[k] K →ₐ[k] (H : Type u) ⊗[k] Ω :=
      Algebra.TensorProduct.map (AlgHom.id k H) g
    have hg : Function.Injective g := RingHom.injective g.toRingHom
    have hf : Function.Injective f :=
      Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
    exact connectedSpace_primeSpectrum_of_injective f.toRingHom hf

end TauCeti
