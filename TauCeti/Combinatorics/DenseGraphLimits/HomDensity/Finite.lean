/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Real.Basic

/-!
# Homomorphism densities in a finite graph

Two densities of a finite pattern graph `F` in a finite host graph `G` on `Fin m`:

* `homDensityFin F G = |Hom(F, G)| / m ^ |V(F)|` — all homomorphisms;
* `injHomDensity F G = |Inj(F, G)| / (m)_{|V(F)|}` — the *injective* ones, normalized by the
  **falling factorial**.

These are the finite-graph front of the sampling theory. Nothing here is about graphons, and nothing
here samples: these are the estimators the later sampling laws are estimators *of*.

## The falling factorial, not the binomial coefficient

`injHomDensity` divides by `m.descFactorial k` with `k = |V(F)|`, the number of *ordered* injections
of a `k`-element set into an `m`-element set. Its numerator counts ordered injective homomorphisms,
so the two agree as conventions. Dividing instead by `Nat.choose m k` would count unordered images
against ordered maps and bias the sampling estimator by a factor of `k!` — the later unbiasedness
identity would read `k! * t(F, W)` rather than `t(F, W)`. The convention is fixed here so that no
downstream statement has to carry the correction.

## One counting convention, not two

`card_injective_hom_eq_labelledCopyCount` identifies the numerator of `injHomDensity` with Mathlib's
`SimpleGraph.labelledCopyCount`. This is proved, not assumed, and it is in this file deliberately:
without it, `injHomDensity` would silently establish a second counting convention alongside
Mathlib's. `SimpleGraph.Copy F G` is definitionally an injective homomorphism, so the bridge is an
equivalence of subtypes; note that Mathlib puts the **host** graph first, so the copy count of `F`
inside `G` is `G.labelledCopyCount F`.

## Counting with `Nat.card`

Both densities count with `Nat.card`, which is total: it returns `0` on an infinite type and needs
no `Fintype` instance or decidability on the hom type, on `G`, or on `G.Adj`. The counted types are
finite here, so no generality is lost — but the definitions can be stated and rewritten without
carrying decidability hypotheses that the analytic statements downstream would then inherit.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityFin` — the homomorphism density `t(F, G)`.
* `TauCeti.DenseGraphLimits.injHomDensity` — the injective homomorphism density `t₀(F, G)`.

## Main results

* `TauCeti.DenseGraphLimits.card_injective_hom_eq_labelledCopyCount` — the numerator of
  `injHomDensity` is Mathlib's `labelledCopyCount`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 9a — the finite hom-density
  estimators. The hom-versus-injective closeness bound
  (`homDensityFin_sub_injHomDensity_le`), the sampling laws, the unbiasedness anchor, and
  finite-graph graphons are separate targets and are not built here.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §5.2.
-/

public section

namespace TauCeti

namespace DenseGraphLimits

/-- The **homomorphism density** `t(F, G) = |Hom(F, G)| / m ^ |V(F)|` of a finite pattern graph `F`
in a finite host graph `G` on `Fin m`.

Counted with `Nat.card`, so no `Fintype` or decidability instance on the hom type or on `G` is
required. -/
noncomputable def homDensityFin {V : Type*} [Fintype V] (F : SimpleGraph V) {m : ℕ}
    (G : SimpleGraph (Fin m)) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (m ^ Fintype.card V : ℝ)

/-- The **injective homomorphism density** `t₀(F, G)`: ordered injective homomorphisms over the
falling factorial `(m)_k = m.descFactorial k`, where `k = |V(F)|`.

The denominator counts *ordered* injections `V ↪ Fin m`, matching the ordered numerator.
`Nat.choose m k` would not: it counts unordered images, and would bias the sampling estimator by
`k!`. -/
noncomputable def injHomDensity {V : Type*} [Fintype V] (F : SimpleGraph V) {m : ℕ}
    (G : SimpleGraph (Fin m)) : ℝ :=
  (Nat.card {φ : F →g G // Function.Injective φ} : ℝ) / (m.descFactorial (Fintype.card V) : ℝ)

/-- The numerator of `injHomDensity` is Mathlib's labelled copy count.

`SimpleGraph.Copy F G` is definitionally an injective homomorphism, so this is an equivalence of
subtypes. Mathlib takes the host graph first: `G.labelledCopyCount F` counts copies of `F` inside
`G`.

This settles the normalization against the existing Mathlib primitive, so `injHomDensity` does not
introduce a parallel counting convention. -/
theorem card_injective_hom_eq_labelledCopyCount {V : Type*} [Fintype V] (F : SimpleGraph V)
    {m : ℕ} (G : SimpleGraph (Fin m)) :
    Nat.card {φ : F →g G // Function.Injective φ} = G.labelledCopyCount F := by
  classical
  rw [Nat.card_congr
    ({ toFun := fun φ => ⟨φ.1, φ.2⟩
       invFun := fun c => ⟨c.toHom, c.injective'⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      {φ : F →g G // Function.Injective φ} ≃ SimpleGraph.Copy F G),
    SimpleGraph.labelledCopyCount]
  convert Nat.card_eq_fintype_card using 2

end DenseGraphLimits

end TauCeti
