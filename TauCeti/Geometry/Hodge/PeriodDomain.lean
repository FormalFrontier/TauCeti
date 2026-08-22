/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Tate

/-!
# Points of a period domain

Fix a lattice `V` — a finitely generated free `ℤ`-module — an integral bilinear form `Qint` on it,
and a prescribed family of Hodge numbers. A **point of the period domain** is a Hodge filtration
on the complexification of `V` that has those Hodge numbers and is polarized by that *same* form:
only the filtration varies from point to point, which is what makes the collection a classifying
space for polarized Hodge structures of a fixed numerical type.

The prescribed numerical data is packaged as `TauCeti.Hodge.HodgeType`: a weight, Hodge numbers of
finite support, and Hodge symmetry `h p = h (weight - p)`. Every Hodge structure has one
(`TauCeti.Hodge.HodgeStructureOn.hodgeType`), so the symmetry axiom excludes no type that a Hodge
structure realizes, and the Hodge structure underlying a point of the period domain has the
prescribed Hodge type (`TauCeti.Hodge.PeriodDomain.Point.hodgeType_eq`).

The main theorem is the numerical shadow of the Hodge decomposition: the prescribed Hodge numbers
sum to the dimension of the complexification, equivalently to the rank of the lattice. It is a
genuine constraint on a `HodgeType`, since it rules out every type whose Hodge numbers do not add
up to the rank of the lattice one wants to carry it.

The symmetry group `Aut(V, Qint)` of the pair — where the monodromy of a variation of Hodge
structure lands — is not redefined here: it is `TauCeti.BilinForm.isometryGroup Qint`, the subgroup
of `V ≃ₗ[ℤ] V` cut out by `TauCeti.BilinForm.IsIsometry`. The complex-manifold structure on the set
of period-domain points is out of scope; it needs flag-variety topology.

## Main declarations

* `TauCeti.Hodge.PeriodDomain.Point`: a point of the period domain of `(V, Qint)` at a fixed type.
* `TauCeti.Hodge.PeriodDomain.Point.finsum_h_eq_finrank`: **the Hodge numbers partition the
  dimension.**
* `TauCeti.Hodge.tatePoint`: the Tate structure `ℤ(m)` as a point of its period domain.

The signature of `PeriodDomain.Point` is adapted from the roadmap's formal companion
`HodgeStructures/Suggested.lean`. The mathematics follows Griffiths, *Periods of integrals on
algebraic manifolds II*, §1, and Carlson–Müller-Stach–Peters, *Period Mappings and Period Domains*,
§4. This is Layer L3 of `TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- A **point of the period domain** of the lattice `V` with the integral form `Qint`, at the Hodge
type `htype`: a weight-`n` Hodge structure of that type which the *fixed* form `Qint` polarizes.

The lattice is a finitely generated free `ℤ`-module, so the complexification is finite-dimensional
and the prescribed Hodge numbers really are the dimensions of the Hodge components.

The form does not vary with the point; it enters through the `Prop`-valued `IsPolarization` and so
is not carried twice.

The `Module.Free` and `Module.Finite` binders are spelled out on the header rather than left to the
surrounding `variable` block: automatic instance inclusion applies to theorems, not to a
`structure`, so omitting them would drop them from the signature entirely. -/
structure PeriodDomain.Point [Module.Free ℤ V] [Module.Finite ℤ V] (hℂ : IsBaseChange ℂ ιℂ)
    (n : ℤ) (Qint : LinearMap.BilinForm ℤ V) (htype : HodgeType) where
  /-- The varying datum: a Hodge filtration on the complexification. -/
  hs : HodgeStructure hℂ n
  /-- The Hodge type's weight is the weight of the structure. -/
  htype_weight : htype.weight = n
  /-- The fixed form polarizes the structure. -/
  pol : IsPolarization hℂ hs Qint
  /-- The structure realizes the prescribed Hodge numbers. -/
  hodge_numbers : ∀ p : ℤ, hs.hodgeNumber p = htype.h p

attribute [simp] PeriodDomain.Point.hodge_numbers

namespace PeriodDomain.Point

variable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {Qint : LinearMap.BilinForm ℤ V} {htype : HodgeType}

/-- Two points of the period domain agree as soon as their Hodge filtrations do: the remaining
fields are propositions. -/
@[ext]
theorem ext {D D' : PeriodDomain.Point hℂ n Qint htype} (h : D.hs = D'.hs) : D = D' := by
  cases D
  cases D'
  subst h
  rfl

/-- The Hodge structure underlying a point of the period domain has the prescribed Hodge type. -/
@[simp]
theorem hodgeType_eq (D : PeriodDomain.Point hℂ n Qint htype) : D.hs.hodgeType = htype := by
  ext p
  · rw [HodgeStructureOn.hodgeType_weight]
    exact D.htype_weight.symm
  · rw [HodgeStructureOn.hodgeType_h]
    exact D.hodge_numbers p

/-- The structure underlying a point of the period domain is polarizable. -/
theorem isPolarizable (D : PeriodDomain.Point hℂ n Qint htype) : IsPolarizable hℂ D.hs :=
  Polarization.isPolarizable ⟨Qint, D.pol⟩

/-- **The Hodge numbers partition the dimension.** For any point of the period domain, the
prescribed Hodge numbers sum to the dimension of the complexification.

This is the numerical shadow of the Hodge decomposition `V_ℂ = ⨁_p H^{p,n-p}`. -/
theorem finsum_h_eq_finrank (D : PeriodDomain.Point hℂ n Qint htype) :
    ∑ᶠ p, htype.h p = Module.finrank ℂ Vℂ := by
  have := finite_of_isBaseChange hℂ
  rw [← HodgeStructureOn.finsum_hodgeNumber_eq_finrank D.hs]
  exact finsum_congr fun p ↦ (D.hodge_numbers p).symm

/-- The prescribed Hodge numbers of a point of the period domain sum to the rank of the lattice. -/
theorem finsum_h_eq_finrank_lattice (D : PeriodDomain.Point hℂ n Qint htype) :
    ∑ᶠ p, htype.h p = Module.finrank ℤ V := by
  rw [D.finsum_h_eq_finrank, finrank_of_isBaseChange hℂ]

end PeriodDomain.Point

/-! ### The Tate structure as a period-domain point -/

/-- The Tate structure `ℤ(m)`, polarized by multiplication of integers, as a point of the period
domain of the rank-one lattice at its own Hodge type. -/
noncomputable def tatePoint (m : ℤ) :
    PeriodDomain.Point isBaseChange_tateLatticeMap (-2 * m) (LinearMap.mul ℤ ℤ)
      (tateHodgeType m) where
  hs := tate m
  htype_weight := tateHodgeType_weight m
  pol := isPolarization_tate m
  hodge_numbers p := by
    rw [tate_hodgeNumber, tateHodgeType_h]

end TauCeti.Hodge
