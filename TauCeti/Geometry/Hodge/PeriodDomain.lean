/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dimension
public import TauCeti.Geometry.Hodge.Tate

/-!
# Points of a period domain

Fix a lattice `V` — a finitely generated free `ℤ`-module — an integral bilinear form `Qint` on it,
and a prescribed family of Hodge numbers. A **point of the period domain** is a Hodge filtration
on the complexification of `V` that has those Hodge numbers and is polarized by that *same* form:
only the filtration varies from point to point, which is what makes the collection a classifying
space for polarized Hodge structures of a fixed numerical type.

The prescribed numerical data is packaged as `TauCeti.Hodge.HodgeType`: a weight, Hodge numbers of
finite support, and Hodge symmetry `h p = h (weight - p)`. Every finite-dimensional Hodge structure
has one (`TauCeti.Hodge.HodgeStructureOn.hodgeType`), so the symmetry axiom excludes exactly the
unrealizable numerical types, and a point of the period domain is precisely a polarized Hodge
structure whose own Hodge type is the prescribed one
(`TauCeti.Hodge.PeriodDomain.Point.hodgeType_eq`).

The main theorem is the numerical shadow of the Hodge decomposition: the prescribed Hodge numbers
sum to the dimension of the complexification, equivalently to the rank of the lattice. It is a
genuine constraint on a `HodgeType`, since it rules out every type whose Hodge numbers do not add
up to the rank of the lattice one wants to carry it.

The symmetry group `Aut(V, Qint)` of the pair — where the monodromy of a variation of Hodge
structure lands — is not redefined here: it is `TauCeti.BilinForm.isometryGroup Qint`, the subgroup
of `V ≃ₗ[ℤ] V` cut out by `TauCeti.BilinForm.IsIsometry`. The complex-manifold structure on the set
of period-domain points is out of scope; it needs flag-variety topology.

## Main declarations

* `TauCeti.Hodge.HodgeType`: a weight and a symmetric, finitely supported family of Hodge numbers.
* `TauCeti.Hodge.HodgeStructureOn.hodgeType`: the Hodge type of a Hodge structure.
* `TauCeti.Hodge.PeriodDomain.Point`: a point of the period domain of `(V, Qint)` at a fixed type.
* `TauCeti.Hodge.PeriodDomain.Point.finsum_h`: **the Hodge numbers partition the dimension.**
* `TauCeti.Hodge.tateHodgeType`: the Hodge type of the Tate structure `ℤ(m)`.
* `TauCeti.Hodge.tatePoint`: the Tate structure `ℤ(m)` as a point of its period domain.

The signatures of `HodgeType` and `PeriodDomain.Point` are adapted from the roadmap's formal
companion `HodgeStructures/Suggested.lean`. The mathematics follows Griffiths, *Periods of
integrals on algebraic manifolds II*, §1, and Carlson–Müller-Stach–Peters, *Period Mappings and
Period Domains*, §4. This is Layer L3 of `TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge

universe u v

/-- The numerical type of a pure Hodge structure: a weight, Hodge numbers `h` of finite support,
and the **Hodge symmetry** `h p = h (weight - p)`.

The symmetry is not an extra restriction on the types that occur, since conjugation exchanges the
Hodge components `H^{p,q}` and `H^{q,p}` of any Hodge structure; it excludes the asymmetric
families of numbers that no Hodge structure realizes. -/
@[ext]
structure HodgeType where
  /-- The weight of the Hodge structures of this type. -/
  weight : ℤ
  /-- The prescribed Hodge numbers. -/
  h : ℤ → ℕ
  /-- All but finitely many Hodge numbers vanish. -/
  finite_support : {p | h p ≠ 0}.Finite
  /-- Hodge symmetry: `h^{p,q} = h^{q,p}`. -/
  symm : ∀ p, h p = h (weight - p)

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The Hodge type of a finite-dimensional Hodge structure: its weight together with its own Hodge
numbers. -/
noncomputable def hodgeType (hs : HodgeStructureOn W ω n) [hW : FiniteDimensional ℂ W] :
    HodgeType where
  weight := n
  h := hs.hodgeNumber
  finite_support := by
    refine hs.finite_setOf_piece_ne_bot.subset fun p hp hbot ↦ hp ?_
    rw [hodgeNumber_def]
    exact Submodule.finrank_eq_zero.mpr hbot
  symm := hs.hodgeNumber_symm

@[simp]
theorem hodgeType_weight (hs : HodgeStructureOn W ω n) [FiniteDimensional ℂ W] :
    hs.hodgeType.weight = n :=
  (rfl)

@[simp]
theorem hodgeType_h (hs : HodgeStructureOn W ω n) [FiniteDimensional ℂ W] :
    hs.hodgeType.h = hs.hodgeNumber :=
  (rfl)

end HodgeStructureOn

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- A **point of the period domain** of the lattice `V` with the integral form `Qint`, at the Hodge
type `htype`: a weight-`n` Hodge structure of that type which the *fixed* form `Qint` polarizes.

The lattice is a finitely generated free `ℤ`-module, so the complexification is finite-dimensional
and the prescribed Hodge numbers really are the dimensions of the Hodge components.

The form does not vary with the point; it enters through the `Prop`-valued `IsPolarization` and so
is not carried twice. -/
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

namespace PeriodDomain.Point

variable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {Qint : LinearMap.BilinForm ℤ V} {htype : HodgeType}

/-- A point of the period domain is exactly a `Qint`-polarized Hodge structure whose own Hodge
type is the prescribed one. -/
theorem hodgeType_eq (D : PeriodDomain.Point hℂ n Qint htype) :
    D.hs.hodgeType (hW := finiteDimensional_complexification (V := V) hℂ) = htype := by
  ext p
  · exact D.htype_weight.symm
  · exact D.hodge_numbers p

/-- The structure underlying a point of the period domain is polarizable. -/
theorem isPolarizable (D : PeriodDomain.Point hℂ n Qint htype) : IsPolarizable hℂ D.hs :=
  Polarization.isPolarizable ⟨Qint, D.pol⟩

/-- **The Hodge numbers partition the dimension.** For any point of the period domain, the
prescribed Hodge numbers sum to the dimension of the complexification.

This is the numerical shadow of the Hodge decomposition `V_ℂ = ⨁_p H^{p,n-p}`. -/
theorem finsum_h (D : PeriodDomain.Point hℂ n Qint htype) :
    ∑ᶠ p, htype.h p = Module.finrank ℂ Vℂ := by
  have := finiteDimensional_complexification (V := V) hℂ
  rw [← HodgeStructureOn.finsum_hodgeNumber D.hs]
  exact finsum_congr fun p ↦ (D.hodge_numbers p).symm

/-- The prescribed Hodge numbers of a point of the period domain sum to the rank of the lattice. -/
theorem finsum_h_eq_finrank_lattice (D : PeriodDomain.Point hℂ n Qint htype) :
    ∑ᶠ p, htype.h p = Module.finrank ℤ V := by
  rw [D.finsum_h, finrank_complexification hℂ]

end PeriodDomain.Point

/-! ### The Tate structure as a period-domain point -/

/-- The Hodge type of the Tate structure `ℤ(m)`: weight `-2m`, with `h^{-m,-m} = 1` and every
other Hodge number zero. -/
def tateHodgeType (m : ℤ) : HodgeType where
  weight := -2 * m
  h p := if p = -m then 1 else 0
  finite_support := (Set.finite_singleton (-m)).subset fun p hp ↦ by
    by_contra hne
    exact hp (ite_eq_right (by simpa using hne))
  symm p := by
    have hiff : (-2 * m - p = -m) ↔ (p = -m) := by omega
    simp only [hiff]

@[simp]
theorem tateHodgeType_weight (m : ℤ) : (tateHodgeType m).weight = -2 * m :=
  (rfl)

@[simp]
theorem tateHodgeType_h (m p : ℤ) : (tateHodgeType m).h p = if p = -m then 1 else 0 :=
  (rfl)

/-- The Tate structure `ℤ(m)`, polarized by multiplication of integers, as a point of the period
domain of the rank-one lattice at its own Hodge type. -/
noncomputable def tatePoint (m : ℤ) :
    PeriodDomain.Point isBaseChange_tateLatticeMap (-2 * m) (LinearMap.mul ℤ ℤ)
      (tateHodgeType m) where
  hs := tate m
  htype_weight := (rfl)
  pol := isPolarization_tate m
  hodge_numbers p := by
    rw [HodgeStructureOn.hodgeNumber_def, finrank_tate_piece, tateHodgeType_h]

/-- The Hodge type of the Tate structure `ℤ(m)` is the prescribed one. -/
theorem tate_hodgeType (m : ℤ) : (tate m).hodgeType = tateHodgeType m :=
  (tatePoint m).hodgeType_eq

/-- The single Hodge number of `ℤ(m)` accounts for the whole rank-one lattice. -/
theorem finsum_tateHodgeType_h (m : ℤ) : ∑ᶠ p, (tateHodgeType m).h p = 1 := by
  rw [(tatePoint m).finsum_h_eq_finrank_lattice, Module.finrank_self]

end TauCeti.Hodge
