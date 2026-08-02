/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.MetricSpace

/-!
# Disc automorphisms as Poincaré isometric equivalences

This file bundles the standard automorphisms of the complex unit disc as isometric
equivalences of `PoincareDisc`. The underlying distance-preservation results are proved in
`Poincare/MetricSpace.lean`; the bundled form records both the isometry and the inverse and is
therefore the natural API for the automorphism group acting on the Poincaré disc.

The main constructions are:

* `PoincareDisc.isometryEquivOfHyperbolicDistEq`, which transports any
  hyperbolic-distance-preserving equivalence of `Complex.UnitDisc`;
* `PoincareDisc.unitDiscMoebiusIsometryEquiv`, for the automorphism sending `a` to zero;
* `PoincareDisc.unitDiscStandardAutomorphismIsometryEquiv`, for
  `z ↦ u * (z - a) / (1 - conj a * z)`;
* `PoincareDisc.starIsometryEquiv`, for the conjugation `z ↦ conj z`, which is a Poincaré
  isometry without being a disc automorphism: it is the orientation-reversing symmetry.

This advances the conformal-mapping roadmap's L2 targets for the Poincaré metric and the disc
automorphism group. It reuses Tau Ceti's disc-automorphism and hyperbolic-distance invariance
API. As with the rest of the L0--L3 conformal-mapping material, it is coordinated with the
upstream Mathlib Riemann-mapping effort leanprover-community/mathlib4#33505 and should be
refactored to upstream API if that work lands a human-curated Poincaré-disc isometry API.
-/

public section

namespace TauCeti

open _root_.Complex

namespace PoincareDisc

/-- A hyperbolic-distance-preserving equivalence of the unit disc induces an isometric
equivalence of the Poincaré disc. -/
noncomputable def isometryEquivOfHyperbolicDistEq
    (e : Complex.UnitDisc ≃ Complex.UnitDisc)
    (he : ∀ z w : Complex.UnitDisc,
      hyperbolicDist (e z : ℂ) (e w : ℂ) = hyperbolicDist (z : ℂ) (w : ℂ)) :
    PoincareDisc ≃ᵢ PoincareDisc where
  toEquiv := toUnitDisc.trans (e.trans Complex.UnitDisc.toPoincare)
  isometry_toFun := isometry_of_hyperbolicDist_eq he

/-- The underlying function of the transported isometric equivalence is the original unit-disc
equivalence, conjugated by the identity reinterpretation maps. -/
@[simp]
lemma isometryEquivOfHyperbolicDistEq_apply (e : Complex.UnitDisc ≃ Complex.UnitDisc)
    (he : ∀ z w : Complex.UnitDisc,
      hyperbolicDist (e z : ℂ) (e w : ℂ) = hyperbolicDist (z : ℂ) (w : ℂ))
    (z : PoincareDisc) :
    isometryEquivOfHyperbolicDistEq e he z =
      Complex.UnitDisc.toPoincare (e (toUnitDisc z)) :=
  (rfl)

/-- Taking the inverse commutes with transporting a hyperbolic-distance-preserving equivalence
to the Poincaré disc. -/
lemma isometryEquivOfHyperbolicDistEq_symm (e : Complex.UnitDisc ≃ Complex.UnitDisc)
    (he : ∀ z w : Complex.UnitDisc,
      hyperbolicDist (e z : ℂ) (e w : ℂ) = hyperbolicDist (z : ℂ) (w : ℂ)) :
    (isometryEquivOfHyperbolicDistEq e he).symm =
      isometryEquivOfHyperbolicDistEq e.symm
        (fun z w => by
          rw [← he (e.symm z) (e.symm w)]
          simp) := by
  ext z
  rfl

/-- The standard disc automorphism with rotation `u` and center `a` as an isometric
equivalence of the Poincaré disc. -/
noncomputable def unitDiscStandardAutomorphismIsometryEquiv
    (u : Circle) (a : Complex.UnitDisc) : PoincareDisc ≃ᵢ PoincareDisc :=
  isometryEquivOfHyperbolicDistEq (unitDiscStandardAutomorphismEquiv u a)
    (hyperbolicDist_unitDiscStandardAutomorphismEquiv u a)

/-- The standard Poincaré isometry acts by the standard unit-disc automorphism. -/
@[simp]
lemma unitDiscStandardAutomorphismIsometryEquiv_apply
    (u : Circle) (a : Complex.UnitDisc) (z : PoincareDisc) :
    unitDiscStandardAutomorphismIsometryEquiv u a z =
      Complex.UnitDisc.toPoincare
        (unitDiscStandardAutomorphismEquiv u a (toUnitDisc z)) :=
  (rfl)

/-- The inverse of the standard Poincaré isometry applies the inverse rotation followed by the
inverse Moebius factor. -/
@[simp]
lemma unitDiscStandardAutomorphismIsometryEquiv_symm_apply
    (u : Circle) (a : Complex.UnitDisc) (z : PoincareDisc) :
    (unitDiscStandardAutomorphismIsometryEquiv u a).symm z =
      Complex.UnitDisc.toPoincare
        (unitDiscMoebiusEquiv (-a) (u⁻¹ • toUnitDisc z)) := by
  -- Unfold the transport through the identity reinterpretation maps to expose its inverse.
  change Complex.UnitDisc.toPoincare
      ((unitDiscStandardAutomorphismEquiv u a).symm (toUnitDisc z)) = _
  rw [unitDiscStandardAutomorphismEquiv_symm]
  rfl

/-- Complex conjugation as an isometric equivalence of the Poincaré disc. It is not a disc
automorphism, being orientation-reversing rather than holomorphic, but it does preserve the
hyperbolic distance (`TauCeti.hyperbolicDist_conj`); together with the standard automorphisms it
exhausts the Poincaré isometries. -/
noncomputable def starIsometryEquiv : PoincareDisc ≃ᵢ PoincareDisc :=
  isometryEquivOfHyperbolicDistEq (star_involutive.toPerm star) fun z w => by
    -- `Complex.UnitDisc.coe_star` turns the coerced `star` into `conj`, and conjugation is a
    -- hyperbolic isometry by `TauCeti.hyperbolicDist_conj`.
    simp

/-- The conjugation isometry of the Poincaré disc acts by `star` on the underlying disc. -/
@[simp]
lemma starIsometryEquiv_apply (z : PoincareDisc) :
    starIsometryEquiv z = Complex.UnitDisc.toPoincare (star (toUnitDisc z)) :=
  (rfl)

/-- Conjugation is an involution of the Poincaré disc, so it is its own inverse. -/
@[simp]
lemma starIsometryEquiv_symm : starIsometryEquiv.symm = starIsometryEquiv := by
  ext z
  -- Both sides become `z` after applying the injective map `starIsometryEquiv`: on the left by
  -- `IsometryEquiv.apply_symm_apply`, on the right because `star` is an involution.
  refine starIsometryEquiv.injective ?_
  rw [starIsometryEquiv.apply_symm_apply, starIsometryEquiv_apply, starIsometryEquiv_apply,
    toUnitDisc_toPoincare, star_star, toPoincare_toUnitDisc]

/-- The disc Moebius automorphism centred at `a` as an isometric equivalence of the Poincaré
disc. -/
noncomputable def unitDiscMoebiusIsometryEquiv (a : Complex.UnitDisc) :
    PoincareDisc ≃ᵢ PoincareDisc :=
  unitDiscStandardAutomorphismIsometryEquiv 1 a

/-- The Moebius Poincaré isometry acts by the usual unit-disc Moebius automorphism. -/
@[simp]
lemma unitDiscMoebiusIsometryEquiv_apply (a : Complex.UnitDisc) (z : PoincareDisc) :
    unitDiscMoebiusIsometryEquiv a z =
      Complex.UnitDisc.toPoincare (unitDiscMoebius a (toUnitDisc z)) := by
  rw [unitDiscMoebiusIsometryEquiv,
    unitDiscStandardAutomorphismIsometryEquiv_apply]
  rw [unitDiscStandardAutomorphismEquiv_one, unitDiscMoebiusEquiv_apply]

/-- The inverse of the Moebius Poincaré isometry centred at `a` is the one centred at `-a`. -/
@[simp]
lemma unitDiscMoebiusIsometryEquiv_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusIsometryEquiv a).symm = unitDiscMoebiusIsometryEquiv (-a) := by
  ext z
  simp [unitDiscMoebiusIsometryEquiv]

/-- With unit rotation factor, the standard Poincaré isometry is the Moebius isometry. -/
@[simp]
lemma unitDiscStandardAutomorphismIsometryEquiv_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismIsometryEquiv 1 a = unitDiscMoebiusIsometryEquiv a :=
  (rfl)

/-- The standard Poincaré isometry sends its center to the origin. -/
lemma unitDiscStandardAutomorphismIsometryEquiv_self
    (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismIsometryEquiv u a
      (Complex.UnitDisc.toPoincare a) = Complex.UnitDisc.toPoincare 0 := by
  simp

end PoincareDisc

end TauCeti
