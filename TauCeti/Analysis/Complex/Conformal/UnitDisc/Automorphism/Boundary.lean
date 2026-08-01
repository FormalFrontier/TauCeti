/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic

/-!
# Disc automorphisms on the closed disc and on the unit circle

A disc automorphism `z ↦ u * (z - a) / (1 - conj a * z)` is given by a formula that already makes
sense on the *closed* disc: the denominator only vanishes at `z = 1 / conj a`, which lies outside
`closedBall 0 1` when `‖a‖ < 1`.  This file shows that the formula is a homeomorphism of
`closedBall (0 : ℂ) 1` onto itself which carries `sphere 0 1` onto `sphere 0 1`, so that the
automorphism group of the disc acts on the boundary circle.

The computational heart is a one-line identity: for `‖z‖ = 1`,
`conj z * (1 - conj a * z) = conj (z - a)`, so numerator and denominator of the Moebius factor have
the *same* modulus on the unit circle and the quotient has modulus one
(`TauCeti.norm_sub_eq_norm_one_sub_conj_mul_of_norm_eq_one`).  In the pseudo-hyperbolic language of
`TauCeti.pseudoHyperbolicExpr` this says that a boundary point is at pseudo-hyperbolic distance
exactly `1` from every interior point.  Mathlib knows the same identity for the reciprocal,
meromorphic, factor: `Complex.norm_canonicalFactor_eval_circle_eq_one` in
`Analysis/Complex/CanonicalDecomposition.lean`, stated for `(R ^ 2 - conj w * z) / (R * (z - w))`;
the form proved here is the reciprocal one, and holds for every centre `a`, not only for
`‖a‖ < R`.

## Main statements

* `TauCeti.bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one` and
  `TauCeti.bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one`: the scalar Moebius factor is a
  bijection of the closed disc, and of the unit circle, onto itself.
* `TauCeti.unitDiscMoebiusClosedBallHomeomorph` and `TauCeti.unitDiscMoebiusSphereHomeomorph`: those
  bijections bundled as homeomorphisms, with the factor centred at `-a` as the explicit inverse.
* `TauCeti.unitDiscStandardAutomorphismClosedBallHomeomorph`: the same for the full standard
  automorphism, rotation factor included.

Two of the layers of the conformal-mapping roadmap meet here.  The **L2** target is the disc
automorphism group `Aut(𝔻) = {e^{iθ}(z - a)/(1 - conj a * z)}`, of which this file describes the
boundary action.  The **L5** Carathéodory milestone asks that a Riemann map of a Jordan domain
extend to a homeomorphism of the closures; `closedBall 0 1 = closure (ball 0 1)` is the model
Jordan domain, and the extension produced here is the model case of that conclusion — obtained
without any of the boundary machinery, since the defining formula extends by itself.  It is also
the tool that *normalizes* a boundary correspondence: precomposing a Riemann map with a disc
automorphism moves a prescribed interior point to `0` and rotates the boundary circle, and by the
results below the composite still extends to the closed disc.  Existence of the extension for a
general Riemann map is not proved here.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
any Tau Ceti overlap with the L0--L3 prerequisites is a temporary shim to be deleted or
refactored to Mathlib once the corresponding upstream API lands.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {a u z : ℂ}

/-! ## The Moebius factor on the unit circle -/

/-- **Numerator and denominator of a Moebius factor have equal modulus on the unit circle.**
For `‖z‖ = 1` the conjugate of `z` turns the denominator into the conjugate of the numerator:
`conj z * (1 - conj a * z) = conj z - conj a * (conj z * z) = conj (z - a)`.  No hypothesis on the
centre `a` is needed.

Mathlib's `Complex.norm_canonicalFactor_eval_circle_eq_one` is the same computation for the
reciprocal factor `(R ^ 2 - conj a * z) / (R * (z - a))`, under the extra hypothesis
`‖a‖ < R`. -/
theorem norm_sub_eq_norm_one_sub_conj_mul_of_norm_eq_one (hz : ‖z‖ = 1) (a : ℂ) :
    ‖z - a‖ = ‖1 - (starRingEnd ℂ) a * z‖ := by
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have key : (starRingEnd ℂ) z * (1 - (starRingEnd ℂ) a * z) = (starRingEnd ℂ) (z - a) := by
    have hexpand : (starRingEnd ℂ) z * (1 - (starRingEnd ℂ) a * z) =
        (starRingEnd ℂ) z - (starRingEnd ℂ) a * ((starRingEnd ℂ) z * z) := by ring
    rw [hexpand, hzz, mul_one, map_sub]
  calc
    ‖z - a‖ = ‖(starRingEnd ℂ) (z - a)‖ := (norm_conj _).symm
    _ = ‖(starRingEnd ℂ) z * (1 - (starRingEnd ℂ) a * z)‖ := by rw [key]
    _ = ‖1 - (starRingEnd ℂ) a * z‖ := by rw [norm_mul, norm_conj, hz, one_mul]

/-- **A point of the unit circle is at pseudo-hyperbolic distance one from any interior point.**
This is `TauCeti.norm_sub_eq_norm_one_sub_conj_mul_of_norm_eq_one` read through
`TauCeti.pseudoHyperbolicExpr`, and the boundary counterpart of
`TauCeti.pseudoHyperbolicExpr_lt_one_of_norm_lt_one`. -/
theorem pseudoHyperbolicExpr_eq_one_of_norm_eq_one (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) :
    pseudoHyperbolicExpr z a = 1 := by
  rw [pseudoHyperbolicExpr_def, norm_div, norm_sub_eq_norm_one_sub_conj_mul_of_norm_eq_one hz a,
    div_self (norm_ne_zero_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_le_one hz.le ha))]

/-! ## The Moebius factor on the closed disc -/

/-- The scalar unit-disc Moebius formula maps the unit circle to itself: on the circle its modulus
is the pseudo-hyperbolic expression, which equals one there. -/
theorem mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz ⊢
  rw [← pseudoHyperbolicExpr_def]
  exact pseudoHyperbolicExpr_eq_one_of_norm_eq_one hz ha

/-- The scalar unit-disc Moebius formula maps the closed unit disc to itself, being the union of the
open disc and the unit circle. -/
theorem mapsTo_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  intro z hz
  rw [← ball_union_sphere] at hz
  rcases hz with h | h
  · exact ball_subset_closedBall (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha h)
  · exact sphere_subset_closedBall (mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha h)

/-- The scalar unit-disc Moebius formula is continuous on the *closed* unit disc: its only pole
`1 / conj a` has modulus `1 / ‖a‖ > 1`. -/
theorem continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    ContinuousOn (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (closedBall (0 : ℂ) 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz =>
    one_sub_conj_mul_ne_zero_of_norm_le_one (mem_closedBall_zero_iff.mp hz) ha

/-- **The Moebius factor centred at `-a` inverts the one centred at `a` on the closed disc.**
The identity is known on the open disc (`TauCeti.leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one`)
and both sides are continuous on the closed disc, which is the closure of the open one, so the two
continuous functions that agree on a dense subset agree throughout. -/
theorem leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    LeftInvOn (fun z : ℂ => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z))
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z)) (closedBall (0 : ℂ) 1) := by
  have hneg : ‖(-a : ℂ)‖ < 1 := by rwa [norm_neg]
  have hcomp : ContinuousOn
      ((fun z : ℂ => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z)) ∘
        fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z)) (closedBall (0 : ℂ) 1) :=
    (continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one hneg).comp
      (continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)
      (mapsTo_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)
  exact (leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha).eqOn.of_subset_closure hcomp
    continuousOn_id ball_subset_closedBall (by rw [closure_ball (0 : ℂ) one_ne_zero])

/-- The Moebius factors centred at `a` and at `-a` are mutually inverse on the closed unit disc. -/
theorem invOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    InvOn (fun z : ℂ => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z))
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  have hneg : ‖(-a : ℂ)‖ < 1 := by rwa [norm_neg]
  refine ⟨leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha, ?_⟩
  have h := leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one hneg
  simpa only [neg_neg] using h

/-- **A Moebius factor is a bijection of the closed unit disc onto itself.** -/
theorem bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
  (invOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha).bijOn
    (mapsTo_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (mapsTo_closedBall_unitDiscMoebiusFormula_of_norm_lt_one (by rwa [norm_neg]))

/-- **A Moebius factor is a bijection of the unit circle onto itself.** This is the boundary action
of the disc automorphism group. -/
theorem bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) :=
  ((invOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha).mono sphere_subset_closedBall
      sphere_subset_closedBall).bijOn
    (mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one (by rwa [norm_neg]))

/-- **A Moebius factor is a bijection of the open unit disc onto itself.** The scalar counterpart of
the bundled `TauCeti.unitDiscMoebiusEquiv`. -/
theorem bijOn_ball_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
  ((invOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha).mono ball_subset_closedBall
      ball_subset_closedBall).bijOn
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (by rwa [norm_neg]))

/-! ## The bundled homeomorphisms of the closed disc and of the circle -/

/-- **A Moebius factor of the unit disc, as a homeomorphism of the closed disc.** Continuity of the
inverse is free: the closed disc is compact and `ℂ` is Hausdorff.

This is the model case of the Carathéodory boundary correspondence (layer **L5**): a conformal
self-map of the disc that extends to a homeomorphism of the closure.  The definition is not exposed;
`TauCeti.coe_unitDiscMoebiusClosedBallHomeomorph_apply` and
`TauCeti.coe_unitDiscMoebiusClosedBallHomeomorph_symm_apply` are its characterizations. -/
noncomputable def unitDiscMoebiusClosedBallHomeomorph (a : Complex.UnitDisc) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  haveI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  Continuous.homeoOfEquivCompactToT2
    (f := (bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).equiv _)
    ((continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).mapsToRestrict
      (bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).mapsTo)

/-- The closed-disc homeomorphism is given by the Moebius formula. -/
@[simp]
lemma coe_unitDiscMoebiusClosedBallHomeomorph_apply (a : Complex.UnitDisc)
    (z : closedBall (0 : ℂ) 1) :
    (unitDiscMoebiusClosedBallHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) := by
  simp only [unitDiscMoebiusClosedBallHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, BijOn.equiv, Equiv.coe_ofBijective,
    MapsTo.val_restrict_apply]

/-- The inverse of the closed-disc homeomorphism is given by the Moebius formula centred at `-a`. -/
lemma coe_unitDiscMoebiusClosedBallHomeomorph_symm_apply (a : Complex.UnitDisc)
    (w : closedBall (0 : ℂ) 1) :
    ((unitDiscMoebiusClosedBallHomeomorph a).symm w : ℂ) =
      ((w : ℂ) - (-(a : ℂ))) / (1 - (starRingEnd ℂ) (-(a : ℂ)) * (w : ℂ)) := by
  -- Apply the left inverse at the point `(unitDiscMoebiusClosedBallHomeomorph a).symm w`, whose
  -- image under the Moebius formula is `w`.
  have himg :
      (((unitDiscMoebiusClosedBallHomeomorph a).symm w : ℂ) - (a : ℂ)) /
          (1 - (starRingEnd ℂ) (a : ℂ) * ((unitDiscMoebiusClosedBallHomeomorph a).symm w : ℂ))
        = (w : ℂ) := by
    rw [← coe_unitDiscMoebiusClosedBallHomeomorph_apply a, Homeomorph.apply_symm_apply]
  have hinv := leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    ((unitDiscMoebiusClosedBallHomeomorph a).symm w).2
  simp only [himg] at hinv
  exact hinv.symm

/-- The inverse of the closed-disc Moebius homeomorphism is the one centred at `-a`. -/
@[simp]
lemma unitDiscMoebiusClosedBallHomeomorph_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusClosedBallHomeomorph a).symm = unitDiscMoebiusClosedBallHomeomorph (-a) := by
  ext w
  rw [coe_unitDiscMoebiusClosedBallHomeomorph_symm_apply,
    coe_unitDiscMoebiusClosedBallHomeomorph_apply, Complex.UnitDisc.coe_neg]

/-- **A Moebius factor of the unit disc, as a homeomorphism of the unit circle.** The boundary
restriction of `TauCeti.unitDiscMoebiusClosedBallHomeomorph`.

The definition is not exposed; `TauCeti.coe_unitDiscMoebiusSphereHomeomorph_apply` and
`TauCeti.coe_unitDiscMoebiusSphereHomeomorph_symm_apply` are its characterizations. -/
noncomputable def unitDiscMoebiusSphereHomeomorph (a : Complex.UnitDisc) :
    sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
  haveI : CompactSpace (sphere (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  Continuous.homeoOfEquivCompactToT2
    (f := (bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).equiv _)
    (((continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).mono
      sphere_subset_closedBall).mapsToRestrict
        (bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one).mapsTo)

/-- The circle homeomorphism is given by the Moebius formula. -/
@[simp]
lemma coe_unitDiscMoebiusSphereHomeomorph_apply (a : Complex.UnitDisc) (z : sphere (0 : ℂ) 1) :
    (unitDiscMoebiusSphereHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) := by
  simp only [unitDiscMoebiusSphereHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, BijOn.equiv, Equiv.coe_ofBijective,
    MapsTo.val_restrict_apply]

/-- The inverse of the circle homeomorphism is given by the Moebius formula centred at `-a`. -/
lemma coe_unitDiscMoebiusSphereHomeomorph_symm_apply (a : Complex.UnitDisc)
    (w : sphere (0 : ℂ) 1) :
    ((unitDiscMoebiusSphereHomeomorph a).symm w : ℂ) =
      ((w : ℂ) - (-(a : ℂ))) / (1 - (starRingEnd ℂ) (-(a : ℂ)) * (w : ℂ)) := by
  have himg :
      (((unitDiscMoebiusSphereHomeomorph a).symm w : ℂ) - (a : ℂ)) /
          (1 - (starRingEnd ℂ) (a : ℂ) * ((unitDiscMoebiusSphereHomeomorph a).symm w : ℂ))
        = (w : ℂ) := by
    rw [← coe_unitDiscMoebiusSphereHomeomorph_apply a, Homeomorph.apply_symm_apply]
  have hinv := leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    (sphere_subset_closedBall ((unitDiscMoebiusSphereHomeomorph a).symm w).2)
  simp only [himg] at hinv
  exact hinv.symm

/-- The inverse of the circle Moebius homeomorphism is the one centred at `-a`. -/
@[simp]
lemma unitDiscMoebiusSphereHomeomorph_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusSphereHomeomorph a).symm = unitDiscMoebiusSphereHomeomorph (-a) := by
  ext w
  rw [coe_unitDiscMoebiusSphereHomeomorph_symm_apply, coe_unitDiscMoebiusSphereHomeomorph_apply,
    Complex.UnitDisc.coe_neg]

/-! ## The full standard automorphism -/

/-- The rotation factor of a standard disc automorphism preserves the unit circle. -/
theorem mapsTo_sphere_unitDiscStandardAutomorphismFormula_of_norm_eq_one (hu : ‖u‖ = 1)
    (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro z hz
  have h := mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  rw [mem_sphere_zero_iff_norm] at h ⊢
  rw [norm_mul, hu, one_mul, h]

/-- The rotation factor of a standard disc automorphism preserves the closed unit disc. -/
theorem mapsTo_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one (hu : ‖u‖ = 1)
    (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  intro z hz
  have h := mapsTo_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  rw [mem_closedBall_zero_iff] at h ⊢
  rw [norm_mul, hu, one_mul]
  exact h

/-- The standard disc-automorphism formula is continuous on the closed unit disc. -/
theorem continuousOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_lt_one (u : ℂ)
    (ha : ‖a‖ < 1) :
    ContinuousOn (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (closedBall (0 : ℂ) 1) :=
  continuousOn_const.mul (continuousOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- **A standard disc automorphism is a bijection of the closed unit disc onto itself.** The
rotation by `u` is undone by the rotation by `conj u`, which is its inverse because
`‖u‖ = 1`. -/
theorem bijOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one (hu : ‖u‖ = 1)
    (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hrot : BijOn (fun w : ℂ => u * w) (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    refine InvOn.bijOn (f' := fun w : ℂ => u⁻¹ * w) ⟨fun w _ => ?_, fun w _ => ?_⟩ ?_ ?_
    · simp [inv_mul_cancel_left₀ hu0]
    · simp [mul_inv_cancel_left₀ hu0]
    · intro w hw
      rw [mem_closedBall_zero_iff] at hw ⊢
      rwa [norm_mul, hu, one_mul]
    · intro w hw
      rw [mem_closedBall_zero_iff] at hw ⊢
      rwa [norm_mul, norm_inv, hu, inv_one, one_mul]
  simpa only [Function.comp_def] using
    hrot.comp (bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- **A standard disc automorphism is a bijection of the unit circle onto itself**: the boundary
action of `Aut(𝔻)`. -/
theorem bijOn_sphere_unitDiscStandardAutomorphismFormula_of_norm_eq_one (hu : ‖u‖ = 1)
    (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  refine BijOn.mk (mapsTo_sphere_unitDiscStandardAutomorphismFormula_of_norm_eq_one hu ha)
    (((bijOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one hu ha).injOn).mono
      sphere_subset_closedBall) ?_
  intro w hw
  obtain ⟨z, hz, hzw⟩ :=
    (bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha).surjOn
      (show (starRingEnd ℂ) u * w ∈ sphere (0 : ℂ) 1 by
        rw [mem_sphere_zero_iff_norm] at hw ⊢
        rw [norm_mul, norm_conj, hu, one_mul, hw])
  refine ⟨z, hz, ?_⟩
  have hzw' : (z - a) / (1 - (starRingEnd ℂ) a * z) = (starRingEnd ℂ) u * w := hzw
  have huu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  calc
    u * ((z - a) / (1 - (starRingEnd ℂ) a * z)) = u * ((starRingEnd ℂ) u * w) := by rw [hzw']
    _ = (u * (starRingEnd ℂ) u) * w := by ring
    _ = w := by rw [huu, one_mul]

/-- **A standard disc automorphism, as a homeomorphism of the closed disc.** The definition is not
exposed; `TauCeti.coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply` characterizes it. -/
noncomputable def unitDiscStandardAutomorphismClosedBallHomeomorph (u : Circle)
    (a : Complex.UnitDisc) : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  haveI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  Continuous.homeoOfEquivCompactToT2
    (f := (bijOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one u.norm_coe
      a.norm_lt_one).equiv _)
    ((continuousOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_lt_one (u : ℂ)
      a.norm_lt_one).mapsToRestrict
        (bijOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one u.norm_coe
          a.norm_lt_one).mapsTo)

/-- The closed-disc automorphism homeomorphism is given by the standard automorphism formula. -/
@[simp]
lemma coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply (u : Circle)
    (a : Complex.UnitDisc) (z : closedBall (0 : ℂ) 1) :
    (unitDiscStandardAutomorphismClosedBallHomeomorph u a z : ℂ) =
      (u : ℂ) * (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  simp only [unitDiscStandardAutomorphismClosedBallHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, BijOn.equiv, Equiv.coe_ofBijective,
    MapsTo.val_restrict_apply]

/-- With trivial rotation factor the standard automorphism of the closed disc is the Moebius
factor. -/
@[simp]
lemma unitDiscStandardAutomorphismClosedBallHomeomorph_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismClosedBallHomeomorph 1 a =
      unitDiscMoebiusClosedBallHomeomorph a := by
  ext z
  rw [coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply,
    coe_unitDiscMoebiusClosedBallHomeomorph_apply, Circle.coe_one, one_mul]

/-- The inverse of the closed-disc automorphism homeomorphism undoes the rotation first: it is the
Moebius factor centred at `-a` evaluated at `conj u * w`. -/
@[simp]
lemma coe_unitDiscStandardAutomorphismClosedBallHomeomorph_symm_apply (u : Circle)
    (a : Complex.UnitDisc) (w : closedBall (0 : ℂ) 1) :
    ((unitDiscStandardAutomorphismClosedBallHomeomorph u a).symm w : ℂ) =
      ((starRingEnd ℂ) (u : ℂ) * (w : ℂ) - (-(a : ℂ))) /
        (1 - (starRingEnd ℂ) (-(a : ℂ)) * ((starRingEnd ℂ) (u : ℂ) * (w : ℂ))) := by
  set x : ℂ := ((unitDiscStandardAutomorphismClosedBallHomeomorph u a).symm w : ℂ) with hx
  have huu : (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_coe]
    norm_num
  have himg :
      (u : ℂ) * ((x - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * x)) = (w : ℂ) := by
    rw [hx, ← coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply u a,
      Homeomorph.apply_symm_apply]
  have hmoe : (x - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * x)
      = (starRingEnd ℂ) (u : ℂ) * (w : ℂ) := by
    rw [← himg, ← mul_assoc, huu, one_mul]
  have hinv := leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    ((unitDiscStandardAutomorphismClosedBallHomeomorph u a).symm w).2
  simp only [← hx, hmoe] at hinv
  exact hinv.symm

end TauCeti
