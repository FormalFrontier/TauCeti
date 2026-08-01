/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic

/-!
# Disc automorphisms on the closed disc and on the unit circle

A disc automorphism `z ↦ u * (z - a) / (1 - conj a * z)` is given by a formula that already makes
sense on the *closed* disc: for `‖a‖ < 1` and `‖z‖ ≤ 1` the product `conj a * z` has norm
`‖a‖ * ‖z‖ ≤ ‖a‖ < 1`, so the denominator never vanishes there.  This file shows that the formula
is a homeomorphism of `closedBall (0 : ℂ) 1` onto itself which carries `sphere 0 1` onto
`sphere 0 1`, so that the automorphism group of the disc acts on the boundary circle.

The computational heart is a one-line identity: for `‖z‖ = 1`,
`conj z * (1 - conj a * z) = conj (z - a)`, so numerator and denominator of the Moebius factor have
the *same* modulus on the unit circle and the quotient has modulus one.  That identity and its
pseudo-hyperbolic reading — a boundary point is at pseudo-hyperbolic distance exactly `1` from
every other point — are generic facts about `TauCeti.pseudoHyperbolicExpr` and live in
`TauCeti/Analysis/Complex/Conformal/PseudoHyperbolic.lean`, as
`TauCeti.norm_sub_eq_norm_one_sub_conj_mul_of_norm_eq_one` and
`TauCeti.pseudoHyperbolicExpr_eq_one_of_norm_eq_one_of_norm_lt_one`.

## Main statements

* `TauCeti.bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one` and
  `TauCeti.bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one`: the scalar Moebius factor is a
  bijection of the closed disc, and of the unit circle, onto itself.
* `TauCeti.unitDiscMoebiusClosedBallHomeomorph` and `TauCeti.unitDiscMoebiusSphereHomeomorph`: those
  bijections bundled as homeomorphisms, with the factor centred at `-a` as the explicit inverse.
* `TauCeti.unitDiscStandardAutomorphismClosedBallHomeomorph` and
  `TauCeti.unitDiscStandardAutomorphismSphereHomeomorph`: the same for the full standard
  automorphism, rotation factor included.
* `TauCeti.unitDiscMoebiusClosedBallHomeomorph_mk_coe_unitDisc` and its three siblings: the
  commuting squares saying that the closed-disc maps *extend* the open-disc automorphisms
  `TauCeti.unitDiscMoebiusEquiv` / `TauCeti.unitDiscStandardAutomorphismEquiv`, and *restrict* to
  the circle maps along the inclusions `ball 0 1 ⊆ closedBall 0 1` and
  `sphere 0 1 ⊆ closedBall 0 1`.

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

variable {a u : ℂ}

/-! ## The Moebius factor on the closed disc -/

/-- The scalar unit-disc Moebius formula maps the unit circle to itself: on the circle its modulus
is the pseudo-hyperbolic expression, which equals one there. -/
theorem mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz ⊢
  rw [← pseudoHyperbolicExpr_def]
  exact pseudoHyperbolicExpr_eq_one_of_norm_eq_one_of_norm_lt_one hz ha

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

/-- The scalar unit-disc Moebius formula is continuous on the *closed* unit disc: there
`‖conj a * z‖ = ‖a‖ * ‖z‖ ≤ ‖a‖ < 1`, so the denominator is nowhere zero. -/
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
@[simp, norm_cast]
lemma coe_unitDiscMoebiusClosedBallHomeomorph_apply (a : Complex.UnitDisc)
    (z : closedBall (0 : ℂ) 1) :
    (unitDiscMoebiusClosedBallHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) := by
  simp only [unitDiscMoebiusClosedBallHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, BijOn.equiv, Equiv.coe_ofBijective,
    MapsTo.val_restrict_apply]

/-- The inverse of the closed-disc homeomorphism is given by the Moebius formula centred at `-a`. -/
-- Not `@[simp]`: `simp` already reduces the left-hand side, rewriting with the `@[simp]` lemma
-- `unitDiscMoebiusClosedBallHomeomorph_symm` and then with
-- `coe_unitDiscMoebiusClosedBallHomeomorph_apply`, so tagging this lemma `@[simp]` is a `simpNF`
-- violation.
@[norm_cast]
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
@[simp, norm_cast]
lemma coe_unitDiscMoebiusSphereHomeomorph_apply (a : Complex.UnitDisc) (z : sphere (0 : ℂ) 1) :
    (unitDiscMoebiusSphereHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) := by
  simp only [unitDiscMoebiusSphereHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, BijOn.equiv, Equiv.coe_ofBijective,
    MapsTo.val_restrict_apply]

/-- The inverse of the circle homeomorphism is given by the Moebius formula centred at `-a`. -/
-- Not `@[simp]`, for the same reason as the closed-ball lemma above: `simp` reduces the left-hand
-- side through `unitDiscMoebiusSphereHomeomorph_symm`.
@[norm_cast]
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

/-- **The closed-disc Moebius homeomorphism extends the open-disc Moebius equivalence.** The square
formed by `TauCeti.unitDiscMoebiusEquiv`, `TauCeti.unitDiscMoebiusClosedBallHomeomorph` and the
inclusion `ball 0 1 ⊆ closedBall 0 1` commutes. -/
@[simp]
lemma unitDiscMoebiusClosedBallHomeomorph_mk_coe_unitDisc (a z : Complex.UnitDisc) :
    unitDiscMoebiusClosedBallHomeomorph a ⟨(z : ℂ), mem_closedBall_zero_iff.mpr z.norm_lt_one.le⟩ =
      ⟨(unitDiscMoebiusEquiv a z : ℂ),
        mem_closedBall_zero_iff.mpr (unitDiscMoebiusEquiv a z).norm_lt_one.le⟩ := by
  have h : (unitDiscMoebiusEquiv a z : ℂ)
      = ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) := by
    rw [unitDiscMoebiusEquiv_apply, coe_unitDiscMoebius]
  ext
  rw [coe_unitDiscMoebiusClosedBallHomeomorph_apply]
  exact h.symm

/-- **The circle Moebius homeomorphism is the restriction of the closed-disc one.** The square
formed by the two homeomorphisms and the inclusion `sphere 0 1 ⊆ closedBall 0 1` commutes. -/
@[simp]
lemma unitDiscMoebiusClosedBallHomeomorph_mk_coe_sphere (a : Complex.UnitDisc)
    (z : sphere (0 : ℂ) 1) :
    unitDiscMoebiusClosedBallHomeomorph a ⟨(z : ℂ), sphere_subset_closedBall z.2⟩ =
      ⟨(unitDiscMoebiusSphereHomeomorph a z : ℂ),
        sphere_subset_closedBall (unitDiscMoebiusSphereHomeomorph a z).2⟩ := by
  ext
  rw [coe_unitDiscMoebiusClosedBallHomeomorph_apply, coe_unitDiscMoebiusSphereHomeomorph_apply]

/-! ## The full standard automorphism -/

/-- A rotation factor is undone by its conjugate: Mathlib's `Complex.conj_mul'` specialized to
`‖u‖ = 1`.  This is the only computation the rotation factor of a standard automorphism needs, so
it is recorded once here instead of being reproved at each use below. -/
private lemma conj_mul_eq_one_of_norm_eq_one (hu : ‖u‖ = 1) : (starRingEnd ℂ) u * u = 1 := by
  rw [Complex.conj_mul', hu, Complex.ofReal_one, one_pow]

/-- Multiplication by a unit-modulus scalar is a bijection of any norm-invariant set of `ℂ` onto
itself.  The underlying permutation of `ℂ` is Mathlib's `Equiv.mulLeft₀`, and `‖u‖ = 1` makes it
norm-preserving, so it preserves membership in `s` both ways.  Below this supplies the rotation
factor of a standard automorphism on `closedBall 0 1` and on `sphere 0 1` alike. -/
private lemma bijOn_mul_left_of_norm_eq_one (hu : ‖u‖ = 1) {s : Set ℂ}
    (hs : ∀ z w : ℂ, ‖z‖ = ‖w‖ → (z ∈ s ↔ w ∈ s)) :
    BijOn (fun w : ℂ => u * w) s s := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  exact (Equiv.mulLeft₀ u hu0).bijOn fun w => hs (u * w) w (by rw [norm_mul, hu, one_mul])

/-- The rotation factor of a standard disc automorphism preserves the unit circle. -/
theorem mapsTo_sphere_unitDiscStandardAutomorphismFormula_of_norm_eq_one_of_norm_lt_one
    (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    MapsTo (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro z hz
  have h := mapsTo_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha hz
  rw [mem_sphere_zero_iff_norm] at h ⊢
  rw [norm_mul, hu, one_mul, h]

/-- The rotation factor of a standard disc automorphism preserves the closed unit disc. -/
theorem mapsTo_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one_of_norm_lt_one
    (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
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

/-- **A standard disc automorphism is a bijection of the closed unit disc onto itself.** It is the
Moebius factor followed by the rotation by `u`, each a bijection of the closed disc. -/
theorem bijOn_closedBall_unitDiscStandardAutomorphismFormula_of_norm_eq_one_of_norm_lt_one
    (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  have hrot := bijOn_mul_left_of_norm_eq_one (s := closedBall (0 : ℂ) 1) hu fun z w h => by
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, h]
  simpa only [Function.comp_def] using
    hrot.comp (bijOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- **A standard disc automorphism is a bijection of the unit circle onto itself**: the boundary
action of `Aut(𝔻)`.  Again the Moebius factor followed by the rotation by `u`, now on the
circle. -/
theorem bijOn_sphere_unitDiscStandardAutomorphismFormula_of_norm_eq_one_of_norm_lt_one
    (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    BijOn (fun z : ℂ => u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  have hrot := bijOn_mul_left_of_norm_eq_one (s := sphere (0 : ℂ) 1) hu fun z w h => by
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, h]
  simpa only [Function.comp_def] using
    hrot.comp (bijOn_sphere_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- A point of `Circle` as a point of the unit sphere of `ℂ`, which is the index type of Mathlib's
actions `Metric.mulActionSphereClosedBall` and `Metric.mulActionSphereSphere`.  Those actions are
what rotates the closed disc and the circle below. -/
private def circleToUnitSphere (u : Circle) : sphere (0 : ℂ) 1 :=
  ⟨(u : ℂ), mem_sphere_zero_iff_norm.mpr u.norm_coe⟩

/-- Mathlib's action of the unit sphere of `ℂ` on `closedBall (0 : ℂ) 1` is multiplication in `ℂ`:
`Metric.mulActionSphereClosedBall` is defined by `c • x = ⟨(c : ℂ) * (x : ℂ), _⟩`, so this unfolds
the instance.  The corresponding statement for the action on `sphere (0 : ℂ) 1` is already available
upstream, as `Metric.unitSphere.coe_mul`. -/
private lemma coe_sphere_smul_closedBall (c : sphere (0 : ℂ) 1) (x : closedBall (0 : ℂ) 1) :
    ((c • x : closedBall (0 : ℂ) 1) : ℂ) = (c : ℂ) * (x : ℂ) :=
  rfl

/-- **A standard disc automorphism, as a homeomorphism of the closed disc.** It is the Moebius
factor `TauCeti.unitDiscMoebiusClosedBallHomeomorph` followed by the rotation by `u`, the latter
being Mathlib's continuous action of the unit sphere of `ℂ` on `closedBall (0 : ℂ) 1`
(`Metric.mulActionSphereClosedBall`) bundled by `Homeomorph.smul`.  The definition is not exposed;
`TauCeti.coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply` characterizes it. -/
noncomputable def unitDiscStandardAutomorphismClosedBallHomeomorph (u : Circle)
    (a : Complex.UnitDisc) : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
  (unitDiscMoebiusClosedBallHomeomorph a).trans (Homeomorph.smul (circleToUnitSphere u))

/-- The closed-disc automorphism homeomorphism is given by the standard automorphism formula. -/
@[simp, norm_cast]
lemma coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply (u : Circle)
    (a : Complex.UnitDisc) (z : closedBall (0 : ℂ) 1) :
    (unitDiscStandardAutomorphismClosedBallHomeomorph u a z : ℂ) =
      (u : ℂ) * (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  rw [unitDiscStandardAutomorphismClosedBallHomeomorph, Homeomorph.trans_apply,
    Homeomorph.smul_apply, coe_sphere_smul_closedBall,
    coe_unitDiscMoebiusClosedBallHomeomorph_apply, circleToUnitSphere]

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
@[simp, norm_cast]
lemma coe_unitDiscStandardAutomorphismClosedBallHomeomorph_symm_apply (u : Circle)
    (a : Complex.UnitDisc) (w : closedBall (0 : ℂ) 1) :
    ((unitDiscStandardAutomorphismClosedBallHomeomorph u a).symm w : ℂ) =
      ((starRingEnd ℂ) (u : ℂ) * (w : ℂ) - (-(a : ℂ))) /
        (1 - (starRingEnd ℂ) (-(a : ℂ)) * ((starRingEnd ℂ) (u : ℂ) * (w : ℂ))) := by
  set x : ℂ := ((unitDiscStandardAutomorphismClosedBallHomeomorph u a).symm w : ℂ) with hx
  have huu : (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = 1 :=
    conj_mul_eq_one_of_norm_eq_one u.norm_coe
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

/-- **A standard disc automorphism, as a homeomorphism of the unit circle.** The boundary
restriction of `TauCeti.unitDiscStandardAutomorphismClosedBallHomeomorph`, and the boundary action
of `Aut(𝔻)` on the circle.  Again the Moebius factor followed by the rotation by `u`, now through
Mathlib's action of the unit sphere of `ℂ` on `sphere (0 : ℂ) 1` (`Metric.mulActionSphereSphere`).
The definition is not exposed;
`TauCeti.coe_unitDiscStandardAutomorphismSphereHomeomorph_apply` and
`TauCeti.coe_unitDiscStandardAutomorphismSphereHomeomorph_symm_apply` characterize it. -/
noncomputable def unitDiscStandardAutomorphismSphereHomeomorph (u : Circle)
    (a : Complex.UnitDisc) : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
  (unitDiscMoebiusSphereHomeomorph a).trans (Homeomorph.smul (circleToUnitSphere u))

/-- The circle automorphism homeomorphism is given by the standard automorphism formula. -/
@[simp, norm_cast]
lemma coe_unitDiscStandardAutomorphismSphereHomeomorph_apply (u : Circle) (a : Complex.UnitDisc)
    (z : sphere (0 : ℂ) 1) :
    (unitDiscStandardAutomorphismSphereHomeomorph u a z : ℂ) =
      (u : ℂ) * (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  rw [unitDiscStandardAutomorphismSphereHomeomorph, Homeomorph.trans_apply,
    Homeomorph.smul_apply, smul_eq_mul, unitSphere.coe_mul,
    coe_unitDiscMoebiusSphereHomeomorph_apply, circleToUnitSphere]

/-- With trivial rotation factor the standard automorphism of the circle is the Moebius factor. -/
@[simp]
lemma unitDiscStandardAutomorphismSphereHomeomorph_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismSphereHomeomorph 1 a = unitDiscMoebiusSphereHomeomorph a := by
  ext z
  rw [coe_unitDiscStandardAutomorphismSphereHomeomorph_apply,
    coe_unitDiscMoebiusSphereHomeomorph_apply, Circle.coe_one, one_mul]

/-- The inverse of the circle automorphism homeomorphism undoes the rotation first: it is the
Moebius factor centred at `-a` evaluated at `conj u * w`. -/
@[simp, norm_cast]
lemma coe_unitDiscStandardAutomorphismSphereHomeomorph_symm_apply (u : Circle)
    (a : Complex.UnitDisc) (w : sphere (0 : ℂ) 1) :
    ((unitDiscStandardAutomorphismSphereHomeomorph u a).symm w : ℂ) =
      ((starRingEnd ℂ) (u : ℂ) * (w : ℂ) - (-(a : ℂ))) /
        (1 - (starRingEnd ℂ) (-(a : ℂ)) * ((starRingEnd ℂ) (u : ℂ) * (w : ℂ))) := by
  set x : ℂ := ((unitDiscStandardAutomorphismSphereHomeomorph u a).symm w : ℂ) with hx
  have huu : (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = 1 :=
    conj_mul_eq_one_of_norm_eq_one u.norm_coe
  have himg : (u : ℂ) * ((x - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * x)) = (w : ℂ) := by
    rw [hx, ← coe_unitDiscStandardAutomorphismSphereHomeomorph_apply u a,
      Homeomorph.apply_symm_apply]
  have hmoe : (x - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * x)
      = (starRingEnd ℂ) (u : ℂ) * (w : ℂ) := by
    rw [← himg, ← mul_assoc, huu, one_mul]
  have hinv := leftInvOn_closedBall_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one
    (sphere_subset_closedBall ((unitDiscStandardAutomorphismSphereHomeomorph u a).symm w).2)
  simp only [← hx, hmoe] at hinv
  exact hinv.symm

/-- **The closed-disc automorphism homeomorphism extends the open-disc standard automorphism.** The
square formed by `TauCeti.unitDiscStandardAutomorphismEquiv`,
`TauCeti.unitDiscStandardAutomorphismClosedBallHomeomorph` and the inclusion
`ball 0 1 ⊆ closedBall 0 1` commutes. -/
@[simp]
lemma unitDiscStandardAutomorphismClosedBallHomeomorph_mk_coe_unitDisc (u : Circle)
    (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismClosedBallHomeomorph u a
        ⟨(z : ℂ), mem_closedBall_zero_iff.mpr z.norm_lt_one.le⟩ =
      ⟨(unitDiscStandardAutomorphismEquiv u a z : ℂ),
        mem_closedBall_zero_iff.mpr (unitDiscStandardAutomorphismEquiv u a z).norm_lt_one.le⟩ := by
  have h := coe_unitDiscStandardAutomorphismEquiv_apply u a z
  ext
  rw [coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply]
  exact h.symm

/-- **The circle automorphism homeomorphism is the restriction of the closed-disc one.** The square
formed by the two homeomorphisms and the inclusion `sphere 0 1 ⊆ closedBall 0 1` commutes. -/
@[simp]
lemma unitDiscStandardAutomorphismClosedBallHomeomorph_mk_coe_sphere (u : Circle)
    (a : Complex.UnitDisc) (z : sphere (0 : ℂ) 1) :
    unitDiscStandardAutomorphismClosedBallHomeomorph u a
        ⟨(z : ℂ), sphere_subset_closedBall z.2⟩ =
      ⟨(unitDiscStandardAutomorphismSphereHomeomorph u a z : ℂ),
        sphere_subset_closedBall (unitDiscStandardAutomorphismSphereHomeomorph u a z).2⟩ := by
  ext
  rw [coe_unitDiscStandardAutomorphismClosedBallHomeomorph_apply,
    coe_unitDiscStandardAutomorphismSphereHomeomorph_apply]

end TauCeti
