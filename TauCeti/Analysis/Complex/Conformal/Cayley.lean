/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.MetricSpace
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# The Cayley transform between the upper half-plane and the unit disc

The **Cayley transform** `cayleyTransform z = (z - I) / (z + I)` is the classical explicit
conformal isomorphism of the upper half-plane `UpperHalfPlane.upperHalfPlaneSet`
(Mathlib's abbreviation for the set `{z : ℂ | 0 < z.im}`) onto the open unit disc
`Metric.ball (0 : ℂ) 1`, with inverse `cayleyTransformInv w = I * (1 + w) / (1 - w)`.  It is the
one conformal map that lets the disc-based conformal-mapping library be used on the upper
half-plane, where Mathlib's `UpperHalfPlane` material lives.

The file has three parts.

*The map and its inverse.*  `norm_cayleyTransform_lt_one_iff` is the computation
`‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im` in disguise: it says that `cayleyTransform` lands in the
open unit disc exactly on the upper half-plane.  Together with the algebraic inversion
identities it gives `bijOn_cayleyTransform`, and `hasDerivAt_cayleyTransform` records the
derivative `2 * I / (z + I) ^ 2`, which never vanishes — whence `conformalAt_cayleyTransform`,
the map's conformality in Mathlib's `ConformalAt` sense.

*The conformal isomorphism.*  `exists_differentiableOn_injOn_image_eq_ball_of_im_pos` states the
conclusion of the Riemann mapping theorem for the upper half-plane, in the exact shape the
conformal-mapping roadmap fixes for it, with `cayleyTransform` as an explicit witness — no
compactness argument needed.  `cayleyTransformEquiv` and `cayleyTransformHomeomorph` package the
map as `ℍ ≃ 𝔻` and `ℍ ≃ₜ 𝔻`.

*The hyperbolic metrics.*  `pseudoHyperbolicExpr_cayleyTransform` computes the pull-back of the
pseudo-hyperbolic expression:
`pseudoHyperbolicExpr (cayleyTransform z) (cayleyTransform w) = ‖z - w‖ / ‖z - conj w‖`.
Mathlib's `UpperHalfPlane.tanh_half_dist` says that the right-hand side is
`Real.tanh (dist z w / 2)`, and `TauCeti.hyperbolicDist` is `Real.artanh` of the
pseudo-hyperbolic expression, so the two hyperbolic metrics are identified:

`hyperbolicDist (cayleyTransform z) (cayleyTransform w) = dist z w / 2`.

The factor `2` is a normalisation, not a discrepancy: `TauCeti.hyperbolicDist` is normalised to
the infinitesimal metric `|dz| / (1 - |z| ^ 2)` on the disc (curvature `-4`), while Mathlib's
`UpperHalfPlane` distance is normalised to `|dz| / z.im` (curvature `-1`), and the Cayley
transform pulls the latter back to `2 * |dz| / (1 - |w| ^ 2)`.  So the Cayley transform is a
similarity of ratio `1 / 2` between the two; in particular the L2 Poincaré metric built in this
area really is the hyperbolic metric, measured against Mathlib's independent definition of it.

This advances the conformal-mapping roadmap: it supplies the explicit L3 Riemann map of the
upper half-plane and transports the L2 Poincaré metric of `𝔻` to `ℍ` (see
`ConformalMapping/README.md`, layers L2 and L3, and the entry's commitment to supply the
conformal inputs the modular layer needs).  It reuses Tau Ceti's pseudo-hyperbolic and
hyperbolic-distance API and Mathlib's `UpperHalfPlane` metric rather than re-deriving either.
As with the rest of the L0--L3 conformal-mapping material, it is coordinated with the upstream
Mathlib Riemann mapping effort leanprover-community/mathlib4#33505 and the preceding
human-curated `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
any overlap is a temporary shim, to be deleted and refactored to Mathlib once the corresponding
upstream API lands.  Mathlib has `Complex.UnitDisc` and `UpperHalfPlane` with its hyperbolic
metric, but no map between them.
-/

public section

open Complex Metric Set
open scoped ComplexConjugate UpperHalfPlane

namespace TauCeti

/-! ### The Cayley transform and its inverse -/

/-- The **Cayley transform** `z ↦ (z - I) / (z + I)`, which maps the upper half-plane onto the
open unit disc.  Off the point `-I` it is the Möbius transformation with that formula; at `-I`
the Lean expression evaluates to `0` by the junk-value convention for division. -/
noncomputable def cayleyTransform (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `w ↦ I * (1 + w) / (1 - w)`, which maps the open unit disc onto
the upper half-plane. -/
noncomputable def cayleyTransformInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The defining formula for the Cayley transform. -/
lemma cayleyTransform_def (z : ℂ) : cayleyTransform z = (z - I) / (z + I) := by
  rw [cayleyTransform]

/-- The defining formula for the inverse Cayley transform. -/
lemma cayleyTransformInv_def (w : ℂ) : cayleyTransformInv w = I * (1 + w) / (1 - w) := by
  rw [cayleyTransformInv]

/-- The denominator of the Cayley transform is nonzero on the upper half-plane. -/
lemma add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have him : (z + I).im = 0 := by rw [h]; simp
  simp only [Complex.add_im, Complex.I_im] at him
  linarith

/-- The denominator of the inverse Cayley transform is nonzero on the open unit disc. -/
lemma one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  simp at hw

@[simp]
lemma cayleyTransform_I : cayleyTransform I = 0 := by
  rw [cayleyTransform]
  simp

@[simp]
lemma cayleyTransformInv_zero : cayleyTransformInv 0 = I := by
  rw [cayleyTransformInv]
  simp

/-- **The Cayley transform lands in the unit disc exactly on the upper half-plane.**  The proof
is the identity `‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im`. -/
theorem norm_cayleyTransform_lt_one_iff {z : ℂ} (hz : z + I ≠ 0) :
    ‖cayleyTransform z‖ < 1 ↔ 0 < z.im := by
  have hpos : 0 < ‖z + I‖ := norm_pos_iff.mpr hz
  have key : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  rw [cayleyTransform, norm_div, div_lt_one hpos]
  constructor
  · intro h
    nlinarith [norm_nonneg (z - I)]
  · intro h
    nlinarith [norm_nonneg (z - I)]

/-- The Cayley transform maps the upper half-plane into the open unit disc. -/
theorem norm_cayleyTransform_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayleyTransform z‖ < 1 :=
  (norm_cayleyTransform_lt_one_iff (add_I_ne_zero_of_im_pos hz)).mpr hz

/-- The value `1 - cayleyTransform z` in closed form. -/
lemma one_sub_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    1 - cayleyTransform z = 2 * I / (z + I) := by
  rw [cayleyTransform]
  field_simp
  ring

/-- The value `cayleyTransformInv w + I` in closed form. -/
lemma cayleyTransformInv_add_I {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    cayleyTransformInv w + I = 2 * I / (1 - w) := by
  rw [cayleyTransformInv]
  field_simp
  ring

/-- `1 - cayleyTransform z` is nonzero: on the upper half-plane the Cayley transform never takes
the value `1`. -/
lemma one_sub_cayleyTransform_ne_zero {z : ℂ} (hz : z + I ≠ 0) :
    (1 : ℂ) - cayleyTransform z ≠ 0 := by
  rw [one_sub_cayleyTransform hz]
  exact div_ne_zero (by simp) hz

/-- `cayleyTransformInv w + I` is nonzero: on the unit disc the inverse Cayley transform never
takes the value `-I`. -/
lemma cayleyTransformInv_add_I_ne_zero {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    cayleyTransformInv w + I ≠ 0 := by
  rw [cayleyTransformInv_add_I hw]
  exact div_ne_zero (by simp) hw

/-- The inverse Cayley transform undoes the Cayley transform. -/
theorem cayleyTransformInv_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    cayleyTransformInv (cayleyTransform z) = z := by
  rw [cayleyTransformInv, div_eq_iff (one_sub_cayleyTransform_ne_zero hz), cayleyTransform]
  field_simp
  ring

/-- The Cayley transform undoes the inverse Cayley transform. -/
theorem cayleyTransform_cayleyTransformInv {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    cayleyTransform (cayleyTransformInv w) = w := by
  rw [cayleyTransform, div_eq_iff (cayleyTransformInv_add_I_ne_zero hw), cayleyTransformInv]
  field_simp
  ring

/-- The inverse Cayley transform maps the open unit disc into the upper half-plane. -/
theorem im_cayleyTransformInv_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyTransformInv w).im := by
  have h1 : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  refine (norm_cayleyTransform_lt_one_iff (cayleyTransformInv_add_I_ne_zero h1)).mp ?_
  rw [cayleyTransform_cayleyTransformInv h1]
  exact hw

/-! ### The Cayley transform is a conformal isomorphism -/

/-- The derivative of the Cayley transform is `2 * I / (z + I) ^ 2`; in particular it never
vanishes. -/
theorem hasDerivAt_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    HasDerivAt cayleyTransform (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I) hz
  refine h.congr_deriv ?_
  congr 1
  ring

/-- The derivative of the inverse Cayley transform is `2 * I / (1 - w) ^ 2`. -/
theorem hasDerivAt_cayleyTransformInv {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    HasDerivAt cayleyTransformInv (2 * I / (1 - w) ^ 2) w := by
  have hnum : HasDerivAt (fun x : ℂ => I * (1 + x)) I w := by
    simpa using ((hasDerivAt_id w).const_add 1).const_mul I
  have hden : HasDerivAt (fun x : ℂ => 1 - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h := hnum.div hden hw
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The derivative of the Cayley transform, in `deriv` form. -/
theorem deriv_cayleyTransform {z : ℂ} (hz : z + I ≠ 0) :
    deriv cayleyTransform z = 2 * I / (z + I) ^ 2 :=
  (hasDerivAt_cayleyTransform hz).deriv

/-- The derivative of the inverse Cayley transform, in `deriv` form. -/
theorem deriv_cayleyTransformInv {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    deriv cayleyTransformInv w = 2 * I / (1 - w) ^ 2 :=
  (hasDerivAt_cayleyTransformInv hw).deriv

/-- The Cayley transform is conformal at every point of the upper half-plane, in Mathlib's sense
of `ConformalAt`. -/
theorem conformalAt_cayleyTransform {z : ℂ} (hz : 0 < z.im) : ConformalAt cayleyTransform z := by
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_pos hz
  refine (hasDerivAt_cayleyTransform hzI).differentiableAt.conformalAt ?_
  rw [deriv_cayleyTransform hzI]
  exact div_ne_zero (by simp) (pow_ne_zero 2 hzI)

/-- The inverse Cayley transform is conformal at every point of the open unit disc. -/
theorem conformalAt_cayleyTransformInv {w : ℂ} (hw : ‖w‖ < 1) :
    ConformalAt cayleyTransformInv w := by
  have hw1 : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  refine (hasDerivAt_cayleyTransformInv hw1).differentiableAt.conformalAt ?_
  rw [deriv_cayleyTransformInv hw1]
  exact div_ne_zero (by simp) (pow_ne_zero 2 hw1)

/-- The Cayley transform is holomorphic on the upper half-plane. -/
theorem differentiableOn_cayleyTransform :
    DifferentiableOn ℂ cayleyTransform UpperHalfPlane.upperHalfPlaneSet := fun _ hz =>
  (hasDerivAt_cayleyTransform (add_I_ne_zero_of_im_pos hz)).differentiableAt.differentiableWithinAt

/-- The inverse Cayley transform is holomorphic on the open unit disc. -/
theorem differentiableOn_cayleyTransformInv :
    DifferentiableOn ℂ cayleyTransformInv (ball (0 : ℂ) 1) := fun _ hw =>
  (hasDerivAt_cayleyTransformInv
      (one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hw))).differentiableAt
    |>.differentiableWithinAt

/-- The Cayley transform maps the upper half-plane into the open unit disc. -/
theorem mapsTo_cayleyTransform :
    MapsTo cayleyTransform UpperHalfPlane.upperHalfPlaneSet (ball (0 : ℂ) 1) := fun _ hz =>
  mem_ball_zero_iff.mpr (norm_cayleyTransform_lt_one hz)

/-- The inverse Cayley transform maps the open unit disc into the upper half-plane. -/
theorem mapsTo_cayleyTransformInv :
    MapsTo cayleyTransformInv (ball (0 : ℂ) 1) UpperHalfPlane.upperHalfPlaneSet := fun _ hw =>
  im_cayleyTransformInv_pos (mem_ball_zero_iff.mp hw)

/-- The two Cayley transforms are mutually inverse between the upper half-plane and the disc. -/
theorem invOn_cayleyTransformInv_cayleyTransform :
    InvOn cayleyTransformInv cayleyTransform UpperHalfPlane.upperHalfPlaneSet (ball (0 : ℂ) 1) :=
  ⟨fun _ hz => cayleyTransformInv_cayleyTransform (add_I_ne_zero_of_im_pos hz),
    fun _ hw => cayleyTransform_cayleyTransformInv
      (one_sub_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp hw))⟩

/-- **The Cayley transform is a bijection of the upper half-plane onto the open unit disc.** -/
theorem bijOn_cayleyTransform :
    BijOn cayleyTransform UpperHalfPlane.upperHalfPlaneSet (ball (0 : ℂ) 1) :=
  invOn_cayleyTransformInv_cayleyTransform.bijOn mapsTo_cayleyTransform mapsTo_cayleyTransformInv

/-- **The Riemann mapping theorem for the upper half-plane, with an explicit map.**  The upper
half-plane is a nonempty, simply connected, proper open subset of `ℂ`, so the Riemann mapping
theorem applies to it; the Cayley transform is an explicit witness, so no compactness argument
is needed.  The statement is in the shape the conformal-mapping roadmap fixes for the Riemann
mapping theorem's conclusion. -/
theorem exists_differentiableOn_injOn_image_eq_ball_of_im_pos :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet ∧
      InjOn f UpperHalfPlane.upperHalfPlaneSet ∧
      f '' UpperHalfPlane.upperHalfPlaneSet = ball (0 : ℂ) 1 :=
  ⟨cayleyTransform, differentiableOn_cayleyTransform, bijOn_cayleyTransform.injOn,
    bijOn_cayleyTransform.image_eq⟩

/-- The Cayley transform as an equivalence `ℍ ≃ 𝔻`. -/
@[expose] noncomputable def cayleyTransformEquiv : ℍ ≃ Complex.UnitDisc where
  toFun z := Complex.UnitDisc.mk (cayleyTransform z) (norm_cayleyTransform_lt_one z.coe_im_pos)
  invFun w := UpperHalfPlane.mk (cayleyTransformInv w) (im_cayleyTransformInv_pos w.norm_lt_one)
  left_inv z := UpperHalfPlane.coe_injective <|
    cayleyTransformInv_cayleyTransform (add_I_ne_zero_of_im_pos z.coe_im_pos)
  right_inv w := Complex.UnitDisc.coe_injective <|
    cayleyTransform_cayleyTransformInv (one_sub_ne_zero_of_norm_lt_one w.norm_lt_one)

@[simp]
lemma coe_cayleyTransformEquiv (z : ℍ) :
    (cayleyTransformEquiv z : ℂ) = cayleyTransform (z : ℂ) := rfl

@[simp]
lemma coe_cayleyTransformEquiv_symm (w : Complex.UnitDisc) :
    (cayleyTransformEquiv.symm w : ℂ) = cayleyTransformInv (w : ℂ) := rfl

/-- The Cayley transform as a homeomorphism `ℍ ≃ₜ 𝔻`. -/
@[expose] noncomputable def cayleyTransformHomeomorph : ℍ ≃ₜ Complex.UnitDisc where
  toEquiv := cayleyTransformEquiv
  continuous_toFun := by
    rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
    simpa only [Function.comp_def, Equiv.toFun_as_coe, coe_cayleyTransformEquiv] using
      differentiableOn_cayleyTransform.continuousOn.comp_continuous
        UpperHalfPlane.continuous_coe fun z => z.coe_im_pos
  continuous_invFun := by
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    simpa only [Function.comp_def, Equiv.invFun_as_coe, coe_cayleyTransformEquiv_symm] using
      differentiableOn_cayleyTransformInv.continuousOn.comp_continuous
        Complex.UnitDisc.continuous_coe fun w => mem_ball_zero_iff.mpr w.norm_lt_one

@[simp]
lemma cayleyTransformHomeomorph_toEquiv :
    cayleyTransformHomeomorph.toEquiv = cayleyTransformEquiv := rfl

@[simp]
lemma coe_cayleyTransformHomeomorph (z : ℍ) :
    (cayleyTransformHomeomorph z : ℂ) = cayleyTransform (z : ℂ) := rfl

/-! ### The two hyperbolic metrics agree up to the normalising factor `2` -/

/-- **The Cayley transform pulls the pseudo-hyperbolic expression back to the half-plane
cross-ratio** `‖z - w‖ / ‖z - conj w‖`. -/
theorem pseudoHyperbolicExpr_cayleyTransform {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    pseudoHyperbolicExpr (cayleyTransform z) (cayleyTransform w) = ‖z - w‖ / ‖z - conj w‖ := by
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_pos hz
  have hwI : w + I ≠ 0 := add_I_ne_zero_of_im_pos hw
  have hconj : conj (w + I) = conj w - I := by
    rw [map_add, Complex.conj_I, sub_eq_add_neg]
  have hnormconj : ‖conj w - I‖ = ‖w + I‖ := by
    rw [← hconj, Complex.norm_conj]
  have hcwI : conj w - I ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnormconj]; exact norm_ne_zero_iff.mpr hwI)
  have hzw : conj w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have him : (conj w).im = z.im := by rw [h]
    simp only [Complex.conj_im] at him
    linarith
  have hnum : cayleyTransform z - cayleyTransform w
      = 2 * I * (z - w) / ((z + I) * (w + I)) := by
    rw [cayleyTransform, cayleyTransform]
    field_simp
    ring
  have hconjcayley : conj (cayleyTransform w) = (conj w + I) / (conj w - I) := by
    rw [cayleyTransform, map_div₀, map_sub, map_add, Complex.conj_I, sub_neg_eq_add,
      sub_eq_add_neg]
  have hden : 1 - conj (cayleyTransform w) * cayleyTransform z
      = 2 * I * (conj w - z) / ((conj w - I) * (z + I)) := by
    rw [hconjcayley, cayleyTransform]
    field_simp
    ring
  have hquot : (cayleyTransform z - cayleyTransform w) /
      (1 - conj (cayleyTransform w) * cayleyTransform z)
      = ((z - w) * (conj w - I)) / ((w + I) * (conj w - z)) := by
    rw [hnum, hden]
    have h2I : (2 : ℂ) * I ≠ 0 := by simp
    field_simp
  rw [pseudoHyperbolicExpr_def, hquot, norm_div, norm_mul, norm_mul, hnormconj,
    norm_sub_rev (conj w) z, mul_comm ‖w + I‖ ‖z - conj w‖]
  exact mul_div_mul_right _ _ (norm_ne_zero_iff.mpr hwI)

/-- **The Cayley transform is a similarity of ratio `1 / 2` from Mathlib's hyperbolic metric on
the upper half-plane to the Poincaré metric on the unit disc.**  The factor `2` records the two
normalisations: `TauCeti.hyperbolicDist` integrates `|dz| / (1 - |z| ^ 2)` on the disc, while
`UpperHalfPlane` integrates `|dz| / z.im`. -/
theorem hyperbolicDist_cayleyTransform (z w : ℍ) :
    hyperbolicDist (cayleyTransform (z : ℂ)) (cayleyTransform (w : ℂ)) = dist z w / 2 := by
  have htanh : Real.tanh (dist z w / 2) = ‖(z : ℂ) - w‖ / ‖(z : ℂ) - conj (w : ℂ)‖ := by
    rw [UpperHalfPlane.tanh_half_dist, dist_eq_norm, dist_eq_norm]
  rw [hyperbolicDist_def, pseudoHyperbolicExpr_cayleyTransform z.coe_im_pos w.coe_im_pos,
    ← htanh, Real.artanh_tanh]

/-- The hyperbolic distance on Mathlib's upper half-plane is twice the Poincaré distance of the
Cayley images. -/
theorem dist_eq_two_mul_hyperbolicDist_cayleyTransform (z w : ℍ) :
    dist z w = 2 * hyperbolicDist (cayleyTransform (z : ℂ)) (cayleyTransform (w : ℂ)) := by
  rw [hyperbolicDist_cayleyTransform]
  ring

/-- The Cayley transform, read as a map into the Poincaré disc metric space, halves distances. -/
theorem dist_cayleyTransformEquiv_toPoincare (z w : ℍ) :
    dist (Complex.UnitDisc.toPoincare (cayleyTransformEquiv z))
        (Complex.UnitDisc.toPoincare (cayleyTransformEquiv w)) = dist z w / 2 := by
  rw [PoincareDisc.dist_eq, PoincareDisc.toUnitDisc_toPoincare,
    PoincareDisc.toUnitDisc_toPoincare, coe_cayleyTransformEquiv, coe_cayleyTransformEquiv,
    hyperbolicDist_cayleyTransform]

end TauCeti
