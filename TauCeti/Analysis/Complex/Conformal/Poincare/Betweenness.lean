/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Geodesic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Module.Ray

/-!
# Betweenness in the Poincaré disc: the hyperbolic geodesic is unique

`Poincare/Geodesic.lean` shows that the Poincaré disc is a **geodesic** metric space: the
Euclidean diameters, reparametrised by `Real.tanh`, are unit-speed geodesic lines, and moving one
of them by a disc automorphism joins any prescribed pair of points. It leaves open the converse —
that these are the *only* geodesics — and it is the converse that this file supplies.

Everything follows from one betweenness criterion, which says that the *hyperbolic* segment issued
from the origin is the *Euclidean* radius:

`hyperbolicDist 0 m + hyperbolicDist m w = hyperbolicDist 0 w ↔ m ∈ segment ℝ 0 w`.

The implication `←` is `TauCeti.hyperbolicDist_zero_add_hyperbolicDist_ofReal_mul`, already proved
in `Poincare/Geodesic.lean`. The implication `→` is the new content, and it comes from the
*equality case* of a triangle inequality. Writing `A = ‖m‖`, `B = ‖w‖` and `ρ` for the
pseudo-hyperbolic expression `TauCeti.pseudoHyperbolicExpr m w`, the addition formula for
`Real.artanh` turns the hypothesis into `(A + ρ) / (1 + A ρ) = B`, hence into
`ρ = |A - B| / (1 - A B)`: the reverse pseudo-hyperbolic triangle inequality against the origin,
`TauCeti.abs_sub_div_one_sub_mul_le_pseudoHyperbolicExpr_of_norm_lt_one`, is *tight*. Its equality
case (proved in `Hyperbolic/Triangle.lean` from the Poincaré defect factorisation) says that this
happens exactly when `(m * conj w).re = ‖m‖ * ‖w‖`, and that — with `A ≤ B`, which the
nonnegativity of `ρ` forces — is exactly the statement that `m` lies on the Euclidean radius
towards `w`. The mirror equality case, for the origin sitting in the *middle* rather than at an
end, is proved the same way and identifies `(z * conj w).re = -(‖z‖ * ‖w‖)` with
`0 ∈ segment ℝ z w`.

Three geometric consequences follow, in increasing strength:

* a point at prescribed distance from `z` on a hyperbolic segment from `z` to `w` is **unique**,
  which is the Menger-convexity statement `Poincare/Geodesic.lean` proved only in its existence
  half;
* two unit-speed geodesics with the same pair of endpoints **agree** on the parameter interval
  between them — the Poincaré disc is *uniquely* geodesic;
* every unit-speed geodesic *line* through the origin **is** a radial one,
  `TauCeti.PoincareDisc.radialGeodesic u` for a unique direction `u : Circle`, which is the
  converse classification `Poincare/Geodesic.lean` explicitly left unproved.

The general case of a geodesic through an arbitrary point needs no separate argument: the disc
automorphisms act transitively by isometries (`TauCeti.PoincareDisc.unitDiscMoebiusIsometryEquiv`),
which is exactly how the betweenness criterion is transported off the origin in
`TauCeti.PoincareDisc.eq_of_dist_add_dist_eq`.

## Main results

* `TauCeti.hyperbolicDist_zero_add_eq_iff_of_norm_lt_one` — the hyperbolic segment from the origin
  is the Euclidean radius.
* `TauCeti.hyperbolicDist_add_zero_eq_iff_of_norm_lt_one` — the origin is hyperbolically between
  two points exactly when it is Euclidean-between them.
* `TauCeti.PoincareDisc.eq_of_dist_add_dist_eq` — a point between `z` and `w` is determined by its
  distance to `z`.
* `TauCeti.PoincareDisc.existsUnique_dist_eq_of_mem_Icc` — the unique-Menger-convexity upgrade of
  `TauCeti.PoincareDisc.exists_dist_eq_of_mem_Icc`.
* `TauCeti.PoincareDisc.eqOn_Icc_of_isometry` — **the Poincaré disc is uniquely geodesic**.
* `TauCeti.PoincareDisc.existsUnique_eq_radialGeodesic` — **every geodesic line through the
  origin is a Euclidean diameter**, for a unique direction.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`), completing the geodesic description that
`Poincare/Geodesic.lean` began. It reuses Tau Ceti's pseudo-hyperbolic, hyperbolic-distance and
disc-automorphism API throughout, and Mathlib's `segment` and `SameRay` for the Euclidean side.
As with the rest of the L0--L3 conformal-mapping material it is coordinated with the upstream
Mathlib Riemann-mapping effort leanprover-community/mathlib4#33505 and the preceding
human-curated work in `Analysis/Complex/RiemannMapping.lean` and
`Analysis/Complex/BranchLogRoot.lean`; none of that
material contains a Poincaré metric on the disc, and Mathlib's hyperbolic geometry on the upper
half-plane (`Analysis/Complex/UpperHalfPlane`) has no geodesics, so nothing here duplicates it.
Should a human-curated Poincaré disc land upstream, this file should be refactored onto it.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set

variable {m w z : ℂ}

/-! ### Euclidean segments through the origin, in terms of `(z * conj w).re` -/

/-- A point of the Euclidean segment from `0` to `w` is a real multiple `t • w` with `t ∈ [0, 1]`,
and conversely. A repackaging of Mathlib's `segment_eq_image_lineMap` at the left endpoint `0`, in
the shape in which the hyperbolic statements below consume it. -/
private lemma mem_segment_zero_left_iff :
    m ∈ segment ℝ 0 w ↔ ∃ t ∈ Icc (0 : ℝ) 1, m = (t : ℂ) * w := by
  rw [segment_eq_image_lineMap]
  simp only [mem_image, AffineMap.lineMap_apply_module, smul_zero, zero_add, Complex.real_smul]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- **Membership in the Euclidean radius, read off the Hermitian product.** A point `m` lies on the
segment from `0` to `w` exactly when `m` and `w` point in the same direction — equality in
`Complex.abs_re_le_norm` for `m * conj w` — and `m` is no further from the origin than `w` is.

Both conditions are needed: `2 * w` points in the direction of `w` without lying on the segment.

"Pointing in the same direction" is Mathlib's `SameRay ℝ`, and `sameRay_iff_norm_add` would give
that reading of the first conjunct — but only in a `StrictConvexSpace ℝ E`, an instance the pinned
Mathlib does not provide for `ℂ`. The two-line normSq computation below is used instead. Both this
lemma and its mirror are kept private: they are statements about complex numbers rather than about
the hyperbolic metric, and only the hyperbolic consequences are exported. -/
private lemma mem_segment_zero_left_iff_re_mul_conj :
    m ∈ segment ℝ 0 w ↔ (m * (starRingEnd ℂ) w).re = ‖m‖ * ‖w‖ ∧ ‖m‖ ≤ ‖w‖ := by
  constructor
  · rw [mem_segment_zero_left_iff]
    rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hnorm : ‖(t : ℂ) * w‖ = t * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hre : ((t : ℂ) * w * (starRingEnd ℂ) w).re = t * ‖w‖ ^ 2 := by
      rw [mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    refine ⟨by rw [hnorm, hre]; ring, ?_⟩
    rw [hnorm]
    nlinarith [norm_nonneg w]
  · rintro ⟨h, hle⟩
    rcases eq_or_ne w 0 with rfl | hw
    · have hm : m = 0 := by
        rw [← norm_eq_zero]
        exact le_antisymm (by simpa using hle) (norm_nonneg m)
      exact hm ▸ left_mem_segment ℝ (0 : ℂ) 0
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      refine mem_segment_zero_left_iff.mpr
        ⟨‖m‖ / ‖w‖, ⟨by positivity, (div_le_one hwpos).mpr hle⟩, ?_⟩
      have hnorm : ‖((‖m‖ / ‖w‖ : ℝ) : ℂ) * w‖ = ‖m‖ / ‖w‖ * ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      -- Conjugation fixes the real scalar, so it can be pulled out in front of `m * conj w`,
      -- which is the shape the hypothesis `h` is about.
      have hpull : m * (starRingEnd ℂ) (((‖m‖ / ‖w‖ : ℝ) : ℂ) * w)
          = ((‖m‖ / ‖w‖ : ℝ) : ℂ) * (m * (starRingEnd ℂ) w) := by
        rw [map_mul, Complex.conj_ofReal]; ring
      have hre : (m * (starRingEnd ℂ) (((‖m‖ / ‖w‖ : ℝ) : ℂ) * w)).re
          = ‖m‖ / ‖w‖ * (‖m‖ * ‖w‖) := by
        rw [hpull, Complex.re_ofReal_mul, h]
      have hzero : ‖m - ((‖m‖ / ‖w‖ : ℝ) : ℂ) * w‖ ^ 2 = 0 := by
        have h3 := Complex.normSq_sub m (((‖m‖ / ‖w‖ : ℝ) : ℂ) * w)
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq] at h3
        rw [h3, hnorm, hre]
        field_simp
        ring
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- **The origin lies between two points exactly when their Hermitian product is negative real.**
This is the mirror of `TauCeti.mem_segment_zero_left_iff_re_mul_conj`, for the origin at the
middle of a Euclidean segment rather than at one of its ends. -/
private lemma zero_mem_segment_iff_re_mul_conj :
    (0 : ℂ) ∈ segment ℝ z w ↔ (z * (starRingEnd ℂ) w).re = -(‖z‖ * ‖w‖) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    rcases eq_or_lt_of_le ha with rfl | hapos
    · have hb1 : b = 1 := by linarith
      rw [hb1, one_smul, zero_smul, zero_add] at h
      simp [h]
    · have h' : (a : ℂ) * z = -((b : ℂ) * w) := by
        rw [eq_neg_iff_add_eq_zero, ← Complex.real_smul, ← Complex.real_smul]
        exact h
      have hnormeq : a * ‖z‖ = b * ‖w‖ := by
        have hn := congrArg norm h'
        rwa [norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hn
      -- Multiplying `h'` by `conj w` makes each side a real scalar times a single complex
      -- number: `z * conj w` on the left, `w * conj w = ‖w‖ ^ 2` on the right.
      have hleft : (a : ℂ) * z * (starRingEnd ℂ) w = (a : ℂ) * (z * (starRingEnd ℂ) w) :=
        mul_assoc _ _ _
      have hright : -((b : ℂ) * w) * (starRingEnd ℂ) w
          = -((b : ℂ) * (w * (starRingEnd ℂ) w)) := by ring
      have hre : a * (z * (starRingEnd ℂ) w).re = -(b * ‖w‖ ^ 2) := by
        have hc := congrArg (fun x : ℂ => (x * (starRingEnd ℂ) w).re) h'
        rwa [hleft, hright, Complex.re_ofReal_mul, Complex.neg_re, Complex.re_ofReal_mul,
          Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hc
      refine mul_left_cancel₀ hapos.ne' ?_
      linear_combination hre + ‖w‖ * hnormeq
  · intro h
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨1, 0, zero_le_one, le_refl 0, by ring, by simp⟩
    rcases eq_or_ne w 0 with rfl | hw
    · exact ⟨0, 1, le_refl 0, zero_le_one, by ring, by simp⟩
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hsum : 0 < ‖z‖ + ‖w‖ := by linarith
    refine ⟨‖w‖ / (‖z‖ + ‖w‖), ‖z‖ / (‖z‖ + ‖w‖), by positivity, by positivity,
      by field_simp; ring, ?_⟩
    -- Conjugation fixes the two real scalars, so the cross term of `normSq_add` is a real
    -- multiple of `z * conj w`, which is the shape the hypothesis `h` is about.
    have hcross : (‖w‖ : ℂ) * z * (starRingEnd ℂ) ((‖z‖ : ℂ) * w)
        = ((‖w‖ * ‖z‖ : ℝ) : ℂ) * (z * (starRingEnd ℂ) w) := by
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
    have hzero : ‖(‖w‖ : ℂ) * z + (‖z‖ : ℂ) * w‖ ^ 2 = 0 := by
      have h3 := Complex.normSq_add ((‖w‖ : ℂ) * z) ((‖z‖ : ℂ) * w)
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq] at h3
      rw [h3, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hwpos.le, abs_of_nonneg hzpos.le, hcross,
        Complex.re_ofReal_mul, h]
      ring
    have hcancel : (‖w‖ : ℂ) * z + (‖z‖ : ℂ) * w = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    have hsumC : ((‖z‖ : ℂ) + (‖w‖ : ℂ)) ≠ 0 := by
      simpa using Complex.ofReal_ne_zero.mpr hsum.ne'
    field_simp
    linear_combination hcancel

/-! ### Hyperbolic betweenness -/

/-- **The hyperbolic segment issued from the origin is the Euclidean radius.** A point `m` of the
disc satisfies `hyperbolicDist 0 m + hyperbolicDist m w = hyperbolicDist 0 w` — it is
hyperbolically between the origin and `w` — exactly when it lies on the Euclidean segment from `0`
to `w`.

The implication `←` is `TauCeti.hyperbolicDist_zero_add_hyperbolicDist_ofReal_mul`. For `→`, the
addition formula `TauCeti.artanh_add` and the injectivity of `Real.artanh` on `Ioo (-1) 1` turn the
hypothesis into `(‖m‖ + ρ) / (1 + ‖m‖ ρ) = ‖w‖`, hence into `ρ (1 - ‖m‖ ‖w‖) = ‖w‖ - ‖m‖`, where
`ρ = pseudoHyperbolicExpr m w`; that is the equality case
`TauCeti.pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff_of_norm_lt_one` of the reverse
pseudo-hyperbolic triangle inequality, and `ρ ≥ 0` supplies `‖m‖ ≤ ‖w‖`. -/
@[simp]
theorem hyperbolicDist_zero_add_eq_iff_of_norm_lt_one (hm : ‖m‖ < 1) (hw : ‖w‖ < 1) :
    hyperbolicDist 0 m + hyperbolicDist m w = hyperbolicDist 0 w ↔ m ∈ segment ℝ 0 w := by
  constructor
  · intro h
    have hden : (0 : ℝ) < 1 - ‖m‖ * ‖w‖ := by nlinarith [norm_nonneg m, norm_nonneg w]
    have hρ0 : 0 ≤ pseudoHyperbolicExpr m w := pseudoHyperbolicExpr_nonneg m w
    have hρ1 : pseudoHyperbolicExpr m w < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hm hw
    have hmIoo : ‖m‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg m], hm⟩
    have hwIoo : ‖w‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg w], hw⟩
    have hρIoo : pseudoHyperbolicExpr m w ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hρ1⟩
    have hquotIoo : (‖m‖ + pseudoHyperbolicExpr m w) / (1 + ‖m‖ * pseudoHyperbolicExpr m w)
        ∈ Ioo (-1 : ℝ) 1 := by
      have hposden : (0 : ℝ) < 1 + ‖m‖ * pseudoHyperbolicExpr m w := by
        nlinarith [norm_nonneg m]
      have hquot0 : (0 : ℝ) ≤ (‖m‖ + pseudoHyperbolicExpr m w)
          / (1 + ‖m‖ * pseudoHyperbolicExpr m w) :=
        div_nonneg (by linarith [norm_nonneg m]) hposden.le
      refine ⟨by linarith, ?_⟩
      rw [div_lt_one hposden]
      nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hρ1)]
    rw [hyperbolicDist_comm 0 m, hyperbolicDist_zero_right, hyperbolicDist_def,
      hyperbolicDist_comm 0 w, hyperbolicDist_zero_right, artanh_add hmIoo hρIoo] at h
    have heq := Real.artanh_injOn hquotIoo hwIoo h
    rw [div_eq_iff (by nlinarith [norm_nonneg m] : (1 : ℝ) + ‖m‖ * pseudoHyperbolicExpr m w ≠ 0)]
      at heq
    have hkey : pseudoHyperbolicExpr m w * (1 - ‖m‖ * ‖w‖) = ‖w‖ - ‖m‖ := by
      linear_combination heq
    have hle : ‖m‖ ≤ ‖w‖ := by nlinarith [mul_nonneg hρ0 hden.le]
    have hρeq : pseudoHyperbolicExpr m w = |‖m‖ - ‖w‖| / (1 - ‖m‖ * ‖w‖) := by
      rw [abs_of_nonpos (by linarith), eq_div_iff hden.ne']
      linarith
    rw [pseudoHyperbolicExpr_eq_abs_sub_div_one_sub_mul_iff_of_norm_lt_one hm hw] at hρeq
    exact mem_segment_zero_left_iff_re_mul_conj.mpr ⟨hρeq, hle⟩
  · intro h
    obtain ⟨t, ht, rfl⟩ := mem_segment_zero_left_iff.mp h
    exact hyperbolicDist_zero_add_hyperbolicDist_ofReal_mul hw ht

/-- **The origin lies hyperbolically between two points exactly when it lies Euclidean-between
them.** The mirror of `TauCeti.hyperbolicDist_zero_add_eq_iff_of_norm_lt_one`, obtained from the
equality case `TauCeti.pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_of_norm_lt_one` of the
*strong* pseudo-hyperbolic triangle inequality in the same way. -/
@[simp]
theorem hyperbolicDist_add_zero_eq_iff_of_norm_lt_one (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hyperbolicDist z 0 + hyperbolicDist 0 w = hyperbolicDist z w ↔ (0 : ℂ) ∈ segment ℝ z w := by
  have hAB : (0 : ℝ) < 1 + ‖z‖ * ‖w‖ := by positivity
  have hρ0 : 0 ≤ pseudoHyperbolicExpr z w := pseudoHyperbolicExpr_nonneg z w
  have hρ1 : pseudoHyperbolicExpr z w < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz hw
  have hzIoo : ‖z‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg z], hz⟩
  have hwIoo : ‖w‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg w], hw⟩
  have hρIoo : pseudoHyperbolicExpr z w ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hρ1⟩
  have hquotIoo : (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖) ∈ Ioo (-1 : ℝ) 1 := by
    have hquot0 : (0 : ℝ) ≤ (‖z‖ + ‖w‖) / (1 + ‖z‖ * ‖w‖) := by positivity
    refine ⟨by linarith, ?_⟩
    rw [div_lt_one hAB]
    nlinarith [mul_pos (sub_pos.mpr hz) (sub_pos.mpr hw)]
  rw [hyperbolicDist_zero_right, hyperbolicDist_comm 0 w, hyperbolicDist_zero_right,
    hyperbolicDist_def, artanh_add hzIoo hwIoo, Real.artanh_injOn.eq_iff hquotIoo hρIoo,
    zero_mem_segment_iff_re_mul_conj,
    ← pseudoHyperbolicExpr_eq_add_div_one_add_mul_iff_of_norm_lt_one hz hw]
  exact eq_comm

/-- Two points of a Euclidean segment issued from the origin at the same distance from the origin
coincide: they are nonnegative multiples of the same vector, hence `SameRay ℝ`, and
`SameRay.eq_of_norm_eq` separates such points by their norm. -/
private lemma eq_of_mem_segment_zero_of_norm_eq {m₁ m₂ : ℂ} (h₁ : m₁ ∈ segment ℝ 0 w)
    (h₂ : m₂ ∈ segment ℝ 0 w) (h : ‖m₁‖ = ‖m₂‖) : m₁ = m₂ := by
  obtain ⟨t₁, ⟨ht₁0, -⟩, rfl⟩ := mem_segment_zero_left_iff.mp h₁
  obtain ⟨t₂, ⟨ht₂0, -⟩, rfl⟩ := mem_segment_zero_left_iff.mp h₂
  refine SameRay.eq_of_norm_eq ?_ h
  rw [← Complex.real_smul, ← Complex.real_smul]
  exact (SameRay.rfl.nonneg_smul_left ht₁0).nonneg_smul_right ht₂0

namespace PoincareDisc

/-! ### Uniqueness of geodesics -/

/-- **A point between `z` and `w` is determined by its distance to `z`.** The Poincaré disc has no
two distinct hyperbolic segments joining a given pair of points.

The Moebius isometry `TauCeti.PoincareDisc.unitDiscMoebiusIsometryEquiv` carries `z` to the origin,
where `TauCeti.hyperbolicDist_zero_add_eq_iff_of_norm_lt_one` places both candidates on the
Euclidean radius towards the image of `w`; on that radius the distance to the origin is a strictly
monotone function of the Euclidean norm, so it separates points. -/
theorem eq_of_dist_add_dist_eq {z w m₁ m₂ : PoincareDisc}
    (h₁ : dist z m₁ + dist m₁ w = dist z w) (h₂ : dist z m₂ + dist m₂ w = dist z w)
    (h : dist z m₁ = dist z m₂) : m₁ = m₂ := by
  set g := unitDiscMoebiusIsometryEquiv (toUnitDisc z) with hg
  have hgz : (toUnitDisc (g z) : ℂ) = 0 := by simp [hg]
  have hd : ∀ p q : PoincareDisc,
      dist p q = hyperbolicDist (toUnitDisc (g p) : ℂ) (toUnitDisc (g q) : ℂ) := fun p q => by
    rw [← g.dist_eq p q, dist_eq]
  have hmem : ∀ p : PoincareDisc, ‖(toUnitDisc (g p) : ℂ)‖ < 1 :=
    fun p => (toUnitDisc (g p)).norm_lt_one
  simp only [hd, hgz] at h₁ h₂ h
  have hs₁ := (hyperbolicDist_zero_add_eq_iff_of_norm_lt_one (hmem m₁) (hmem w)).mp h₁
  have hs₂ := (hyperbolicDist_zero_add_eq_iff_of_norm_lt_one (hmem m₂) (hmem w)).mp h₂
  rw [hyperbolicDist_comm 0, hyperbolicDist_zero_right, hyperbolicDist_comm 0,
    hyperbolicDist_zero_right] at h
  have hnorm := Real.artanh_injOn ⟨by linarith [norm_nonneg (toUnitDisc (g m₁) : ℂ)], hmem m₁⟩
    ⟨by linarith [norm_nonneg (toUnitDisc (g m₂) : ℂ)], hmem m₂⟩ h
  exact g.injective (toUnitDisc.injective
    (Complex.UnitDisc.coe_injective (eq_of_mem_segment_zero_of_norm_eq hs₁ hs₂ hnorm)))

/-- **Menger convexity, with uniqueness.** For `0 ≤ r ≤ dist z w` there is exactly one point at
distance `r` from `z` and `dist z w - r` from `w`. The existence half is
`TauCeti.PoincareDisc.exists_dist_eq_of_mem_Icc`. -/
theorem existsUnique_dist_eq_of_mem_Icc (z w : PoincareDisc) {r : ℝ} (hr : r ∈ Icc 0 (dist z w)) :
    ∃! p : PoincareDisc, dist z p = r ∧ dist p w = dist z w - r := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_dist_eq_of_mem_Icc z w hr
  refine ⟨p, ⟨hp₁, hp₂⟩, fun q hq => ?_⟩
  refine eq_of_dist_add_dist_eq (z := z) (w := w) (m₁ := q) (m₂ := p) ?_ ?_ ?_
  · rw [hq.1, hq.2]; ring
  · rw [hp₁, hp₂]; ring
  · rw [hq.1, hp₁]

/-- **The Poincaré disc is uniquely geodesic.** Two unit-speed geodesics that start at `z` at time
`0` and reach `w` at time `dist z w` agree at every intermediate time. Together with
`TauCeti.PoincareDisc.exists_isometry_apply_zero_apply_dist`, which produces one such geodesic,
this says that hyperbolic segments exist and are unique. -/
theorem eqOn_Icc_of_isometry {γ₁ γ₂ : ℝ → PoincareDisc} {z w : PoincareDisc}
    (h₁ : Isometry γ₁) (h₂ : Isometry γ₂) (hz₁ : γ₁ 0 = z) (hz₂ : γ₂ 0 = z)
    (hw₁ : γ₁ (dist z w) = w) (hw₂ : γ₂ (dist z w) = w) :
    EqOn γ₁ γ₂ (Icc 0 (dist z w)) := by
  intro t ht
  have key : ∀ γ : ℝ → PoincareDisc, Isometry γ → γ 0 = z → γ (dist z w) = w →
      dist z (γ t) = t ∧ dist (γ t) w = dist z w - t := by
    intro γ hγ h0 hend
    have hstart : dist z (γ t) = dist (0 : ℝ) t := by
      conv_lhs => rw [← h0]
      exact hγ.dist_eq 0 t
    have hfinish : dist (γ t) w = dist t (dist z w) := by
      conv_lhs => rw [← hend]
      exact hγ.dist_eq t (dist z w)
    refine ⟨?_, ?_⟩
    · rw [hstart, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht.1]
    · rw [hfinish, Real.dist_eq, abs_of_nonpos (by linarith [ht.2]), neg_sub]
  obtain ⟨ha₁, hb₁⟩ := key γ₁ h₁ hz₁ hw₁
  obtain ⟨ha₂, hb₂⟩ := key γ₂ h₂ hz₂ hw₂
  refine eq_of_dist_add_dist_eq (z := z) (w := w) (m₁ := γ₁ t) (m₂ := γ₂ t) ?_ ?_ ?_
  · rw [ha₁, hb₁]; ring
  · rw [ha₂, hb₂]; ring
  · rw [ha₁, ha₂]

/-- **Every geodesic line through the origin is a Euclidean diameter.** This is the converse to
`TauCeti.PoincareDisc.isometry_radialGeodesic`, and it completes the description of the geodesics
of the Poincaré disc: an isometric embedding of the real line sending `0` to the origin *is* one of
the radial geodesics `TauCeti.PoincareDisc.radialGeodesic u`.

On the nonnegative half-line the hypothesis places `γ t` and `γ 1` on a common Euclidean radius —
whichever of the two is nearer the origin lies on the segment towards the other — so `γ t` is a
nonnegative multiple of `γ 1`, and its norm is pinned to `Real.tanh t` by its distance to the
origin. On the negative half-line the origin is *between* `γ t` and `γ (-t)`, which by
`TauCeti.hyperbolicDist_add_zero_eq_iff_of_norm_lt_one` puts the two on opposite radii, at equal
distance from the origin; so `γ t = -γ (-t)`, and `Real.tanh` is odd.

The direction is unique: evaluating `radialGeodesic u = radialGeodesic v` at time `1` gives
`u * Real.tanh 1 = v * Real.tanh 1`, and `Real.tanh 1 ≠ 0` because `Real.tanh` is injective. In
particular `u ↦ radialGeodesic u` is injective, so distinct directions give distinct lines. -/
theorem existsUnique_eq_radialGeodesic {γ : ℝ → PoincareDisc} (hγ : Isometry γ)
    (h0 : γ 0 = Complex.UnitDisc.toPoincare 0) : ∃! u : Circle, γ = radialGeodesic u := by
  have hmem : ∀ p : PoincareDisc, ‖(toUnitDisc p : ℂ)‖ < 1 := fun p => (toUnitDisc p).norm_lt_one
  have hdist0 : ∀ t : ℝ, hyperbolicDist 0 (toUnitDisc (γ t) : ℂ) = |t| := by
    intro t
    have hi := hγ.dist_eq 0 t
    rwa [dist_eq, h0, toUnitDisc_toPoincare, Complex.UnitDisc.coe_zero, Real.dist_eq, zero_sub,
      abs_neg] at hi
  have hdistst : ∀ s t : ℝ,
      hyperbolicDist (toUnitDisc (γ s) : ℂ) (toUnitDisc (γ t) : ℂ) = |s - t| := by
    intro s t
    have hi := hγ.dist_eq s t
    rwa [dist_eq, Real.dist_eq] at hi
  have hnorm : ∀ t : ℝ, ‖(toUnitDisc (γ t) : ℂ)‖ = Real.tanh |t| := by
    intro t
    have hi := hdist0 t
    rw [hyperbolicDist_comm, hyperbolicDist_zero_right] at hi
    rw [← hi]
    exact (Real.tanh_artanh ⟨by linarith [norm_nonneg (toUnitDisc (γ t) : ℂ)], hmem (γ t)⟩).symm
  have hne : ∀ s : ℝ, s ≠ 0 → (toUnitDisc (γ s) : ℂ) ≠ 0 := by
    intro s hs hzero
    have hi := hdist0 s
    rw [hzero, hyperbolicDist_self, eq_comm, abs_eq_zero] at hi
    exact hs hi
  -- Points of the nonnegative half-line lie on a common Euclidean radius.
  have hbetween : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (toUnitDisc (γ s) : ℂ) ∈ segment ℝ 0 (toUnitDisc (γ t) : ℂ) := by
    intro s t hs hst
    refine (hyperbolicDist_zero_add_eq_iff_of_norm_lt_one (hmem _) (hmem _)).mp ?_
    rw [hdist0, hdistst, hdist0, abs_of_nonneg hs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t),
      abs_of_nonpos (by linarith : s - t ≤ 0)]
    ring
  have hray : ∀ t : ℝ, 0 ≤ t → ∃ κ : ℝ, 0 ≤ κ ∧
      (toUnitDisc (γ t) : ℂ) = (κ : ℂ) * (toUnitDisc (γ 1) : ℂ) := by
    intro t ht
    rcases le_total t 1 with hle | hle
    · obtain ⟨κ, hκ, heq⟩ := mem_segment_zero_left_iff.mp (hbetween t 1 ht hle)
      exact ⟨κ, hκ.1, heq⟩
    · obtain ⟨θ, hθ, heq⟩ := mem_segment_zero_left_iff.mp (hbetween 1 t zero_le_one hle)
      have hθ0 : θ ≠ 0 := by
        rintro rfl
        rw [Complex.ofReal_zero, zero_mul] at heq
        exact hne 1 one_ne_zero heq
      refine ⟨θ⁻¹, inv_nonneg.mpr hθ.1, ?_⟩
      rw [heq, Complex.ofReal_inv, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hθ0)]
  -- The direction of the ray.
  have hcne : (toUnitDisc (γ 1) : ℂ) ≠ 0 := hne 1 one_ne_zero
  have hpos1 : 0 < ‖(toUnitDisc (γ 1) : ℂ)‖ := norm_pos_iff.mpr hcne
  obtain ⟨u, hu⟩ : ∃ u : Circle,
      (u : ℂ) = (toUnitDisc (γ 1) : ℂ) / ((‖(toUnitDisc (γ 1) : ℂ)‖ : ℝ) : ℂ) :=
    ⟨⟨_, mem_sphere_zero_iff_norm.2 (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos1,
        div_self hpos1.ne'])⟩, rfl⟩
  have hX1 : ((‖(toUnitDisc (γ 1) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos1.ne'
  have hnonneg : ∀ t : ℝ, 0 ≤ t →
      (toUnitDisc (γ t) : ℂ) = (u : ℂ) * ((Real.tanh t : ℝ) : ℂ) := by
    intro t ht
    obtain ⟨κ, hκ, heq⟩ := hray t ht
    have hn : ‖(toUnitDisc (γ t) : ℂ)‖ = κ * ‖(toUnitDisc (γ 1) : ℂ)‖ := by
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
    have hκval : (κ : ℂ) = ((Real.tanh t : ℝ) : ℂ) / ((‖(toUnitDisc (γ 1) : ℂ)‖ : ℝ) : ℂ) := by
      rw [eq_div_iff hX1, ← Complex.ofReal_mul, ← hn, hnorm t, abs_of_nonneg ht]
    rw [heq, hu, hκval]
    field_simp
  -- Opposite times sit on opposite radii.
  have hopp : ∀ s : ℝ, 0 < s → (toUnitDisc (γ (-s)) : ℂ) = -(toUnitDisc (γ s) : ℂ) := by
    intro s hs
    obtain ⟨a, b, ha, hb, hab, heq⟩ :
        (0 : ℂ) ∈ segment ℝ (toUnitDisc (γ (-s)) : ℂ) (toUnitDisc (γ s) : ℂ) := by
      refine (hyperbolicDist_add_zero_eq_iff_of_norm_lt_one (hmem _) (hmem _)).mp ?_
      rw [hyperbolicDist_comm _ 0, hdist0, hdist0, hdistst, abs_of_nonpos (by linarith),
        abs_of_nonneg hs.le, abs_of_nonpos (by linarith : -s - s ≤ 0)]
      ring
    have hnormeq : ‖(toUnitDisc (γ (-s)) : ℂ)‖ = ‖(toUnitDisc (γ s) : ℂ)‖ := by
      rw [hnorm, hnorm, abs_neg]
    have hnz : ‖(toUnitDisc (γ s) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (hne s hs.ne')
    have hsplit : a • (toUnitDisc (γ (-s)) : ℂ) = -(b • (toUnitDisc (γ s) : ℂ)) := by
      rw [eq_neg_iff_add_eq_zero]; exact heq
    have hab' : a = b := by
      have hn := congrArg norm hsplit
      rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb, hnormeq] at hn
      exact mul_right_cancel₀ hnz hn
    have ha2 : a = 1 / 2 := by linarith
    have hb2 : b = 1 / 2 := by linarith
    rw [ha2, hb2, Complex.real_smul, Complex.real_smul] at heq
    push_cast at heq
    linear_combination 2 * heq
  have heq : γ = radialGeodesic u := by
    refine funext fun t => toUnitDisc.injective (Complex.UnitDisc.coe_injective ?_)
    rw [coe_radialGeodesic]
    rcases le_total 0 t with ht | ht
    · exact hnonneg t ht
    · rcases eq_or_lt_of_le ht with rfl | hlt
      · exact hnonneg 0 le_rfl
      · have hopp' := hopp (-t) (by linarith)
        rw [neg_neg] at hopp'
        rw [hopp', hnonneg (-t) (by linarith), Real.tanh_neg]
        push_cast
        ring
  -- The direction is pinned by the value at time `1`, where `Real.tanh` does not vanish.
  refine ⟨u, heq, fun v hv => ?_⟩
  have htanh : (Real.tanh 1 : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr fun hzero => one_ne_zero (α := ℝ) ?_
    exact Real.tanh_injective (hzero.trans Real.tanh_zero.symm)
  have hval : (v : ℂ) * (Real.tanh 1 : ℝ) = (u : ℂ) * (Real.tanh 1 : ℝ) := by
    have hcoe := congrArg (fun p : PoincareDisc => (toUnitDisc p : ℂ))
      (congrFun (hv.symm.trans heq) 1)
    simpa only [coe_radialGeodesic] using hcoe
  exact Circle.ext (mul_right_cancel₀ htanh hval)

end PoincareDisc

end TauCeti
