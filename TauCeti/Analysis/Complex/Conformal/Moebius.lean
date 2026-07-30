/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
public import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic

/-!
# Unit-disc Moebius factors

This file packages the standard Moebius factor
`z ↦ (z - a) / (1 - conj a * z)` as a bundled self-map of the complex unit disc.  It is
the elementary automorphism API used by the Schwarz--Pick and disc-automorphism layer of
the conformal-mapping roadmap: the map sends `a` to `0`, its norm is the
pseudo-hyperbolic expression from `z` to `a`, and the inverse is the factor with center
`-a`.  The same map is also bundled as an equivalence and as a homeomorphism of the
unit disc.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only adds the small discoverable API around `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The standard Moebius factor of the unit disc sending `a` to `0`. -/
noncomputable def unitDiscMoebius (a z : Complex.UnitDisc) : Complex.UnitDisc :=
  Complex.UnitDisc.mk
    (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)))
    (by
      have h := pseudoHyperbolicExpr_lt_one_unitDisc z a
      rw [pseudoHyperbolicExpr_def] at h
      simpa using h)

/-- The defining formula for the unit-disc Moebius factor. -/
@[simp, norm_cast]
lemma coe_unitDiscMoebius (a z : Complex.UnitDisc) :
    (unitDiscMoebius a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) :=
  by simp [unitDiscMoebius]

/-- The unit-disc Moebius factor centered at zero is the identity. -/
@[simp]
lemma unitDiscMoebius_zero (z : Complex.UnitDisc) :
    unitDiscMoebius 0 z = z := by
  ext
  simp

/-- The unit-disc Moebius factor sends its center to zero. -/
@[simp]
lemma unitDiscMoebius_self (a : Complex.UnitDisc) :
    unitDiscMoebius a a = 0 := by
  ext
  simp

/-- The unit-disc Moebius factor sends zero to the negative of its center. -/
@[simp]
lemma unitDiscMoebius_apply_zero (a : Complex.UnitDisc) :
    unitDiscMoebius a 0 = -a := by
  ext
  simp

/-- The norm of the Moebius factor is the pseudo-hyperbolic expression. -/
lemma norm_unitDiscMoebius (a z : Complex.UnitDisc) :
    ‖(unitDiscMoebius a z : ℂ)‖ = pseudoHyperbolicExpr (z : ℂ) (a : ℂ) :=
  (pseudoHyperbolicExpr_def (z : ℂ) (a : ℂ)).symm

/-- A unit-disc Moebius factor vanishes exactly at its center. -/
@[simp]
lemma unitDiscMoebius_eq_zero_iff (a z : Complex.UnitDisc) :
    unitDiscMoebius a z = 0 ↔ z = a := by
  rw [← Complex.UnitDisc.coe_inj, Complex.UnitDisc.coe_zero, norm_eq_zero.symm,
    norm_unitDiscMoebius]
  exact pseudoHyperbolicExpr_eq_zero_iff_unitDisc z a

/-- The scalar unit-disc Moebius formula maps the open unit disc to itself. -/
lemma mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  rw [mem_ball_zero_iff, ← pseudoHyperbolicExpr_def]
  exact
    pseudoHyperbolicExpr_lt_one_of_norm_lt_one
      (by simpa only [mem_ball_zero_iff] using hz) ha

/-- The scalar formula of a unit-disc Moebius factor maps the open unit disc to itself. -/
lemma mapsTo_ball_unitDiscMoebiusFormula (a : Complex.UnitDisc) :
    MapsTo
      (fun z : ℂ => (z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z))
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
  mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one

/-- The scalar Moebius formula with center of norm less than one is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) := by
  intro z hz
  have hden :
      1 - (starRingEnd ℂ) a * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one
      (by simpa [mem_ball_zero_iff] using hz) ha
  have hnum :
      DifferentiableWithinAt ℂ (fun z : ℂ => z - a) (ball (0 : ℂ) 1) z :=
    differentiableWithinAt_id.sub (differentiableWithinAt_const (c := a))
  have hden_diff :
      DifferentiableWithinAt ℂ
        (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) (ball (0 : ℂ) 1) z :=
    (differentiableWithinAt_const (c := (1 : ℂ))).sub
      ((differentiableWithinAt_const (c := (starRingEnd ℂ) a)).mul
        differentiableWithinAt_id)
  exact hnum.div hden_diff hden

/-- The complex derivative of the scalar unit-disc Moebius factor
`z ↦ (z - a) / (1 - conj a * z)` at a point `p` where the denominator is nonzero.  Its value at
`p = 0` (with center `-z`) is `1 - ‖z‖ ^ 2`, and at `p = a` it is `1 / (1 - ‖a‖ ^ 2)`, the two
factors that appear in the infinitesimal Schwarz--Pick estimate. -/
lemma hasDerivAt_unitDiscMoebiusFormula (a p : ℂ)
    (hp : 1 - (starRingEnd ℂ) a * p ≠ 0) :
    HasDerivAt (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * p) ^ 2) p := by
  have hn : HasDerivAt (fun z : ℂ => z - a) 1 p := (hasDerivAt_id p).sub_const a
  have hd : HasDerivAt (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) (-(starRingEnd ℂ) a) p := by
    simpa using ((hasDerivAt_id p).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have hq := hn.div hd hp
  have hval : (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * p) ^ 2
      = (1 * (1 - (starRingEnd ℂ) a * p) - (p - a) * -(starRingEnd ℂ) a)
        / (1 - (starRingEnd ℂ) a * p) ^ 2 := by
    congr 1
    ring
  rw [hval]
  exact hq

/-- The scalar formula of the unit-disc Moebius factor is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscMoebiusFormula (a : Complex.UnitDisc) :
    DifferentiableOn ℂ
      (fun z : ℂ => (z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z))
      (ball (0 : ℂ) 1) :=
  differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one

/-- **Schwarz--Pick conjugation scaffold.** For a holomorphic self-map `f` of the open unit
disc and a disc point `a`, conjugating `f` by the Moebius automorphisms centred at `a` (on the
source) and at `f a` (on the target) yields a holomorphic self-map of the disc that fixes the
origin.  This is the common scaffold of the finite and infinitesimal Schwarz--Pick estimates:
applying Schwarz's lemma at `0` to the conjugate `g` unwinds to the contraction estimate for
`f`. -/
lemma differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ
        ((fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
          fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ)) (ball (0 : ℂ) 1) ∧
      MapsTo
        ((fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
          fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ)) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) ∧
      ((fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
          fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ)) 0 = 0 := by
  have ha_mem : a ∈ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using ha
  have hfa_norm : ‖f a‖ < 1 := by simpa [mem_ball_zero_iff] using hmaps ha_mem
  have hsource_maps :
      MapsTo (fun ξ : ℂ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ))
        (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := -a) (by simpa using ha)
  have htarget_maps :
      MapsTo (fun η : ℂ => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η))
        (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := f a) hfa_norm
  have hsource_diff :
      DifferentiableOn ℂ (fun ξ : ℂ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ))
        (ball (0 : ℂ) 1) :=
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -a) (by simpa using ha)
  have htarget_diff :
      DifferentiableOn ℂ (fun η : ℂ => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η))
        (ball (0 : ℂ) 1) :=
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := f a) hfa_norm
  refine ⟨htarget_diff.comp (hf.comp hsource_diff hsource_maps) (hmaps.comp hsource_maps),
    fun ξ hξ => htarget_maps (hmaps (hsource_maps hξ)), ?_⟩
  simp

private lemma unitDiscMoebius_neg_apply_unitDiscMoebius_apply_scalar {a z : ℂ}
    (hden : 1 - (starRingEnd ℂ) a * z ≠ 0)
    (hnorm : 1 - (starRingEnd ℂ) a * a ≠ 0) :
    (((z - a) / (1 - (starRingEnd ℂ) a * z) + a) /
        (1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)))) = z := by
  have hden₂_eq :
      1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
        (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp [hden]
    ring
  have hden₂ :
      1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) ≠ 0 := by
    rw [hden₂_eq]
    exact div_ne_zero hnorm hden
  have hden_comm : 1 - z * (starRingEnd ℂ) a ≠ 0 := by
    simpa [mul_comm] using hden
  have hnorm_comm : 1 - a * (starRingEnd ℂ) a ≠ 0 := by
    simpa [mul_comm] using hnorm
  rw [hden₂_eq]
  field_simp [hden_comm, hnorm_comm]
  ring_nf

private lemma unitDiscMoebius_neg_apply_unitDiscMoebius_apply (a z : Complex.UnitDisc) :
    unitDiscMoebius (-a) (unitDiscMoebius a z) = z := by
  ext
  have hden₁ :
      1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ) ≠ 0 :=
    one_sub_conj_mul_ne_zero_unitDisc z a
  have hnorm :
      1 - (starRingEnd ℂ) (a : ℂ) * (a : ℂ) ≠ 0 :=
    one_sub_conj_mul_ne_zero_unitDisc a a
  simp only [coe_unitDiscMoebius, Complex.UnitDisc.coe_neg, map_neg]
  simpa [sub_neg_eq_add] using
    unitDiscMoebius_neg_apply_unitDiscMoebius_apply_scalar hden₁ hnorm

/-- The inverse of the unit-disc Moebius factor centered at `a` is the factor centered at `-a`. -/
@[simp]
lemma unitDiscMoebius_neg_comp_unitDiscMoebius (a : Complex.UnitDisc) :
    unitDiscMoebius (-a) ∘ unitDiscMoebius a = id := by
  funext z
  exact unitDiscMoebius_neg_apply_unitDiscMoebius_apply a z

/-- The unit-disc Moebius factors centered at `a` and `-a` compose in the other order too. -/
@[simp]
lemma unitDiscMoebius_comp_unitDiscMoebius_neg (a : Complex.UnitDisc) :
    unitDiscMoebius a ∘ unitDiscMoebius (-a) = id := by
  simpa using unitDiscMoebius_neg_comp_unitDiscMoebius (-a)

/-- The scalar unit-disc Moebius formula centered at `-a` is a left inverse for the scalar
formula centered at `a` on the open unit disc. -/
lemma leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    LeftInvOn
      (fun z : ℂ => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z))
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hz
  have h := congrArg (fun u : Complex.UnitDisc => (u : ℂ))
    (congr_fun (unitDiscMoebius_neg_comp_unitDiscMoebius (Complex.UnitDisc.mk a ha))
      (Complex.UnitDisc.mk z hz_norm))
  simpa [coe_unitDiscMoebius, Complex.UnitDisc.coe_neg, Complex.UnitDisc.coe_mk, map_neg,
    neg_mul, sub_neg_eq_add] using h

/-- The standard Moebius self-equivalence of the unit disc sending `a` to `0`. -/
noncomputable def unitDiscMoebiusEquiv (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ Complex.UnitDisc where
  toFun := unitDiscMoebius a
  invFun := unitDiscMoebius (-a)
  left_inv z := by
    exact congr_fun (unitDiscMoebius_neg_comp_unitDiscMoebius a) z
  right_inv z := by
    exact congr_fun (unitDiscMoebius_comp_unitDiscMoebius_neg a) z

/-- The equivalence applies by the unit-disc Moebius formula. -/
@[simp]
lemma unitDiscMoebiusEquiv_apply (a z : Complex.UnitDisc) :
    unitDiscMoebiusEquiv a z = unitDiscMoebius a z :=
  by simp [unitDiscMoebiusEquiv]

/-- The inverse equivalence is the Moebius equivalence centered at `-a`. -/
@[simp]
lemma unitDiscMoebiusEquiv_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusEquiv a).symm = unitDiscMoebiusEquiv (-a) :=
  Equiv.ext fun _ => rfl

/-- The unit-disc Moebius factor is continuous as a map of the bundled open disc. -/
lemma continuous_unitDiscMoebius (a : Complex.UnitDisc) :
    Continuous (unitDiscMoebius a) := by
  rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
  simpa only [Function.comp_def, coe_unitDiscMoebius] using
    (differentiableOn_unitDiscMoebiusFormula a).continuousOn.comp_continuous
      Complex.UnitDisc.continuous_coe
      (fun z => by simpa [mem_ball_zero_iff] using Complex.UnitDisc.norm_lt_one z)

/-- The standard Moebius self-map of the unit disc, bundled as a homeomorphism. -/
noncomputable def unitDiscMoebiusHomeomorph (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ₜ Complex.UnitDisc where
  toEquiv := unitDiscMoebiusEquiv a
  continuous_toFun := by
    exact (continuous_unitDiscMoebius a).congr fun z => by
      calc
        unitDiscMoebius a z = unitDiscMoebiusEquiv a z :=
          (unitDiscMoebiusEquiv_apply a z).symm
        _ = (unitDiscMoebiusEquiv a).toFun z := rfl
  continuous_invFun := by
    exact (continuous_unitDiscMoebius (-a)).congr fun z => by
      calc
        unitDiscMoebius (-a) z = unitDiscMoebiusEquiv (-a) z :=
          (unitDiscMoebiusEquiv_apply (-a) z).symm
        _ = (unitDiscMoebiusEquiv a).symm z := by
          rw [unitDiscMoebiusEquiv_symm]
        _ = (unitDiscMoebiusEquiv a).invFun z := rfl

/-- The Moebius homeomorphism applies by the existing Moebius factor. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_apply (a z : Complex.UnitDisc) :
    unitDiscMoebiusHomeomorph a z = unitDiscMoebius a z :=
  unitDiscMoebiusEquiv_apply a z

/-- The underlying equivalence of the Moebius homeomorphism is the existing equivalence. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_toEquiv (a : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a).toEquiv = unitDiscMoebiusEquiv a :=
  by
    ext z
    calc
      ((unitDiscMoebiusHomeomorph a).toEquiv z : ℂ)
          = (unitDiscMoebiusHomeomorph a z : ℂ) := rfl
      _ = (unitDiscMoebiusEquiv a z : ℂ) := by
        rw [unitDiscMoebiusHomeomorph_apply, unitDiscMoebiusEquiv_apply]

/-- The inverse Moebius homeomorphism is the Moebius homeomorphism centered at `-a`. -/
@[simp]
lemma unitDiscMoebiusHomeomorph_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a).symm = unitDiscMoebiusHomeomorph (-a) := by
  ext z
  calc
    ((unitDiscMoebiusHomeomorph a).symm z : ℂ)
        = ((unitDiscMoebiusEquiv a).symm z : ℂ) := rfl
    _ = (unitDiscMoebiusHomeomorph (-a) z : ℂ) := by
      rw [unitDiscMoebiusEquiv_symm, unitDiscMoebiusEquiv_apply,
        unitDiscMoebiusHomeomorph_apply]

/-- The scalar formula for the Moebius homeomorphism. -/
@[norm_cast]
lemma coe_unitDiscMoebiusHomeomorph_apply (a z : Complex.UnitDisc) :
    (unitDiscMoebiusHomeomorph a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) :=
  by
    rw [unitDiscMoebiusHomeomorph_apply]
    exact coe_unitDiscMoebius a z

end TauCeti
