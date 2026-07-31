/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.UnitDisc.Basic

/-!
# Standard automorphisms of the complex unit disc

This file adds the rotation factor in the standard disc-automorphism formula
`z ↦ u * (z - a) / (1 - conj a * z)`, with `u` on the unit circle and `a` in the
unit disc.  The previous Moebius file supplies the factor sending `a` to `0`; this file
composes it with Mathlib's `Circle` action on `Complex.UnitDisc`.

This advances the conformal-mapping roadmap's L2 disc-automorphism target.  It reuses
Mathlib's `Circle` action on `Complex.UnitDisc` and Tau Ceti's `unitDiscMoebiusEquiv`.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only adds the small discoverable API around `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open _root_.Complex
open scoped ComplexConjugate

/--
The standard automorphism of the complex unit disc
`z ↦ u * (z - a) / (1 - conj a * z)`.

The center-removing factor is `unitDiscMoebiusEquiv a`; the circle element `u` supplies the
rotation factor in the usual classification formula for disc automorphisms.
-/
noncomputable def unitDiscStandardAutomorphismEquiv (u : Circle) (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ Complex.UnitDisc :=
  (unitDiscMoebiusEquiv a).trans (MulAction.toPerm u : Equiv.Perm Complex.UnitDisc)

/-- The standard automorphism applies by first sending `a` to `0`, then rotating. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a z = u • unitDiscMoebius a z :=
  by simp [unitDiscStandardAutomorphismEquiv]

/-- The scalar formula for the standard disc automorphism. -/
@[norm_cast]
lemma coe_unitDiscStandardAutomorphismEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a z : ℂ) =
      (u : ℂ) *
        (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  simp [unitDiscStandardAutomorphismEquiv]

/-- With zero center, the standard automorphism is just rotation. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_zero (u : Circle) :
    unitDiscStandardAutomorphismEquiv u 0 =
      (MulAction.toPerm u : Equiv.Perm Complex.UnitDisc) := by
  ext z
  simp [unitDiscStandardAutomorphismEquiv]

/-- With unit rotation factor, the standard automorphism is the Moebius equivalence. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv 1 a = unitDiscMoebiusEquiv a := by
  ext z
  simp [unitDiscStandardAutomorphismEquiv]

/-- The standard automorphism sends its center to zero. -/
lemma unitDiscStandardAutomorphismEquiv_self (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a a = 0 := by
  simp

/-- The standard automorphism sends zero to `-u * a`. -/
lemma unitDiscStandardAutomorphismEquiv_apply_zero (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a 0 = u • (-a) := by
  simp [unitDiscStandardAutomorphismEquiv]

/-- The norm of a standard automorphism value is the pseudo-hyperbolic expression. -/
lemma norm_unitDiscStandardAutomorphismEquiv (u : Circle) (a z : Complex.UnitDisc) :
    ‖(unitDiscStandardAutomorphismEquiv u a z : ℂ)‖ = pseudoHyperbolicExpr (z : ℂ) (a : ℂ) := by
  rw [unitDiscStandardAutomorphismEquiv_apply, Complex.UnitDisc.coe_circle_smul, norm_mul,
    Circle.norm_coe, one_mul, norm_unitDiscMoebius]

/-- A standard disc automorphism vanishes exactly at its center. -/
lemma unitDiscStandardAutomorphismEquiv_eq_zero_iff (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a z = 0 ↔ z = a := by
  simp

/-- The scalar formula of a standard automorphism is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscStandardAutomorphismFormula_of_norm_lt_one
    (u : ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_const (c := u)).mul
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- The scalar formula of the standard automorphism is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscStandardAutomorphismFormula (u : Circle) (a : Complex.UnitDisc) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (u : ℂ) *
          ((z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z)))
      (Metric.ball (0 : ℂ) 1) :=
  differentiableOn_unitDiscStandardAutomorphismFormula_of_norm_lt_one (u : ℂ) a.norm_lt_one

/-- The inverse of a standard automorphism as a composition of the inverse rotation and
the inverse Moebius factor. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_symm (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a).symm =
      (MulAction.toPerm u⁻¹ : Equiv.Perm Complex.UnitDisc).trans (unitDiscMoebiusEquiv (-a)) :=
  by
    ext z
    simp [unitDiscStandardAutomorphismEquiv]

end TauCeti
