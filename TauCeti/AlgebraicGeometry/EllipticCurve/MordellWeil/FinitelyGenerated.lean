/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Descent
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.WeakMordellWeil
public import TauCeti.NumberTheory.NumberField.IntegralClosure

/-!
# Finite generation of the group of rational points

The descent is complete: the weak Mordell–Weil theorem gives that `E(K)/2E(K)` is finite, the
naïve height satisfies the approximate parallelogram law and the Northcott property, and Mathlib's
descent engine `AddCommGroup.fg_of_descent'` turns those two into finite generation of `E(K)`.

The statements are named for their conclusions, per the roadmap: no declaration is called
`mordellWeil`, and the classical name appears in docstrings only.

## Main results

* `WeierstrassCurve.Affine.finite_torsion` : the torsion subgroup of `E(K)` is finite.
* `WeierstrassCurve.Affine.fg_point` : `E(K)` is finitely generated, for a curve in the normal
  form `y² = f(x)` over the fraction field of a Dedekind domain, under per-factor class-group and
  unit-group finiteness.
* `WeierstrassCurve.Affine.fg_point_of_variableChange` : the same for an arbitrary Weierstrass
  curve, transferred along an admissible change of variables.
* `WeierstrassCurve.Affine.fg_point_of_numberField` : **the Mordell–Weil theorem** — `E(K)` is
  finitely generated for an elliptic curve over a number field.

## Two divergences from the source, both forced by what is already on `main`

*Unit groups are `Monoid.FG`, not `Group.FG`.* The source states `fg_point` with
`Group.FG (ringOfIntegersFactor R p)ˣ`, but `main`'s weak Mordell–Weil theorem
(`finiteIndex_range_nsmulAddMonoidHom_two`) takes `Monoid.FG`. Matching `main` avoids an
impedance mismatch at the one place the hypothesis is used; `Group.fg_iff_monoid_fg` converts,
and `fg_point_of_numberField` does exactly that when discharging it from Dirichlet's theorem.

*The finiteness inputs are `TauCeti`'s.* `NumberField.finite_classGroup_integralClosure` and
`NumberField.fg_units_integralClosure` are in
`TauCeti.NumberTheory.NumberField.IntegralClosure`, since they are general number theory and
mention no curve.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean` (`:350`, `:371`,
  `:390`, `:416`), Apache-2.0. The proofs are that file's.
-/

public section

open Height NumberField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section Northcott

variable [AdmissibleAbsValues F] [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F] [W.toAffine.IsElliptic]

/-- The torsion subgroup of `E(F)` is finite, for any field `F` carrying admissible absolute
values whose `logHeight₁` satisfies the Northcott property. No number field is needed: the
descent uses only the approximate parallelogram law and Northcott finiteness, both of which are
available at that generality. A number field is one such `F`, via
`Mathlib/NumberTheory/Height/NumberField.lean`. -/
theorem finite_torsion : Finite (AddCommGroup.torsion W.Point) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.finite_torsion_of_descent' hC

/-- **The Mordell–Weil theorem**, general version: `E(K)` is finitely generated, for an elliptic
curve `E` given by an equation `y² = f(x)` with a monic cubic `f` (`a₁ = a₃ = 0`) over a field `K`
such that `K` has admissible absolute values with the Northcott property, `K` is the fraction
field of a Dedekind domain `R`, and for each irreducible factor `p` of `f` the integral closure of
`R` in `K[X] ⧸ (p)` has finite class group and finitely generated unit group.

For `K` a number field all of these hold; see `fg_point_of_numberField`.

The per-factor hypotheses cannot be replaced by the corresponding hypotheses on `R` itself: by a
theorem of Claborn, refined by Leedham-Green and by Clark, *every* abelian group is the class
group of the integral closure of a PID in a separable quadratic extension, so
`Finite (ClassGroup R)` gives no control over the class groups of the factors. -/
theorem fg_point (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [W.IsCharNeTwoNF]
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → Monoid.FG (W.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' (W.finiteIndex_range_nsmulAddMonoidHom_two R) H₂ hC

/-- **The Mordell–Weil theorem** for an arbitrary Weierstrass curve: `E(K)` is finitely generated,
given an admissible change of variables `C` bringing `E` into the normal form `y² = f(x)`,
together with the finiteness hypotheses of `fg_point` for the model `C • E`. The result transfers
along the isomorphism of point groups `Point.equivVariableChange`.

Such a `C` exists whenever `2` is invertible in `K`, by completing the square. -/
theorem fg_point_of_variableChange (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (C : VariableChange F) [(C • W).IsCharNeTwoNF]
    [(p : (C • W).toAffine.f.Factors) →
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor R p))]
    [(p : (C • W).toAffine.f.Factors) →
      Monoid.FG ((C • W).toAffine.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have := fg_point (W := (C • W).toAffine) R
  exact AddGroup.fg_of_surjective (f := (Point.equivVariableChange W C).toAddMonoidHom)
    (Point.equivVariableChange W C).surjective

end Northcott

section NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- **The Mordell–Weil theorem**: the group `E(K)` of `K`-rational points of an elliptic curve `E`
over a number field `K` is finitely generated.

The square on the left-hand side is completed by an admissible change of variables, possible since
`K` has characteristic zero, and the finiteness hypotheses of `fg_point` for the resulting model
are the class number theorem and Dirichlet's unit theorem. -/
theorem fg_point_of_numberField : AddGroup.FG W.Point := by
  have := invertibleOfNonzero (two_ne_zero (α := F))
  obtain ⟨C, hC⟩ := exists_variableChange_isCharNeTwoNF (W := W)
  have (p : (C • W).toAffine.f.Factors) :
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)) :=
    NumberField.finite_classGroup_integralClosure F (AdjoinRoot (p : Polynomial F))
  have (p : (C • W).toAffine.f.Factors) :
      Monoid.FG ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)ˣ :=
    Group.fg_iff_monoid_fg.mp
      (NumberField.fg_units_integralClosure F (AdjoinRoot (p : Polynomial F)))
  exact fg_point_of_variableChange (𝓞 F) C

end NumberField

end WeierstrassCurve.Affine

end
