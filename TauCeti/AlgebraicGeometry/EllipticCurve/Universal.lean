/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# The universal elliptic curve

This file defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and the universal pointed elliptic curve
(`Universal.pointedCurve`) over the field of fractions (`Universal.Field`) of
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩` (where `P` is the Weierstrass
polynomial) with distinguished point `(X,Y)`.

## Main definitions

* `WeierstrassCurve.Universal.curve`: the universal Weierstrass curve, over `ℤ[A₁,⋯,A₆]`.
* `WeierstrassCurve.Universal.Poly`, `.Ring`, `.Field`: the polynomial ring `ℤ[A₁,⋯,A₆,X,Y]`, its
  quotient by the Weierstrass polynomial, and that quotient's field of fractions; `polyToField` is
  the composite `Poly →+* Field`.
* `WeierstrassCurve.Universal.pointedCurve`: the universal curve over `Universal.Field`. It is an
  elliptic curve, and carries the distinguished point `Universal.Affine.point`
  (`Universal.Jacobian.point` in Jacobian coordinates).
* `WeierstrassCurve.specialize`: for a Weierstrass curve `W` over a commutative ring `R`, the
  specialization homomorphism `ℤ[A₁,⋯,A₆] →+* R` substituting `W`'s coefficients.
* `WeierstrassCurve.Universal.polyEval`, `.ringEval`: the homomorphism `Universal.Poly →+* R`
  induced by a point `(x,y)` of the affine plane, and its factorisation `Universal.Ring →+* R`
  through the Weierstrass polynomial when `(x,y)` lies on `W`.

## Main results

* `WeierstrassCurve.Universal.equation_point`: `(X,Y)` satisfies the affine Weierstrass equation
  of `pointedCurve` — the universal curve really is pointed.
* `WeierstrassCurve.map_specialize`: every Weierstrass curve is a specialization of the universal
  one.
* `WeierstrassCurve.Universal.map_ringEval`: pushing the universal curve over
  `Universal.Ring` along `ringEval` returns `W`, so one identity **over `curveRing`** is the same
  identity for every curve and every point on it. Note the restriction: `ringEval` maps out of
  `Universal.Ring`, so it transports identities over `curveRing`, not over `pointedCurve`, which
  lives over `Universal.Field`. An identity stated there needs its denominators cleared into
  `Universal.Ring` first.
* `WeierstrassCurve.Universal.ringHom_ext`: two homomorphisms out of `Universal.Ring` agreeing on
  the coefficient ring and on the two distinguished coordinates are equal — the uniqueness half of
  the universal property, since those generate.
* `WeierstrassCurve.Universal.algebraMap_field_injective`: `ℤ[A₁,⋯,A₆]` embeds in
  `Universal.Field`, which is what makes `pointedCurve` an elliptic curve.

## Implementation notes

The cusp curve `Y² = X³` carries the rational point `(1,1)`, with the nice property that
`ψₙ(1,1) = n`. Specializing along it is therefore the cheap route to nonvanishing of the universal
`ψₙ` for `n ≠ 0`, which shows that `(X,Y)` is a point of infinite order on the universal pointed
elliptic curve. The `CharZero Universal.Ring` instance is the first use of that argument.

## Roadmap

The `[n]`-is-division-polynomials bullet of `TauCetiRoadmap/EllipticCurves/README.md`'s opening
narrative on isogenies asks for multiplication by `n ≠ 0` as an isogeny of degree `n²` whose
pullback is "pinned by the division-polynomial multiplication formula, already proved at the point
level in the Lutz–Nagell provenance through J. Xu's work (mathlib #13782 / `ZSMul.lean`) — the
mathlib-track anchor Layer 1 consumes". This file is the `Universal.Ring` prerequisite of that
`ZSMul.lean`: `ringEval` is what turns a single identity **over `curveRing`** into the same
identity for every Weierstrass curve and every point on it, so the point-level
`[n]`-compatibility is proved once, universally, rather than curve by curve. It maps out of
`Universal.Ring`; identities over `pointedCurve`, which is over `Universal.Field`, transport only
after their denominators are cleared into `Universal.Ring`. Mathlib PR #13782 is
still open, so the whole `Universal` namespace below is absent from Mathlib.

## Provenance

Ported from J. Xu's `LutzNagell/Universal.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache 2.0, `main` at `1c1c7466`, `projects/NagellLutz/LutzNagell/Universal.lean`), the source the
roadmap pins for the Nagell–Lutz strand. **Most** declarations here come from that file: the
`Coeff` index type and the bulk of the `Universal` namespace (`curve`, `Poly`, `Ring`, `Field`,
`polyToField`, `pointedCurve`, `Affine.point`, `Jacobian.point`, `curvePoly` and `curveRing` with
their lemmas), and the specialization API (`specialize`, `polyEval`, `ringEval` with their
compatibility lemmas).

Three groups are **not** simple ports, and are listed among the adaptations below: `ringHom_ext`
is new; the `CharZero Universal.Ring` instance **replaces** the source's `Poly.two_ne_zero` and
`Field.two_ne_zero` rather than porting them, and carries the field case with it — Mathlib derives
`CharZero Universal.Field` from it through `IsFractionRing`, so no second instance is declared; and
the equation lemmas for the opaque definitions
(`polyToField_apply`, `Affine.point_def`, `Jacobian.point_def`, `pointedCurve_Δ`) exist because
this repository's module system leaves definition bodies unexposed.
That file's header reads `Authors: Junyan Xu`; following this repository's convention for adapted
material, the upstream authorship is credited here rather than in the copyright header.

Four adaptations were made. The file was converted to this repository's module system (`module`,
`public import`, `public section`). The source's three opening lemmas —
`CoordinateRing.algebraMap_poly_injective`, `CoordinateRing.algebraMap_injective'` and
`Affine.Point.some_eq_some_iff` — are **not** ported: the first two are
`FaithfulSMul.algebraMap_injective` applied to Mathlib's own `FaithfulSMul` instances on the
coordinate ring, and the third is the `Iff` reading of the auto-generated `some.injEq`, which `simp`
proves alone. This repository declines such wrappers, and had already declined the analogous
instances in `Affine/FunctionField/Finrank.lean`; the one internal use, in
`algebraMap_field_injective`, calls `FaithfulSMul.algebraMap_injective` directly. Dropping them also
removes the source's `set_option backward.isDefEq.respectTransparency false in`, which existed only
for the first of them and which `TauCeti/` forbids in any case.
No definition in this file is exposed. `polyToField_apply`, `algebraMap_field_eq_comp`, the five
`pointedCurve_aᵢ` lemmas and the two `point_def` lemmas are proved `:= (rfl)`: the parentheses
satisfy the module system's export check without publishing any body, which is what an `@[expose]`
would do. The section is a plain `public section` for the reason spelled out in
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/VariableChange.lean` — exposing the whole file
would publish every proof body to make a handful of `rfl`s go through. And `equation_point` opens
with `change` where the source has `show`, that step rewriting the goal rather than only naming it
(`linter.style.show`).
-/

public section

noncomputable section

/-! ## The universal elliptic curve -/

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆` of the
Weierstrass polynomial. It indexes the variables of `MvPolynomial Coeff ℤ = ℤ[A₁,⋯,A₆]`, the ring
the universal curve is defined over. There is no `A₅` — the subscripts are weights, not positions —
and the constructors are uppercase as names of indeterminates: `specialize` sends `A₁` to `W.a₁`. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Universal

open scoped Polynomial Polynomial.Bivariate
open Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve: the curve over `ℤ[A₁,⋯,A₆] = MvPolynomial Coeff ℤ` (the
**universal polynomial ring** for Weierstrass curves) whose five coefficients are the five
indeterminates. Every Weierstrass curve is one of its specializations (`map_specialize`); its base
changes are `curvePoly`, `curveRing` and `pointedCurve`. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

open MvPolynomial (X) in
/-- The `a₁` coefficient of the universal curve is the indeterminate `A₁`, and likewise for `A₂`
through `A₆`. The definition body is unexposed, so these are how a consumer normalises a coefficient
of `curve` inside a polynomial identity. -/
@[simp] lemma curve_a₁ : curve.a₁ = X A₁ := (rfl)
open MvPolynomial (X) in
/-- The `a₂` coefficient of the universal curve is the indeterminate `A₂`. -/
@[simp] lemma curve_a₂ : curve.a₂ = X A₂ := (rfl)
open MvPolynomial (X) in
/-- The `a₃` coefficient of the universal curve is the indeterminate `A₃`. -/
@[simp] lemma curve_a₃ : curve.a₃ = X A₃ := (rfl)
open MvPolynomial (X) in
/-- The `a₄` coefficient of the universal curve is the indeterminate `A₄`. -/
@[simp] lemma curve_a₄ : curve.a₄ = X A₄ := (rfl)
open MvPolynomial (X) in
/-- The `a₆` coefficient of the universal curve is the indeterminate `A₆`. -/
@[simp] lemma curve_a₆ : curve.a₆ = X A₆ := (rfl)

/-- The discriminant of the universal Weierstrass curve is a nonzero polynomial in `ℤ[A₁,⋯,A₆]`,
i.e. a Weierstrass equation is not singular *identically* in its coefficients. Transported along
`algebraMap_field_injective`, this is what makes `pointedCurve` elliptic over `Universal.Field`. -/
lemma curve_Δ_ne_zero : curve.Δ ≠ 0 :=
  -- specialize `A₆ ↦ 1` and the rest to `0`: the curve `Y² = X³ + 1`, whose `Δ` is `-432`
  ne_of_apply_ne (MvPolynomial.eval (Coeff.rec 0 0 0 0 1)) <| by simp [Δ, b₂, b₄, b₆, b₈, curve]

/-- The polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]`: two variables adjoined to the universal polynomial
ring `ℤ[A₁,⋯,A₆]`, in Mathlib's iterated form `R[X][Y]`, so `Y` is the outer variable. The
Weierstrass polynomial `curve.polynomial` lives here; `Universal.Ring` is the quotient by it. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
/-- The universal ring for **pointed** Weierstrass curves: `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`, for `P` the
Weierstrass polynomial. A Weierstrass curve over `R` together with an affine point on it determines
a ring homomorphism out of it — `ringEval` — and determines it uniquely, since the coefficients and
the two coordinates generate (`ringHom_ext`). Being an `abbrev` for `curve.CoordinateRing`, it
inherits Mathlib's `Affine.CoordinateRing` API. -/
protected abbrev Ring : Type := curve.CoordinateRing
/-- The universal field for pointed Weierstrass curves is
the field of fractions of the universal ring. -/
protected abbrev Field : Type := FractionRing Universal.Ring

/-- The ring homomorphism `ℤ[A₁,⋯,A₆,X,Y] → Universal.Field`: reduce modulo the Weierstrass
polynomial, then include the universal ring into its fraction field. Every statement about the
universal pointed curve is ultimately about the images of `X` and `Y` under this map. -/
def polyToField : Poly →+* Universal.Field :=
  (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

/-- `polyToField` is reduction modulo the Weierstrass polynomial followed by the inclusion into
the fraction field. -/
@[simp]
lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := (rfl)

/-- The structure map of `Universal.Field` over the coefficient ring factors through `Poly`: the
coefficients `A₁,⋯,A₆` reach the universal field by the same route as `X` and `Y` do. Rewriting
with this turns a statement about `algebraMap` into one about `polyToField`. -/
lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := (rfl)

/-- The `Universal.Ring` counterpart of `algebraMap_field_eq_comp`: the structure map from the
coefficient ring is the inclusion `ℤ[A₁,⋯,A₆] → Poly` followed by the quotient map. -/
lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  (rfl)

/-- The coefficient ring `ℤ[A₁,⋯,A₆]` embeds in the universal field: the five indeterminates stay
algebraically independent after adjoining a point and passing to fractions. This is what carries
`curve_Δ_ne_zero` over to `pointedCurve`, giving the `IsElliptic` instance below. -/
lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (FaithfulSMul.algebraMap_injective _ _)

/-- The universal **pointed** Weierstrass curve: the universal curve base-changed to the universal
field, over which it is an elliptic curve (instance below) carrying the distinguished point `(X, Y)`
(`equation_point`, packaged as `Affine.point`). It is the base change to `Universal.Field`, and so
is the third of `curvePoly`, `curveRing`, `pointedCurve`. -/
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

/-- The discriminant of `pointedCurve` is the image of `curve.Δ`. `pointedCurve` is by definition
`curve.baseChange Universal.Field`, so this is `map_Δ` at that base change — named here rather than
reached through a definitional `show`, so the ellipticity proof rewrites with an ordinary equation
and the reliance on that definitional unfolding sits in one place. -/
lemma pointedCurve_Δ : pointedCurve.Δ = algebraMap _ Universal.Field curve.Δ :=
  map_Δ curve (algebraMap _ Universal.Field)

/-- The universal pointed Weierstrass curve is an elliptic curve: its discriminant is a unit,
because `Δ` of the universal curve is a nonzero polynomial and the coefficient ring embeds in the
universal field. -/
instance : pointedCurve.IsElliptic where
  isUnit := by
    rw [pointedCurve_Δ]
    exact ((map_ne_zero_iff _ algebraMap_field_injective).mpr curve_Δ_ne_zero).isUnit

open Polynomial in
/-- The pair `(X, Y)` — the images of the two adjoined variables in the universal field — satisfies
the affine Weierstrass equation of `pointedCurve`. This is what makes the universal curve *pointed*;
`Affine.point` packages it as an element of the point group. -/
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  -- Two steps at once, and neither is a rewrite: unfold `Equation` to its defining
  -- `evalEval _ _ polynomial = 0` (Mathlib's `equation_iff'` expands to the coefficient form
  -- instead, which is not what the argument below needs), and present `pointedCurve` as
  -- `curve.map (algebraMap _ _)` so that `Affine.map_polynomial` applies. The two curves are
  -- definitionally equal — `pointedCurve` is `baseChange curve Universal.Field` — so `change`
  -- is the step, not a `rw`.
  change evalEval (polyToField (C X)) (polyToField Y)
    ((curve.map (algebraMap _ Universal.Field)).toAffine.polynomial) = 0
  have h : (evalEvalRingHom (polyToField (C X)) (polyToField Y)).comp
      (mapRingHom <| mapRingHom (algebraMap _ Universal.Field)) = polyToField := by
    ext <;> simp [polyToField, algebraMap_field_eq_comp]
  have : ∀ p, evalEval (polyToField (C X)) (polyToField Y)
      (p.map (mapRingHom (algebraMap _ Universal.Field))) = polyToField p :=
    fun p ↦ congr($h p)
  -- The Weierstrass polynomial vanishes at `(X, Y)`: it is exactly what was quotiented out, so
  -- `AdjoinRoot.mk_self` closes the goal through `polyToField_apply`.
  rw [Affine.map_polynomial, this, polyToField_apply, AdjoinRoot.mk_self, map_zero]

open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def Affine.point : (curve.baseChange Universal.Field).toAffine.Point :=
  .mk equation_point

/-- The affine distinguished point is `equation_point` packaged as a point of the group. The
definition body is not exposed, so this equation lemma is how a consumer recovers it. -/
@[simp]
theorem Affine.point_def : Affine.point = .mk equation_point := (rfl)

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point

/-- The Jacobian distinguished point is the affine one, moved along `fromAffine`. -/
@[simp]
theorem Jacobian.point_def : Jacobian.point = Jacobian.Point.fromAffine Affine.point := (rfl)

open Polynomial (CC)

/-- The `a₁` coefficient of `pointedCurve` is the image of the indeterminate `A₁` in the universal
field, and likewise for `pointedCurve_a₂` through `pointedCurve_a₆`.

None of the five is `@[simp]`: `simp` already rewrites `pointedCurve.a₁` with Mathlib's
`Affine.baseChange_a₁`, to `algebraMap _ _ curve.a₁`, so tagging these would put a non-normal-form
left-hand side in the simp set. They are the `polyToField` reading of the same coefficients, for
use by name. -/
lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := (rfl)
/-- The `a₂` coefficient of `pointedCurve` is the image of the indeterminate `A₂`. -/
lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := (rfl)
/-- The `a₃` coefficient of `pointedCurve` is the image of the indeterminate `A₃`. -/
lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := (rfl)
/-- The `a₄` coefficient of `pointedCurve` is the image of the indeterminate `A₄`. -/
lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := (rfl)
/-- The `a₆` coefficient of `pointedCurve` is the image of the indeterminate `A₆`. -/
lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := (rfl)

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
end Universal

open Universal
variable {R} [CommRing R] (W : WeierstrassCurve R)

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

open MvPolynomial (X) in
/-- `specialize` sends each indeterminate to the corresponding coefficient of `W`. With
`curve_a₁`‥`curve_a₆` this normalises coefficient evaluation inside a polynomial identity, without
unfolding either definition. -/
@[simp]
lemma specialize_X (i : Coeff) :
    W.specialize (X i) = Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ i := by
  simp [specialize]

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
@[simp]
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]

namespace Universal

variable (x y : R)

open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
/-- `polyEval` computes in the expected order: substitute `W`'s coefficients for the indeterminates
`A₁,⋯,A₆`, then evaluate the resulting bivariate polynomial at `(x, y)`. -/
@[simp]
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

/-- `ringEval` is `polyEval` read on the quotient: evaluating a representative `p` gives the same
answer as evaluating `p` in `Poly`. The pointwise form of `ringEval_comp_mk`. -/
@[simp]
lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

/-- The homomorphism-level form of `ringEval_mk`: `ringEval eqn` is the factorisation of
`polyEval W x y` through the quotient by the Weierstrass polynomial. Use this shape when composing
ring maps and `ringEval_mk` when rewriting underneath an application. -/
@[simp]
lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

open Polynomial MvPolynomial in
/-- `ringEval` sends the distinguished `X` to the abscissa of the point. Together with
`ringEval_root` this is the coordinate-level content of the universal property: the pair
`(X, Y)` of `Universal.Ring` goes to the chosen point `(x, y)` of `W`. -/
@[simp]
lemma ringEval_of_X : ringEval eqn (AdjoinRoot.of _ Polynomial.X) = x := by
  rw [← AdjoinRoot.mk_C, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

open Polynomial MvPolynomial in
/-- `ringEval` sends the distinguished `Y` to the ordinate of the point. -/
@[simp]
lemma ringEval_root : ringEval eqn (AdjoinRoot.root _) = y := by
  rw [← AdjoinRoot.mk_X, ringEval_mk, polyEval_apply]
  simp [Polynomial.evalEval]

/-- Restricted to the coefficient ring, `polyEval W x y` is just `W.specialize`: evaluating at a
point does not disturb the substitution of `W`'s coefficients. -/
@[simp]
lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

section RingHomExt

variable {R : Type*} [Semiring R]

/-- **Extensionality for homomorphisms out of the universal ring.** Two ring homomorphisms out of
`Universal.Ring` are equal as soon as they agree on the coefficient ring `ℤ[A₁,⋯,A₆]` and on the two
distinguished coordinates `X` and `Y` — that is, on generators.

Together with `ringEval_comp_eq_specialize`, `ringEval_of_X` and `ringEval_root` this is the
uniqueness half of the universal property: `ringEval` is not merely *a* homomorphism carrying the
universal curve and its point to `W` and `(x, y)`, it is the *only* one. That is what licenses
proving an identity once over `curveRing` and reading it off for every curve and every point.

Agreement after composing with `AdjoinRoot.mk` would **not** do: `mk` is surjective, so that
hypothesis is merely a restatement of the conclusion and proves nothing about generators. -/
@[ext]
lemma ringHom_ext {f g : Universal.Ring →+* R}
    (hcoeff : f.comp (algebraMap (MvPolynomial Coeff ℤ) Universal.Ring)
      = g.comp (algebraMap (MvPolynomial Coeff ℤ) Universal.Ring))
    (hX : f (AdjoinRoot.of _ Polynomial.X) = g (AdjoinRoot.of _ Polynomial.X))
    (hY : f (AdjoinRoot.root _) = g (AdjoinRoot.root _)) : f = g := by
  exact AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext' hcoeff hX) hY

end RingHomExt

/-- The `Universal.Ring` counterpart of `polyEval_comp_eq_specialize`: `ringEval eqn` also restricts
to `W.specialize` on the coefficient ring. This is the compatibility that makes
`map_ringEval`, and with it every specialization argument, go through. -/
@[simp]
lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

/-- The universal ring has characteristic zero: specializing to the cusp curve at `(1, 1)` retracts
it onto `ℤ`. This is the first use of that specialization argument, and it is what gives
`(2 : Universal.Ring) ≠ 0` — needed by the halving steps of the group law and of the
division-polynomial recursion. -/
instance : CharZero Universal.Ring :=
  RingHom.charZero (ringEval (equation_cusp_one_one ℤ))

/-- Specialization is compatible with base change: pushing the universal curve over
`Universal.Ring` along `ringEval eqn` returns `W` itself. This is the mechanism the whole file
exists for — an identity proved once for `curveRing` and its distinguished point becomes the same
identity for every Weierstrass curve `W` and every point `(x, y)` on it. -/
@[simp]
lemma map_ringEval : curveRing.map (ringEval eqn) = W :=
  (map_map curve (algebraMap _ _) (ringEval eqn)).symm ▸
    (ringEval_comp_eq_specialize eqn) ▸ map_specialize W

end Universal

end WeierstrassCurve
