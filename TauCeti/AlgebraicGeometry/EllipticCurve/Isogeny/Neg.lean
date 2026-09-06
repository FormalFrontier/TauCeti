/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint

/-!
# Negation

The involution `(x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve is negation for the group
law. Its pullback on functions is `CoordinateRing.conj`, the conjugation of the coordinate ring
over `F[X]`, so negation is an isogeny of `W` with itself, an involution, and of degree one.

Postcomposing with it negates on the hom carrier, which is the `Neg` structure the carrier's
additive group is built from. That this pullback really is negation, and not just some involution
of degree one, is `tautologicalPoint_negPullback`: its tautological point is the negated generic
point.

## Main definitions

* `TauCeti.Isogeny.negPullback`: the coordinate pullback `x ↦ conj x`.
* `TauCeti.Isogeny.negIsogeny`: the same map packaged as an `Isogeny W W`.
* `TauCeti.Isogeny.Hom.instNeg`: negation on `Hom W₁ W₂`, by postcomposition.

## Main results

* `TauCeti.Isogeny.negIsogeny_comp_negIsogeny`: negation is an involution.
* `TauCeti.Isogeny.degree_negIsogeny`: negation has degree one, so it is an automorphism of `W`
  fixing the point at infinity.
* `TauCeti.Isogeny.Hom.neg_comp` and `TauCeti.Isogeny.Hom.degree_neg`: negation passes through
  composition, and preserves degrees, on the carrier.
* `TauCeti.Isogeny.tautologicalPoint_negPullback`: read at the generic point, negation is the
  group law's inverse — which is what identifies this pullback as negation rather than merely
  some degree-one involution.

The `MapsInfinity` condition says each `x` of the coordinate ring is integral over the pulled-back
copy. Conjugation is an *equivalence*, so every function is the pullback of its own conjugate — the
algebraic form of "negation fixes the point at infinity".

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
-/

-- Design provenance: the negation formula is Silverman III.2; the isogeny packaging follows
-- `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, whose hom-group target names the
-- `AddCommGroup` as its content. Negation is that instance's `Neg`.

public section

open TauCeti.WeierstrassCurve.Affine.CoordinateRing

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

/-- The negation coordinate pullback: an element of the coordinate ring is sent to its
conjugate over `F[X]`, viewed in the function field. -/
noncomputable def negPullback : CoordinatePullback W W :=
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    ((conj W).toAlgHom.restrictScalars F)

/-- The negation pullback is conjugation. -/
@[simp]
theorem negPullback_apply (x : W.CoordinateRing) :
    negPullback W x = algebraMap W.CoordinateRing W.FunctionField (conj W x) :=
  (rfl)

/-- **Negation maps the point at infinity to itself.** -/
theorem mapsInfinity_negPullback : (negPullback W).MapsInfinity :=
  -- Conjugation is an involution, so every function is already a pullback — of its own conjugate.
  -- That is the first-power case of the general criterion.
  CoordinatePullback.mapsInfinity_of_pow (negPullback W) Nat.one_pos fun z =>
    ⟨conj W z, by rw [negPullback_apply, conj_conj, pow_one]⟩

/-- **Negation, as an isogeny** `W ⟶ W`. -/
noncomputable def negIsogeny : Isogeny W W where
  pullback := negPullback W
  mapsInfinity := mapsInfinity_negPullback W

/-- The negation isogeny's pullback is conjugation. -/
@[simp]
theorem negIsogeny_pullback : (negIsogeny W).pullback = negPullback W := (rfl)

/-- **Negation is an involution.** -/
@[simp]
theorem negIsogeny_comp_negIsogeny : (negIsogeny W).comp (negIsogeny W) = id W := by
  refine Isogeny.ext (AlgHom.ext fun x => ?_)
  -- Both conjugations act on the numerator, and `conj` squares to the identity.
  simp [comp_pullback, fieldPullback_algebraMap, id_pullback]

/-- **Negation has degree one**, so it is an automorphism of `W` fixing the point at infinity. -/
@[simp]
theorem degree_negIsogeny : (negIsogeny W).degree = 1 :=
  (degree_eq_one_of_comp_eq_id (negIsogeny_comp_negIsogeny W)).1

/-- **Negation's tautological point is the negated generic point.** This is what identifies
`negIsogeny` as negation: read at the generic point of `W`, it is the group law's inverse. -/
@[simp]
theorem tautologicalPoint_negPullback [W.IsElliptic] :
    (negPullback W).tautologicalPoint = -W.genericPoint := by
  have hg : W.genericPoint ≠ 0 := by
    rw [genericPoint_eq_some]; exact Point.some_ne_zero _
  refine Point.eq_of_coords (CoordinatePullback.tautologicalPoint_ne_zero _)
    (neg_ne_zero.mpr hg) ?_ ?_
  · rw [CoordinatePullback.xCoord_tautologicalPoint, Point.xCoord_neg, xCoord_genericPoint,
      negPullback_apply, conj_mk_C, genericX_def, AdjoinRoot.mk_C]
  · rw [CoordinatePullback.yCoord_tautologicalPoint, Point.yCoord_neg hg,
      xCoord_genericPoint, yCoord_genericPoint,
      negPullback_apply, conj_mk_Y, ← evalEval_genericX_genericY,
      ← map_negPolynomial, evalEval_negPolynomial]
    simp only [WeierstrassCurve.baseChange]

namespace Hom

variable {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

/-- **Negation on the hom carrier**, by postcomposition with the negation isogeny. This is the
`Neg` structure of the carrier's additive group; the addition is not built here. -/
noncomputable instance : Neg (Hom W₁ W₂) :=
  ⟨fun f => (ofIsogeny (negIsogeny W₂)).comp f⟩

-- Deliberately not `@[simp]`: unfolding `-f` to a composition would make `-` vanish from every
-- normalised goal, and the lemmas below about `-` could then never fire.
/-- The equation lemma for negation: the definition's body is not exposed across the module
boundary, so this is how downstream modules compute with it. -/
theorem neg_def (f : Hom W₁ W₂) : -f = (ofIsogeny (negIsogeny W₂)).comp f := (rfl)

/-- **The zero map is its own negative.** -/
@[simp]
theorem neg_zero : -(0 : Hom W₁ W₂) = 0 := by
  rw [neg_def, comp_zero]

/-- **Negating a nonzero element** postcomposes the underlying isogeny. -/
@[simp]
theorem neg_ofIsogeny (φ : Isogeny W₁ W₂) :
    -(ofIsogeny φ) = ofIsogeny ((negIsogeny W₂).comp φ) := by
  rw [neg_def, ofIsogeny_comp_ofIsogeny]

/-- **Negation on the carrier is an involution**, because it is on the curve. -/
noncomputable instance : InvolutiveNeg (Hom W₁ W₂) where
  neg_neg f := by
    rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
    · rw [neg_zero, neg_zero]
    · rw [neg_ofIsogeny, neg_ofIsogeny, ← Isogeny.comp_assoc, negIsogeny_comp_negIsogeny,
        Isogeny.id_comp]

/-- **Negation passes through composition on the left.** -/
@[simp]
theorem neg_comp (g : Hom W₂ W₃) (f : Hom W₁ W₂) : (-g).comp f = -(g.comp f) := by
  rw [neg_def, neg_def, comp_assoc]

/-- **Negation preserves degrees**, negation itself having degree one. -/
@[simp]
theorem degree_neg (f : Hom W₁ W₂) : (-f).degree = f.degree := by
  rw [neg_def, degree_comp, degree_ofIsogeny, degree_negIsogeny, one_mul]

end Hom

end Isogeny

end TauCeti

end
