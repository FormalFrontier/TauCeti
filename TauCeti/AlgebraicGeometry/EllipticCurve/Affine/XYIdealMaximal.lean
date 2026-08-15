/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Ideals of points of a Weierstrass curve

For a point `(x, y)` on an affine Weierstrass curve `W` over a field, Mathlib's
`CoordinateRing.XYIdeal W x (C y)` is the ideal `⟨X - x, Y - y⟩` of the coordinate ring, and
`CoordinateRing.quotientXYIdealEquiv` identifies the quotient by it with the base field. This file
records the consequences: that ideal is maximal, it is nonzero, and it determines the coordinates
it was built from. Conversely, every ideal whose quotient has rank one over the base field is the
ideal of a point.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot`: `XYIdeal W x y` is nonzero, over
  any nontrivial commutative base.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal`: `XYIdeal W x y` is maximal
  for any `y : F[X]` solving the Weierstrass equation at `x`, matching the generality of
  `XYIdeal` and `quotientXYIdealEquiv` themselves.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation`: the point case,
  `XYIdeal W x (C y)` for `(x, y)` on `W`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff_of_ne_top`: two such ideals are
  equal exactly when `x₁ = x₂` and the two `Y`-polynomials agree at the point,
  `y₁.eval x₁ = y₂.eval x₂`, as soon as the first is proper.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff`: the constant-polynomial point
  case, where the conclusion is equality of the coordinates and properness comes from maximality.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.ringHom_comp_mk_eq_evalEvalRingHom`: a ring
  homomorphism from the coordinate ring to the base field that fixes the base field is evaluation
  at the images of the two coordinate functions, and
  `TauCeti.WeierstrassCurve.Affine.CoordinateRing.equation_of_ringHom`: that pair of images is
  therefore a point of the curve.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.exists_equation_and_eq_XYIdeal`: an ideal whose
  quotient has rank one over the base field is `XYIdeal W x (C y)` for a point `(x, y)` of `W`.

Mathlib has the quotient isomorphism but records nothing about the ideal itself; the many `XYIdeal`
lemmas it does state (`XYIdeal_eq₁`, `XYIdeal_eq₂`, `XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul`) are
all about products and rewriting, not about the ideal's place in the spectrum. It does record that
the two generators are nonzero (`XClass_ne_zero`, `YClass_ne_zero`), which is what `XYIdeal_ne_bot`
rests on.

Only the curve equation is needed, not nonsingularity: the quotient is the base field either way.

This supports `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0, whose point–place dictionary
identifies the affine places of `W` with the maximal ideals of its coordinate ring — "the affine
places are the maximal ideals of the coordinate ring". Maximality of `XYIdeal` is the direction
that sends a point to a place, `XYIdeal_eq_iff` says that map is injective, and
`exists_equation_and_eq_XYIdeal` classifies the ideals with residue degree one.

The roadmap's §"What Mathlib already has (consume)" lists `Affine.CoordinateRing` as consumed
infrastructure that "is load-bearing API here, not an
implementation detail"; this is a complement to that API, not a reimplementation of it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/Basic.lean`, declaration
`maximalIdealAt_isMaximal`. The two `XYIdeal_eq_iff` lemmas are not in the source.

Changes from the source. There the ideal is reached through a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine` and a `SmoothPoint` structure bundling the coordinates with their
nonsingularity proof; the surrounding wrappers are not ported, and the statement is made directly
about Mathlib's `XYIdeal`. The hypothesis is correspondingly weakened from nonsingularity to the
curve equation, which is all the quotient isomorphism consumes.

The classification has a counterpart in the same project, in
`projects/HasseWeil/HasseWeil/Foundation/Curves/Valuation/NormValuation.lean` at
`github.com/CBirkbeck/AINTLIB @ 1c1c74664e40` (Apache-2.0 per that file's header;
Authors: Chris Birkbeck): `exists_coordinates_of_isMaximal_of_surjective`,
`equation_of_coordinates_of_field` and `exists_smoothPoint_of_isMaximal_of_surjective`, packaged
in `Valuation/SmoothPointPrime.lean` as `smoothPointEquivHeightOneSpectrum`. That statement is
about a *maximal* ideal of the coordinate ring of a `SmoothPlaneCurve`, hypothesises surjectivity
of `algebraMap F (F[C] ⧸ M)`, and assumes ellipticity throughout. The classification below is
written directly against Mathlib's `XYIdeal`: its hypothesis is the residue degree and it uses no
ellipticity or Dedekind assumption.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

section CommRing

variable {R : Type*} [CommRing R] [Nontrivial R] {W : _root_.WeierstrassCurve.Affine R}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is nonzero** over a nontrivial base. -/
@[simp]
lemma XYIdeal_ne_bot (x : R) (y : R[X]) : CoordinateRing.XYIdeal W x y ≠ ⊥ := fun hbot => by
  have hmem : CoordinateRing.XClass W x ∈ CoordinateRing.XYIdeal W x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact CoordinateRing.XClass_ne_zero x hmem

end CommRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The ideal `⟨X - x, Y - y(X)⟩` of the coordinate ring is maximal** whenever `y` is a
polynomial solving the Weierstrass equation at `x`. Equivalently, the quotient by it is the base
field. -/
theorem XYIdeal_isMaximal {y : F[X]} (h : (W.polynomial.eval y).eval x = 0) :
    (CoordinateRing.XYIdeal W x y).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((CoordinateRing.quotientXYIdealEquiv h).toRingEquiv.isField (Field.toIsField F))

/-- **The ideal of a point of a Weierstrass curve is maximal**, the constant-polynomial case of
`XYIdeal_isMaximal`. -/
theorem XYIdeal_isMaximal_of_equation {y : F} (h : W.Equation x y) :
    (CoordinateRing.XYIdeal W x (C y)).IsMaximal :=
  XYIdeal_isMaximal h

/-- A proper ideal of the coordinate ring contains the class of no nonzero constant: the class of
a unit is a unit. -/
private theorem eq_zero_of_mk_C_C_mem {I : Ideal W.CoordinateRing} (hI : I ≠ ⊤) {c : F}
    (hc : CoordinateRing.mk W (C (C c)) ∈ I) : c = 0 := by
  by_contra hne
  exact hI (I.eq_top_of_isUnit_mem hc
    ((isUnit_C.mpr (isUnit_C.mpr (IsUnit.mk0 c hne))).map (CoordinateRing.mk W)))

/-- Two `XClass` generators differ by the constant `x₂ - x₁`. -/
private theorem XClass_sub_XClass (x₁ x₂ : F) :
    CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ =
      CoordinateRing.mk W (C (C (x₂ - x₁))) := by
  simp only [CoordinateRing.XClass, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- Two `YClass` generators differ by the image of the polynomial `y₂ - y₁`. -/
private theorem YClass_sub_YClass (y₁ y₂ : F[X]) :
    CoordinateRing.YClass W y₁ - CoordinateRing.YClass W y₂ =
      CoordinateRing.mk W (C (y₂ - y₁)) := by
  simp only [CoordinateRing.YClass, ← map_sub]
  congr 1
  simp only [map_sub]
  ring

/-- Modulo `X - x`, a polynomial in `X` is its value at `x`: the two differ by an explicit multiple
of the `XClass` generator. -/
private theorem mk_C_sub_mk_C_C_eval (x : F) (y : F[X]) :
    ∃ q : F[X], CoordinateRing.mk W (C y) - CoordinateRing.mk W (C (C (y.eval x))) =
      CoordinateRing.XClass W x * CoordinateRing.mk W (C q) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := x) (p := y)
  refine ⟨q, ?_⟩
  rw [CoordinateRing.XClass, ← map_mul, ← map_sub, ← map_sub, ← C_mul, ← hq]

/-- A proper ideal `⟨X - x₁, Y - y₁(X)⟩` sees the value of a polynomial at the point: if the class
of `p` lies in it, then `p` vanishes at `x₁`. -/
private theorem eval_eq_zero_of_mk_C_mem {x₁ : F} {y₁ : F[X]}
    (hI : CoordinateRing.XYIdeal W x₁ y₁ ≠ ⊤) {p : F[X]}
    (hp : CoordinateRing.mk W (C p) ∈ CoordinateRing.XYIdeal W x₁ y₁) : p.eval x₁ = 0 := by
  -- modulo `X - x₁` the class of `p` is the constant `p.eval x₁`, which a proper ideal can only
  -- contain if it is zero
  obtain ⟨q, hq⟩ := mk_C_sub_mk_C_C_eval (W := W) x₁ p
  refine eq_zero_of_mk_C_C_mem hI ?_
  have hX₁ : CoordinateRing.XClass W x₁ ∈ CoordinateRing.XYIdeal W x₁ y₁ :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hmem := Ideal.sub_mem _ hp (hq ▸ Ideal.mul_mem_right (CoordinateRing.mk W (C q)) _ hX₁)
  rwa [sub_sub_cancel] at hmem

/-- **Equal ideals have equal data**: if `⟨X - x₁, Y - y₁(X)⟩` is proper and equals
`⟨X - x₂, Y - y₂(X)⟩`, then `x₁ = x₂` and the two `Y`-polynomials agree at the point. The forward
half of `XYIdeal_eq_iff_of_ne_top`. -/
private theorem eq_and_eval_eq_of_XYIdeal_eq {x₁ x₂ : F} {y₁ y₂ : F[X]}
    (hI : CoordinateRing.XYIdeal W x₁ y₁ ≠ ⊤)
    (h : CoordinateRing.XYIdeal W x₁ y₁ = CoordinateRing.XYIdeal W x₂ y₂) :
    x₁ = x₂ ∧ y₁.eval x₁ = y₂.eval x₂ := by
  -- the two `XClass` generators differ by the constant `x₂ - x₁`, which a proper ideal can only
  -- contain if it is zero; the `YClass` generators then differ by `y₂ - y₁`
  have hmemX : CoordinateRing.XClass W x₁ - CoordinateRing.XClass W x₂ ∈
      CoordinateRing.XYIdeal W x₁ y₁ :=
    Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _))
      (h ▸ Ideal.subset_span (Set.mem_insert _ _))
  rw [XClass_sub_XClass] at hmemX
  have hx : x₁ = x₂ := (sub_eq_zero.mp (eq_zero_of_mk_C_C_mem hI hmemX)).symm
  have hmemY : CoordinateRing.mk W (C (y₂ - y₁)) ∈ CoordinateRing.XYIdeal W x₁ y₁ := by
    rw [← YClass_sub_YClass]
    exact Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      (h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hy := eval_eq_zero_of_mk_C_mem hI hmemY
  rw [eval_sub, sub_eq_zero] at hy
  exact ⟨hx, by rw [← hx, hy]⟩

/-- **Two such ideals are equal exactly when their data agree at the point**, given only that the
first is proper: the `X`-coordinates must coincide, and the two `Y`-polynomials must take the same
value there. Stated for polynomial `y`, matching `XYIdeal` and `XYIdeal_isMaximal`; no curve
equation is needed. Use `XYIdeal_eq_iff` for points, whose properness is automatic. -/
theorem XYIdeal_eq_iff_of_ne_top {x₁ x₂ : F} {y₁ y₂ : F[X]}
    (hI : CoordinateRing.XYIdeal W x₁ y₁ ≠ ⊤) :
    CoordinateRing.XYIdeal W x₁ y₁ = CoordinateRing.XYIdeal W x₂ y₂ ↔
      x₁ = x₂ ∧ y₁.eval x₁ = y₂.eval x₂ := by
  constructor
  · exact eq_and_eval_eq_of_XYIdeal_eq hI
  · rintro ⟨rfl, hy⟩
    -- the two `Y` generators differ by a multiple of `X - x₁`, which is a change of generator
    -- Mathlib already knows leaves the span alone
    obtain ⟨q, hq⟩ := mk_C_sub_mk_C_C_eval (W := W) x₁ (y₂ - y₁)
    rw [eval_sub, sub_eq_zero.mpr hy.symm] at hq
    simp only [map_zero, sub_zero, ← YClass_sub_YClass] at hq
    rw [CoordinateRing.XYIdeal, CoordinateRing.XYIdeal, sub_eq_iff_eq_add.mp hq,
      Ideal.span_pair_left_mul_add]

/-- **The ideal of a point determines the point**: for points of the curve, equality of the ideals
`⟨X - x, Y - y⟩` is equality of the coordinates, so `fun (x, y) ↦ XYIdeal W x (C y)` is injective
on points. The point case of `XYIdeal_eq_iff_of_ne_top`, whose properness comes from
`XYIdeal_isMaximal_of_equation`. -/
@[simp]
theorem XYIdeal_eq_iff {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) :
    CoordinateRing.XYIdeal W x₁ (C y₁) = CoordinateRing.XYIdeal W x₂ (C y₂) ↔
      x₁ = x₂ ∧ y₁ = y₂ := by
  simpa only [eval_C] using XYIdeal_eq_iff_of_ne_top (x₂ := x₂) (y₂ := C y₂)
    (XYIdeal_isMaximal_of_equation h₁).ne_top

/-- A ring homomorphism from the coordinate ring that fixes the base field is evaluation at the
images of the two coordinate functions. -/
theorem ringHom_comp_mk_eq_evalEvalRingHom (f : W.CoordinateRing →+* F)
    (hf : ∀ c : F, f (algebraMap F W.CoordinateRing c) = c) :
    f.comp (CoordinateRing.mk W) =
      evalEvalRingHom (f (CoordinateRing.mk W (C X))) (f (CoordinateRing.mk W Y)) := by
  refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
  · ext c
    have hCC : CoordinateRing.mk W (C (C c)) = algebraMap F W.CoordinateRing c := by
      rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq]
      simp
    simp only [RingHom.comp_apply, hCC, hf, coe_evalRingHom, eval_C]
  · simp
  · simp

/-- The images of the coordinate functions under a base-field-preserving ring homomorphism from
the coordinate ring satisfy the Weierstrass equation. -/
theorem equation_of_ringHom (f : W.CoordinateRing →+* F)
    (hf : ∀ c : F, f (algebraMap F W.CoordinateRing c) = c) :
    W.Equation (f (CoordinateRing.mk W (C X))) (f (CoordinateRing.mk W Y)) := by
  have hcomp := congrArg (fun g : F[X][Y] →+* F ↦ g W.polynomial)
    (ringHom_comp_mk_eq_evalEvalRingHom f hf)
  have hzero : f (CoordinateRing.mk W W.polynomial) = 0 := by
    rw [AdjoinRoot.mk_self, map_zero]
  rw [← RingHom.comp_apply] at hzero
  rw [hcomp] at hzero
  exact hzero

/-- **An ideal of residue degree one is the ideal of a point.** Every ideal `I` for which
`F[W] ⧸ I` has finrank one over `F` is `XYIdeal W x (C y)` for some solution `(x, y)` of the
Weierstrass equation. No ellipticity or Dedekind hypothesis is involved. -/
theorem exists_equation_and_eq_XYIdeal {I : Ideal W.CoordinateRing}
    (hdeg : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (_ : W.Equation x y), I = CoordinateRing.XYIdeal W x (C y) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp <|
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hdeg]; norm_num)
  have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ I)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg
  let e : (W.CoordinateRing ⧸ I) ≃ₐ[F] F :=
    (AlgEquiv.ofBijective (Algebra.ofId F _) hbij).symm
  let ρ : W.CoordinateRing →ₐ[F] F := e.toAlgHom.comp (Ideal.Quotient.mkₐ F I)
  have hρmem : ∀ a, ρ a = 0 ↔ a ∈ I := fun a ↦ by
    rw [show ρ a = e (Ideal.Quotient.mk I a) from rfl, map_eq_zero_iff _ e.injective,
      Ideal.Quotient.eq_zero_iff_mem]
  let x₀ := ρ (CoordinateRing.mk W (C X))
  let y₀ := ρ (CoordinateRing.mk W Y)
  have hcomp : ∀ p : F[X][Y], ρ (CoordinateRing.mk W p) = p.evalEval x₀ y₀ := fun p ↦
    congrArg (fun g : F[X][Y] →+* F ↦ g p)
      (ringHom_comp_mk_eq_evalEvalRingHom ρ.toRingHom ρ.commutes)
  have heq : W.Equation x₀ y₀ := equation_of_ringHom ρ.toRingHom ρ.commutes
  refine ⟨x₀, y₀, heq, ((XYIdeal_isMaximal_of_equation heq).eq_of_le hI ?_).symm⟩
  rw [CoordinateRing.XYIdeal, Ideal.span_le, Set.pair_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, ← hρmem, CoordinateRing.XClass, hcomp]
    simp [evalEval_C]
  · rw [SetLike.mem_coe, ← hρmem, CoordinateRing.YClass, hcomp]
    simp

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
