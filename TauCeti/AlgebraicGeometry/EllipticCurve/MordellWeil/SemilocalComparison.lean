/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# The semilocal comparison of `2`-descent at the good finite places

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal form
over a number field `F`, with étale algebra `W.A = F[X] ⧸ (f)` and square classes `W.M`. Two
subgroups of `W.M` cut out by valuation conditions are in play:

* `W.selmerGroupA (𝓞 F)` — the `S`-unramifiedness condition `A(S,2)`, a *global* condition at the
  primes of the rings of integers of the field factors of `W.A` not lying above a bad prime;
* `(W⁄F_v).toAffine.selmerGroupA 𝒪_v` — the same condition for the curve base-changed to the
  completion at a finite place `v`.

This file compares the two at the **good** finite places, in both directions: an `S`-unramified
class localizes to an unramified class at each good place, and conversely a class that localizes
to an unramified class at every good place is `S`-unramified. That is what makes the local
conditions at the good finite places redundant — they are already implied by `A(S,2)` — so
membership in the `2`-Selmer group reduces to the finitely many conditions at the bad and infinite
places.

## Main results

* `WeierstrassCurve.Affine.localRes_mem_selmerGroupA` (global to local): an `S`-unramified square
  class localizes to an unramified class at every good finite place.
* `WeierstrassCurve.Affine.mem_selmerGroupA_of_forall_localRes` (local to global): a square class
  that localizes to an unramified class at every good finite place is `S`-unramified.

## Provenance

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache 2.0, by Michael Stoll) at commit
`66889eada51a`: `EllipticCurves/SelmerGroup.lean`, section `Semilocal`, together with
`AdjoinRoot.map_comp_algebraMap` from `EllipticCurves/Mathlib/Basic.lean`. The source states
square classes as its own `Units.modPow`; they are re-spelled here to this repository's single
spelling `Mˣ ⧸ (powMonoidHom n).range`, and `HeightOneSpectrum.below` is Mathlib's
`HeightOneSpectrum.under`.

-/

public section

open IsDedekindDomain NumberField Polynomial


namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [NumberField F] (W : Affine F)

/- Notation local to this file: `F_[v]` and `𝒪_[v]` are the completion of `F` at the finite place
`v` and its valuation ring, `𝕎[v]` is the base change of `W` to `F_[v]` as an affine curve, and
`𝕃 p` is the field factor `F[X] ⧸ (p)` of the étale algebra attached to a factor `p` of `f`. -/
local notation:max "F_[" v "]" => HeightOneSpectrum.adicCompletion F v
local notation:max "𝒪_[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v
local notation:max "𝕎[" v "]" =>
  WeierstrassCurve.toAffine (W⁄(HeightOneSpectrum.adicCompletion F v))
local notation:max "𝕃" p:max => AdjoinRoot (p : F[X])

section Semilocal

open AdjoinRoot IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 F))

/- The instance found by unifying through the `ringOfIntegersFactor` abbreviation carries
mismatched `SMul` arguments; pin them to the `Algebra`-derived ones. -/
private instance instIsScalarTowerRingOfIntegersFactor (p : W.f.Factors) :
    @IsScalarTower (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

/- Goodness transfers to the completion: over the valuation ring of a good place, the base-changed
curve has no bad primes. -/
private lemma badPrimes_adicCompletionIntegers {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ W.badPrimes (𝓞 F)) : 𝕎[v].badPrimes 𝒪_[v] = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false, mem_badPrimes_iff]
  have hPval (z : F) : P.valuation F_[v] (algebraMap F F_[v] z) = v.valuation F z :=
    valuation_adicCompletion_algebraMap v P z
  have hone {y : F} {c : F_[v]} (hc : c = algebraMap F F_[v] y)
      (h : P.valuation F_[v] c ≠ 1) : v.valuation F y ≠ 1 := by
    rwa [hc, hPval] at h
  have hsupp {y : F} {c : F_[v]} (hc : c = algebraMap F F_[v] y)
      (h : 1 < P.valuation F_[v] c) : ¬ v.valuation F y ≤ 1 :=
    not_le.mpr <| by rwa [hc, hPval] at h
  rintro (h | h | h | h | h)
  · exact hone (by rw [map_ofNat]) h (W.valuation_two_eq_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hone (_root_.WeierstrassCurve.map_Δ ..) h
      (W.valuation_Δ_eq_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (_root_.WeierstrassCurve.map_a₂ ..) h
      (W.valuation_a₂_le_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (_root_.WeierstrassCurve.map_a₄ ..) h
      (W.valuation_a₄_le_one_of_notMem_badPrimes (𝓞 F) hv)
  · exact hsupp (_root_.WeierstrassCurve.map_a₆ ..) h
      (W.valuation_a₆_le_one_of_notMem_badPrimes (𝓞 F) hv)

/- The base-change map on a field factor is integral on the ring of integers. -/
private lemma isIntegral_mapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (x : W.ringOfIntegersFactor (𝓞 F) p) :
    _root_.IsIntegral 𝒪_[v] (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  refine ⟨P.map (algebraMap (𝓞 F) 𝒪_[v]), hPm.map _, ?_⟩
  have h2 := congrArg (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) hPe
  rw [map_zero, Polynomial.hom_eval₂] at h2
  rw [Polynomial.eval₂_map]
  exact (congrArg (fun φ ↦ Polynomial.eval₂ φ
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) P)
    (AdjoinRoot.map_comp_algebraMap v hq)).symm.trans h2

/- The base-change map on the rings of integers of the field factors: the restriction of
`AdjoinRoot.map` to the integral closures. -/
private noncomputable def integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    W.ringOfIntegersFactor (𝓞 F) p →+* 𝕎[v].ringOfIntegersFactor 𝒪_[v] q :=
  ((AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
    (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p))).codRestrict
      (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X]))).toSubring
      fun x ↦ W.isIntegral_mapOfDvd v hq x

/- The square of ring homomorphisms defining `integerMapOfDvd`. -/
private lemma algebraMap_comp_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (algebraMap (𝕎[v].ringOfIntegersFactor 𝒪_[v] q) (AdjoinRoot (q : F_[v][X]))).comp
        (W.integerMapOfDvd v hq) =
      (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
        (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)) :=
  RingHom.ext fun _ ↦ rfl

/- The square `𝓞 F → 𝒪_v → B_q` versus `𝓞 F → B_p → B_q` on the rings of integers. -/
private lemma integerMapOfDvd_comp_algebraMap {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (W.integerMapOfDvd v hq).comp (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) =
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)).comp
        (algebraMap (𝓞 F) 𝒪_[v]) := by
  ext c
  exact RingHom.congr_fun (AdjoinRoot.map_comp_algebraMap v hq) c

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/- The `F_v`-algebra structure on the completion of the field factor `F[X] ⧸ (p)` at a place `w`
above `v`, via `adicCompletionExtension`; a local instance for the constructions below. -/
@[implicit_reducible]
private noncomputable def algebraAdicCompletionFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra F_[v] (w.adicCompletion (𝕃 p)) :=
  (adicCompletionExtension F (𝕃 p) v w).toAlgebra

attribute [local instance] algebraAdicCompletionFactor

/- The `algebraMap` of that local instance is `adicCompletionExtension` itself. Stated here,
where `algebraAdicCompletionFactor` is visible, because `adicCompletionExtension` is not exposed
outside its own module, so the identification is not available by `rfl` at the use sites. -/
private lemma algebraMap_adicCompletionFactor_apply (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (x : F_[v]) :
    algebraMap F_[v] (w.adicCompletion (𝕃 p)) x = adicCompletionExtension F (𝕃 p) v w x :=
  rfl

/- The square `F → F_v → (F[X] ⧸ (p))_w` = `F → F[X] ⧸ (p) → (F[X] ⧸ (p))_w` of coefficient maps. -/
private lemma algebraMap_adicCompletion_comp (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap F_[v] (w.adicCompletion (𝕃 p))).comp (algebraMap F F_[v]) =
      (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).comp (algebraMap F (𝕃 p)) :=
  RingHom.ext fun c ↦ adicCompletionExtension_coe F (𝕃 p) v w c

/- Evaluating a base-changed polynomial at the image of the root in the completion. -/
private lemma aeval_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (g : F[X]) :
    Polynomial.aeval (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X])))
        (g.map (algebraMap F F_[v])) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (AdjoinRoot.mk (p : F[X]) g) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← aeval_eq, Polynomial.aeval_def,
    Polynomial.hom_eval₂]
  exact congrArg (fun φ ↦ Polynomial.eval₂ φ
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) g)
    (W.algebraMap_adicCompletion_comp v p w)

/- The image of the root in the completion is integral over `F_v`. -/
private lemma isIntegral_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    _root_.IsIntegral F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) := by
  refine ⟨(p : F[X]).map (algebraMap F F_[v]), p.monic.map _, ?_⟩
  rw [← Polynomial.aeval_def, W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_self, map_zero]

/- The local factor of `f` attached to a place `w` of the field factor `F[X] ⧸ (p)` above `v`: the
minimal polynomial over `F_v` of the image of the root in the completion at `w`. -/
private noncomputable def localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].f.Factors :=
  ⟨minpoly F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))),
    minpoly.irreducible (W.isIntegral_root_adicCompletion v p w),
    minpoly.monic (W.isIntegral_root_adicCompletion v p w), by
      rw [baseChange_f]
      refine minpoly.dvd _ _ ?_
      rw [W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_eq_zero.mpr p.dvd, map_zero]⟩

private lemma coe_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactor v p w : F_[v][X]) =
      minpoly F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) :=
  rfl

/- The embedding of the local field factor into the completion, sending the root of the local
factor to the image of the global root. -/
private noncomputable def localFactorEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    AdjoinRoot (W.localFactor v p w : F_[v][X]) →+* w.adicCompletion (𝕃 p) :=
  AdjoinRoot.lift (algebraMap F_[v] (w.adicCompletion (𝕃 p)))
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) (by
      rw [W.coe_localFactor v p w]
      exact minpoly.aeval _ _)

/- The square `𝒪_v → F_v[X] ⧸ (q) → (F[X] ⧸ (p))_w` = `𝒪_v → 𝒪_w → (F[X] ⧸ (p))_w`. -/
private lemma localFactorEmb_comp_algebraMap (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactorEmb v p w).comp
        (algebraMap 𝒪_[v] (AdjoinRoot (W.localFactor v p w : F_[v][X]))) =
      (algebraMap (w.adicCompletionIntegers (𝕃 p)) (w.adicCompletion (𝕃 p))).comp
        (adicCompletionIntegersExtension F (𝕃 p) v w) := by
  ext c
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply 𝒪_[v] F_[v]
      (AdjoinRoot (W.localFactor v p w : F_[v][X])),
    AdjoinRoot.algebraMap_eq, localFactorEmb, AdjoinRoot.lift_of]
  rw [RingHom.comp_apply, W.algebraMap_adicCompletionFactor_apply v p w]
  exact congrArg _ (coe_adicCompletionIntegersExtension F (𝕃 p) v w c).symm

/- The embedding maps the local ring of integers into the integers of the completion. -/
private lemma localFactorEmb_mem_adicCompletionIntegers (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (x : 𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w)) :
    W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X])) ∈
      w.adicCompletionIntegers (𝕃 p) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  have h2 := congrArg (W.localFactorEmb v p w) hPe
  rw [map_zero, Polynomial.hom_eval₂, W.localFactorEmb_comp_algebraMap v p w] at h2
  have hint2 : _root_.IsIntegral (w.adicCompletionIntegers (𝕃 p))
      (W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X]))) := by
    refine ⟨P.map (adicCompletionIntegersExtension F (𝕃 p) v w), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h2
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint2
  rw [← hy]
  exact y.2

/- The restriction of `localFactorEmb` to the rings of integers. -/
private noncomputable def localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w) →+* w.adicCompletionIntegers (𝕃 p) :=
  ((W.localFactorEmb v p w).comp (algebraMap _ _)).codRestrict
    (w.adicCompletionIntegers (𝕃 p)).toSubring
    fun x ↦ W.localFactorEmb_mem_adicCompletionIntegers v p w x

private lemma algebraMap_comp_localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap (w.adicCompletionIntegers (𝕃 p)) (w.adicCompletion (𝕃 p))).comp
        (W.localFactorIntegerEmb v p w) =
      (W.localFactorEmb v p w).comp (algebraMap _ _) :=
  RingHom.ext fun _ ↦ rfl

/- The contraction of the maximal ideal of `𝒪_w` to the local ring of integers is nonzero. -/
private lemma comap_localFactorIntegerEmb_ne_bot (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p))).asIdeal.comap
      (W.localFactorIntegerEmb v p w) ≠ ⊥ := by
  refine Ideal.ne_bot_of_comap_ne_bot _ (FaithfulSMul.algebraMap_injective 𝒪_[v]
    (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) ?_
  have hsq0 : (W.localFactorIntegerEmb v p w).comp
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) =
      adicCompletionIntegersExtension F (𝕃 p) v w := by
    ext c : 2
    exact RingHom.congr_fun (W.localFactorEmb_comp_algebraMap v p w) c
  -- `comap_maximalIdeal_adicCompletionIntegersExtension` is stated for
  -- `IsLocalRing.maximalIdeal`, while contracting a prime lands on the `HeightOneSpectrum`
  -- wrapper's `asIdeal`. The two are the same term, but `rw` needs the goal written in the
  -- second spelling and no named equality bridges them, so the identification is `rfl` here.
  rw [Ideal.comap_comap, hsq0,
    show (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p))).asIdeal =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p)) from rfl,
    comap_maximalIdeal_adicCompletionIntegersExtension]
  exact IsDiscreteValuationRing.not_a_field _

/- The embedding of the local field factor is compatible with the CRT projections. -/
private lemma localFactorEmb_projFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.A) :
    W.localFactorEmb v p w (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w) (W.mapA F_[v] a)) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (projFactor W.f_ne_zero W.squarefree_f p a) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [mapA_mk, projFactor_mk, projFactor_mk, localFactorEmb, AdjoinRoot.lift_mk]
  exact W.aeval_root_adicCompletion v p w g

/- Unfolding of the local unramifiedness condition into per-factor divisibilities. -/
private lemma localRes_mem_selmerGroupA_iff (a : W.Aˣ) :
    W.localRes F_[v] (QuotientGroup.mk a) ∈ 𝕎[v].selmerGroupA 𝒪_[v] ↔
      ∀ (q : 𝕎[v].f.Factors) (w' : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)),
        w' ∉ HeightOneSpectrum.primesAbove 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)
          (𝕎[v].badPrimes 𝒪_[v]) →
        (2 : ℤ) ∣ Multiplicative.toAdd (w'.valuationOfNeZero
          (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toRingHom.toMonoidHom
            (Units.map (W.mapA F_[v]).toMonoidHom a))) := by
  rw [localRes_mk]
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff]

/- Transport of the divisibility from the contracted prime of the local factor to `w`. -/
private lemma dvd_toAdd_valuationOfNeZero_of_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.Aˣ)
    (h : (2 : ℤ) ∣ Multiplicative.toAdd ((HeightOneSpectrum.comapOfNeBot
        (W.localFactorIntegerEmb v p w) (IsDiscreteValuationRing.maximalIdeal _)
        (W.comap_localFactorIntegerEmb_ne_bot v p w)).valuationOfNeZero
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)))) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
      (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a)) := by
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (W.localFactorEmb v p w) (W.localFactorIntegerEmb v p w)
    (W.algebraMap_comp_localFactorIntegerEmb v p w)
    (IsDiscreteValuationRing.maximalIdeal _)
    (W.comap_localFactorIntegerEmb_ne_bot v p w) _ h
  have hunits : Units.map (W.localFactorEmb v p w : _ →* _)
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)) =
      Units.map (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).toMonoidHom
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a) :=
    Units.ext (W.localFactorEmb_projFactor v p w (a : W.A))
  rw [hunits, HeightOneSpectrum.valuationOfNeZero_maximalIdeal_adicCompletionIntegers] at hkey
  exact hkey

/- The double contraction of a prime of the local ring of integers is `v`. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma comap_comap_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    (w.asIdeal.comap (W.integerMapOfDvd v hq)).comap
      (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) = v.asIdeal := by
  rw [Ideal.comap_comap, integerMapOfDvd_comp_algebraMap W v hq, ← Ideal.comap_comap]
  have h1 : w.asIdeal.comap (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) =
      IsLocalRing.maximalIdeal 𝒪_[v] :=
    IsLocalRing.eq_maximalIdeal (HeightOneSpectrum.under 𝒪_[v] w).isMaximal
  rw [h1, ← Ideal.under_def, HeightOneSpectrum.under_maximalIdeal_adicCompletionIntegers]

/- The contraction of a prime of the local ring of integers to the global one is nonzero. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma comap_integerMapOfDvd_ne_bot {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    w.asIdeal.comap (W.integerMapOfDvd v hq) ≠ ⊥ := by
  refine Ideal.ne_bot_of_comap_ne_bot _ (FaithfulSMul.algebraMap_injective (𝓞 F)
    (W.ringOfIntegersFactor (𝓞 F) p)) ?_
  rw [W.comap_comap_integerMapOfDvd v hq w]
  exact v.ne_bot

/- The contracted prime lies over `v`. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma under_comapOfNeBot_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    HeightOneSpectrum.under (𝓞 F) (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w
      (W.comap_integerMapOfDvd_ne_bot v hq w)) = v :=
  HeightOneSpectrum.ext <| by
    simpa [HeightOneSpectrum.under, HeightOneSpectrum.comapOfNeBot_asIdeal] using
      W.comap_comap_integerMapOfDvd v hq w

/- The base-change maps of the field factors are compatible with the CRT projections. -/
private lemma map_projFactor {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) (a : W.A) :
    AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (projFactor W.f_ne_zero W.squarefree_f p a) =
      projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q (W.mapA F_[v] a) := by
  obtain ⟨g, rfl⟩ := mk_surjective a
  rw [projFactor_mk, AdjoinRoot.map_mk, mapA_mk, projFactor_mk]

end Semilocal

variable [W.IsElliptic] [W.IsCharNeTwoNF]

open AdjoinRoot in
open scoped Classical in
/-- **Semilocal comparison, global to local**: an `S`-unramified square class localizes to an
unramified class at every good finite place. -/
theorem localRes_mem_selmerGroupA {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ W.badPrimes (𝓞 F))
    {m : W.M} (hm : m ∈ W.selmerGroupA (𝓞 F)) :
    W.localRes F_[v] m ∈ 𝕎[v].selmerGroupA 𝒪_[v] := by
  -- Each monic irreducible factor `q` of `f` over `F_v` divides the image of a factor `p` of `f`;
  -- the induced embedding `F[X] ⧸ (p) → F_v[X] ⧸ (q)` restricts to the rings of integers, the
  -- prime of the local ring of integers contracts to a prime `w ∣ v`, and the local valuation is
  -- the `w`-adic one raised to the ramification index, so evenness transfers.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply] at hm ⊢
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff] at hm
  rw [W.localRes_mem_selmerGroupA_iff v a]
  intro q w hw
  -- find the global factor `p` below the local factor `q`
  obtain ⟨p, hq⟩ := Polynomial.Factors.exists_dvd_map (algebraMap F F_[v]) W.f_ne_zero q.prime
    (q.dvd.trans (W.baseChange_f F_[v]).dvd)
  -- the prime of the global field factor below `w`
  have hne := W.comap_integerMapOfDvd_ne_bot v hq w
  have hunder := W.under_comapOfNeBot_integerMapOfDvd v hq w
  -- the global unramifiedness hypothesis at that prime
  have hdvd := hm p (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w hne) fun hmem ↦
    hv (hunder ▸ (HeightOneSpectrum.mem_primesAbove_iff (𝓞 F) _ _ _).mp hmem)
  -- transport along the embedding of field factors
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) (W.integerMapOfDvd v hq)
    (W.algebraMap_comp_integerMapOfDvd v hq) w hne _ hdvd
  have hunits : Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a) =
      Units.map (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq : _ →* _)
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a) :=
    Units.ext (W.map_projFactor v hq (a : W.A)).symm
  rw [hunits]
  exact hkey

open AdjoinRoot in
open scoped Classical in
/-- **Semilocal comparison, local to global**: a square class that localizes to an unramified class
at every good finite place is `S`-unramified. -/
theorem mem_selmerGroupA_of_forall_localRes {m : W.M}
    (hm : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ W.badPrimes (𝓞 F) →
      W.localRes F_[v] m ∈ 𝕎[v].selmerGroupA 𝒪_[v]) :
    m ∈ W.selmerGroupA (𝓞 F) := by
  -- Every prime `w` of a field factor `F[X] ⧸ (p)` above a good place `v` arises from a factor of
  -- `f` over `F_v`, namely the minimal polynomial of the image of the root in the completion at
  -- `w` (`localFactor`). Evenness transports from the primes of the local ring of integers
  -- through the completion `(F[X] ⧸ (p))_w` back to `w`.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply]
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff]
  intro p w hw
  have hv : HeightOneSpectrum.under (𝓞 F) w ∉ W.badPrimes (𝓞 F) :=
    W.under_notMem_badPrimes (𝓞 F) p hw
  refine W.dvd_toAdd_valuationOfNeZero_of_localFactor (HeightOneSpectrum.under (𝓞 F) w) p w a ?_
  refine (W.localRes_mem_selmerGroupA_iff (HeightOneSpectrum.under (𝓞 F) w) a).mp
    (hm (HeightOneSpectrum.under (𝓞 F) w) hv) _ _ ?_
  rw [HeightOneSpectrum.mem_primesAbove_iff, W.badPrimes_adicCompletionIntegers hv]
  exact Set.notMem_empty _

end WeierstrassCurve.Affine

end
