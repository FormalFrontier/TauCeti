/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Polynomial.Factors

/-!
# Evaluating a real étale algebra at its real and complex places

For a real polynomial `f`, the quotient `ℝ[X]/f` maps to a product of copies of `ℝ`, one for each
real root of `f`, and copies of `ℂ`, one for each irreducible quadratic factor — the archimedean
places of the algebra. This file builds that evaluation map and shows it is injective when `f` is
squarefree, which is the point: an element of `ℝ[X]/f` is determined by its values at
the real roots together with its values at the upper-half-plane roots of the quadratic factors.

Over `ℝ` an irreducible polynomial has degree `1` or `2` (`Irreducible.natDegree_le_two`), so those
two families exhaust the factors, and a degree-2 factor `p` has two conjugate non-real roots. One
is singled out by its sign: `Polynomial.selectedRoot` picks the one with positive imaginary part
when the two differ, `Polynomial.selectedRoot_im_pos` confirms that it really is in the upper
half-plane once `p` is quadratic, and evaluation there identifies `ℝ[X]/p` with `ℂ`
(`Polynomial.evalUpperEquiv`).

## Main definitions

* `Polynomial.selectedRoot` : a distinguished complex root of an irreducible real polynomial —
  the one with positive imaginary part when the two conjugates differ. Defined for every
  irreducible `p`; the upper-half-plane claim needs `p` quadratic and is
  `Polynomial.selectedRoot_im_pos`.
* `Polynomial.evalSelectedHom`, `Polynomial.evalUpperEquiv` : evaluation at that root, as an
  `ℝ`-algebra hom `ℝ[X]/p → ℂ` for any irreducible `p` and, for a quadratic `p`, an
  isomorphism.
* `Polynomial.etaleEvalHom` : the evaluation map
  `ℝ[X]/f → ({x // f.eval x = 0} → ℝ) × ({p : f.Factors // deg p = 2} → ℂ)`.

## Main results

* `Polynomial.selectedRoot_im_pos` : for a quadratic, the chosen root really does lie in the
  upper half-plane.
* `Polynomial.etaleEvalHom_injective` : for squarefree `f`, the evaluation map is injective.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/Mathlib/RealEtale.lean`, the section preceding the square-class decomposition.

Two things are spelled differently here, in both cases because Mathlib already has what the
source provides for itself.

* The source indexes the quadratic factors by its own `Polynomial.Factors` wrapper — a subtype
  of monic irreducible divisors. That wrapper is now this repository's, ported by #4730, so the
  factors are indexed by `f.Factors` here too and its API is reused rather than reproved:
  `Polynomial.Factors.isCoprime` for pairwise coprimality, `Polynomial.Factors.associated_prod`
  for the product of the distinct factors, and `Polynomial.Factors.linearEquivRoots` for the
  correspondence between the linear factors and the roots.
* The source proves `Module.finrank ℝ (AdjoinRoot p) = p.natDegree` for itself. That is Mathlib's
  `finrank_quotient_span_eq_natDegree`, which is stronger — it needs no `p ≠ 0` — so it is used
  instead. It has to be ascribed at the `AdjoinRoot` spelling before rewriting, since `rw` does not
  see through the definitional unfolding to `ℝ[X] ⧸ Ideal.span {p}`.
-/

public section

open Complex

namespace Polynomial

variable {p : ℝ[X]}

/-- **A distinguished complex root of an irreducible real polynomial**: of the two conjugate
roots, the one with positive imaginary part when they differ. The name deliberately does not
promise positivity, because for a linear `p` the root is real; that claim is
`selectedRoot_im_pos`, which asks for the quadratic hypothesis. -/
noncomputable def selectedRoot (hp : Irreducible p) : ℂ :=
  let z := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose
  if 0 < z.im then z else starRingEnd ℂ z

/-- The chosen root is a root: conjugation preserves vanishing of a real polynomial. -/
@[simp]
theorem aeval_selectedRoot (hp : Irreducible p) : aeval (selectedRoot hp) p = 0 := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  rw [selectedRoot]
  split_ifs with h
  · exact hz
  · rw [aeval_conj, hz, map_zero]

/-- An irreducible real quadratic has no real root, so each of its complex roots is non-real. -/
theorem im_ne_zero_of_aeval_eq_zero (hp : Irreducible p) (hd : p.natDegree = 2) {z : ℂ}
    (hz : aeval z p = 0) : z.im ≠ 0 := by
  intro him
  have hz' : z = algebraMap ℝ ℂ z.re := Complex.ext (by simp) (by simp [him])
  rw [hz', aeval_algebraMap_apply, map_eq_zero] at hz
  exact hp.not_isRoot_of_natDegree_ne_one (by omega) hz

/-- The chosen root lies in the open upper half-plane. -/
theorem selectedRoot_im_pos (hp : Irreducible p) (hd : p.natDegree = 2) :
    0 < (selectedRoot hp).im := by
  have hz := (IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hp).ne').choose_spec
  have hne := im_ne_zero_of_aeval_eq_zero hp hd hz
  rw [selectedRoot]
  split_ifs with h
  · exact h
  · rw [Complex.conj_im]
    exact neg_pos.mpr ((not_lt.mp h).lt_of_ne hne)

/-- Evaluation at the selected root, as an `ℝ`-algebra hom `ℝ[X]/p → ℂ`. For a quadratic `p`
that root is the upper-half-plane one (`selectedRoot_im_pos`), and the hom is then the
isomorphism `evalUpperEquiv`. -/
noncomputable def evalSelectedHom (hp : Irreducible p) : AdjoinRoot p →ₐ[ℝ] ℂ :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℝ ℂ) (selectedRoot hp)
    (by have := aeval_selectedRoot hp; simpa [aeval_def] using this)

/-- Evaluating a representative: the hom is evaluation of the polynomial at the selected root, so
consumers never unfold the definition. -/
@[simp]
theorem evalSelectedHom_mk (hp : Irreducible p) (q : ℝ[X]) :
    evalSelectedHom hp (AdjoinRoot.mk p q) = aeval (selectedRoot hp) q := (rfl)

theorem evalSelectedHom_injective (hp : Irreducible p) :
    Function.Injective (evalSelectedHom hp) :=
  have : Fact (Irreducible p) := ⟨hp⟩
  (evalSelectedHom hp).toRingHom.injective

/-- **`ℝ[X]/p ≃ ℂ` for an irreducible real quadratic `p`.** The evaluation hom is injective, and
a dimension count over `ℝ` makes it surjective. -/
noncomputable def evalUpperEquiv (hp : Irreducible p) (hd : p.natDegree = 2) :
    AdjoinRoot p ≃ₐ[ℝ] ℂ :=
  have : Fact (Irreducible p) := ⟨hp⟩
  AlgEquiv.ofBijective (evalSelectedHom hp) ⟨evalSelectedHom_injective hp, by
    have hsurj : Function.Surjective ⇑(evalSelectedHom hp).toLinearMap := by
      -- `AdjoinRoot p` is by definition `ℝ[X] ⧸ span {p}`, but `rw` does not see through that,
      -- so Mathlib's dimension count is ascribed at the `AdjoinRoot` spelling first.
      have hfr : Module.finrank ℝ (AdjoinRoot p) = p.natDegree :=
        finrank_quotient_span_eq_natDegree
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj (evalSelectedHom_injective hp), hfr, hd,
        Complex.finrank_real_complex]
    exact hsurj⟩

/-- Evaluating a representative through the isomorphism, for the same reason as
`evalSelectedHom_mk`. -/
@[simp]
theorem evalUpperEquiv_mk (hp : Irreducible p) (hd : p.natDegree = 2) (q : ℝ[X]) :
    evalUpperEquiv hp hd (AdjoinRoot.mk p q) = aeval (selectedRoot hp) q := (rfl)

/-! ### The evaluation map at all archimedean places -/

variable {f : ℝ[X]}

/-- The tuple of evaluation points: each real root of `f`, and the upper root of each
degree-2 factor. -/
noncomputable def etaleTuple (f : ℝ[X]) :
    ({x : ℝ // f.eval x = 0} → ℝ) × ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) :=
  (fun x ↦ (x : ℝ), fun p ↦ selectedRoot (p : f.Factors).irreducible)

/-- The real-root component of `aeval (etaleTuple f) q` is `q.eval x`. -/
@[simp]
theorem aeval_etaleTuple_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (aeval (etaleTuple f) q).1 x = q.eval (x : ℝ) := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ (fun _ : {x : ℝ // f.eval x = 0} ↦ ℝ) x).comp (AlgHom.fst ℝ _ _))
    (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.fst_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  -- `(etaleTuple f).1 x` is by definition the real number `x`, so this is ordinary evaluation.
  change aeval ((etaleTuple f).1 x) q = q.eval (x : ℝ)
  simp [etaleTuple]

/-- The degree-2-factor component of `aeval (etaleTuple f) q` is the value at the upper root. -/
@[simp]
theorem aeval_etaleTuple_snd (q : ℝ[X]) (p : {p : f.Factors // (p : ℝ[X]).natDegree = 2}) :
    (aeval (etaleTuple f) q).2 p = aeval (selectedRoot (p : f.Factors).irreducible) q := by
  have h := aeval_algHom_apply
    ((Pi.evalAlgHom ℝ (fun _ : {p : f.Factors // (p : ℝ[X]).natDegree = 2} ↦ ℂ) p).comp
      (AlgHom.snd ℝ _ _)) (etaleTuple f) q
  simp only [AlgHom.comp_apply, AlgHom.snd_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  rfl

/-- `f` itself vanishes at every evaluation point. -/
@[simp]
theorem aeval_etaleTuple : aeval (etaleTuple f) f = 0 := by
  have h1 : (aeval (etaleTuple f) f).1 = 0 := by
    funext x; rw [Pi.zero_apply, aeval_etaleTuple_fst]; exact x.2
  have h2 : (aeval (etaleTuple f) f).2 = 0 := by
    funext p
    rw [Pi.zero_apply, aeval_etaleTuple_snd]
    have hirr := (p : f.Factors).irreducible
    have hdvd : aeval (selectedRoot hirr) ((p : f.Factors) : ℝ[X]) ∣ aeval (selectedRoot hirr) f :=
      _root_.map_dvd _ (p : f.Factors).dvd
    rw [aeval_selectedRoot] at hdvd
    exact zero_dvd_iff.mp hdvd
  exact Prod.ext h1 h2

/-- **Evaluation at the archimedean places of `ℝ[X]/f`**, as an `ℝ`-algebra hom into the product
of the residue fields: `ℝ` at each real root, `ℂ` at each irreducible quadratic factor. -/
noncomputable def etaleEvalHom (f : ℝ[X]) :
    AdjoinRoot f →ₐ[ℝ]
      ({x : ℝ // f.eval x = 0} → ℝ) × ({p : f.Factors // (p : ℝ[X]).natDegree = 2} → ℂ) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId ℝ _) (etaleTuple f) (by
    have := aeval_etaleTuple (f := f); rwa [aeval_def] at this)

/-- Definitional: `AdjoinRoot.liftAlgHom_mk` and `Algebra.toRingHom_ofId` are both `rfl`, so
evaluating a representative is evaluating the polynomial. Parenthesised so that it elaborates
against the sealed body across the module boundary. -/
@[simp]
theorem etaleEvalHom_mk (q : ℝ[X]) :
    etaleEvalHom f (AdjoinRoot.mk f q) = aeval (etaleTuple f) q := (rfl)

/-- The real-root component on a representative. Deliberately not `@[simp]`: `etaleEvalHom_mk`
and `aeval_etaleTuple_fst` are simp lemmas that already reach this normal form in two steps, so
the attribute here would be a rule the simp set can prove. Kept as the one-step `rw` form. -/
theorem etaleEvalHom_mk_fst (q : ℝ[X]) (x : {x : ℝ // f.eval x = 0}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).1 x = q.eval (x : ℝ) := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_fst]

/-- The degree-2-factor component on a representative. Not `@[simp]`, for the same reason as
`etaleEvalHom_mk_fst`. -/
theorem etaleEvalHom_mk_snd (q : ℝ[X]) (p : {p : f.Factors // (p : ℝ[X]).natDegree = 2}) :
    (etaleEvalHom f (AdjoinRoot.mk f q)).2 p
      = aeval (selectedRoot (p : f.Factors).irreducible) q := by
  rw [etaleEvalHom_mk, aeval_etaleTuple_snd]

/-- **The evaluation map is injective for squarefree `f`.** A class killed at every
place is divisible by every irreducible factor of `f`; the factors are pairwise coprime, so their
product — which is `f` up to a unit — divides it. -/
theorem etaleEvalHom_injective (hsq : Squarefree f) :
    Function.Injective (etaleEvalHom f) := by
  classical
  -- `Squarefree` already excludes `0` over a domain, so nonvanishing is not a separate hypothesis.
  have hf : f ≠ 0 := hsq.ne_zero
  have : Finite f.Factors := Factors.finite hf
  have : Fintype f.Factors := Fintype.ofFinite _
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [AdjoinRoot.mk_eq_zero]
  -- Every irreducible factor divides `q`: a linear one because `q` vanishes at the root it
  -- records, a quadratic one because `q` vanishes at its selected root, which has it as minimal
  -- polynomial.
  have hfac (p : f.Factors) : (p : ℝ[X]) ∣ q := by
    rcases eq_or_ne (p : ℝ[X]).natDegree 1 with h1 | h1
    · -- `Factors.linearEquivRoots` carries the linear factor to the root of `f` it records,
      -- together with the proof that `f` vanishes there.
      obtain ⟨x, hx⟩ : ∃ x : {x : ℝ // f.eval x = 0}, (p : ℝ[X]) = X - C (x : ℝ) :=
        ⟨Factors.linearEquivRoots ⟨p, h1⟩, by
          conv_lhs => rw [p.monic.eq_X_add_C h1]
          rw [Factors.linearEquivRoots_apply, map_neg, sub_neg_eq_add]⟩
      have hq : q.eval (x : ℝ) = 0 := by simpa using congrArg (·.1 x) ha
      rw [hx]
      exact dvd_iff_isRoot.mpr hq
    · have hd2 : (p : ℝ[X]).natDegree = 2 := by
        have h0 := p.irreducible.natDegree_pos
        have h2 := p.irreducible.natDegree_le_two
        omega
      have hq : aeval (selectedRoot p.irreducible) q = 0 := by
        simpa using congrArg (·.2 ⟨p, hd2⟩) ha
      rw [minpoly.eq_of_irreducible_of_monic p.irreducible (aeval_selectedRoot p.irreducible)
        p.monic]
      exact minpoly.dvd ℝ _ hq
  -- The distinct factors are pairwise coprime, so their product divides `q`; and squarefreeness
  -- makes that product `f` up to a unit.
  exact (Factors.associated_prod hf hsq).symm.dvd.trans
    (Fintype.prod_dvd_of_coprime (fun _ _ hne ↦ Factors.isCoprime hne) hfac)

end Polynomial
