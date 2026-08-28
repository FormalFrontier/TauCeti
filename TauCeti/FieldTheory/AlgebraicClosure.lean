/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Minimal polynomials over a relatively algebraically closed base field

Let `F / k` be a field extension in which `k` is relatively algebraically closed, that is,
`IsIntegrallyClosedIn k F` — equivalently `algebraicClosure k F = ⊥` — and let `E` be a further
extension of `F`.  An element `x` of `E` algebraic over `k` then has the same minimal polynomial
over `F` as over `k`: the coefficients of `minpoly F x` are integral over `k`, because that
polynomial divides the monic polynomial `(minpoly k x).map (algebraMap k F)`, and relative
algebraic closedness puts them back into `k`.

Consequently `F⟮x⟯ / F` and `k⟮x⟯ / k` have the same degree.  This is the mechanism behind the
degree behaviour of a constant field extension: adjoining constants to `F` costs exactly what
adjoining them to `k` costs.

## Main results

* `TauCeti.map_minpoly_eq_minpoly`: `minpoly F x` is the image of `minpoly k x`.
* `TauCeti.finrank_adjoin_eq_finrank_adjoin`: `[F⟮x⟯ : F] = [k⟮x⟯ : k]`.
-/

public section

namespace TauCeti

open IntermediateField Polynomial

universe u v w

variable {k : Type u} {F : Type v} {E : Type w} [Field k] [Field F] [Field E]
variable [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then an element of an extension of `F` that
is algebraic over `k` has the same minimal polynomial over `F` as over `k`.

Without the hypothesis only the divisibility `minpoly F x ∣ (minpoly k x).map (algebraMap k F)`
holds; the content is that the coefficients of the left-hand factor, being integral over `k` and
lying in `F`, are constants. -/
theorem map_minpoly_eq_minpoly (hex : IsIntegrallyClosedIn k F) {x : E} (hx : IsIntegral k x) :
    (minpoly k x).map (algebraMap k F) = minpoly F x := by
  -- make the exactness hypothesis available to instance search
  have := hex
  have hxF : IsIntegral F x := hx.tower_top
  have hmk : (minpoly k x).Monic := minpoly.monic hx
  have hmF : (minpoly F x).Monic := minpoly.monic hxF
  have hinj : Function.Injective (algebraMap k F) := (algebraMap k F).injective
  have hmap0 : (minpoly k x).map (algebraMap k F) ≠ 0 := (hmk.map _).ne_zero
  have hdvd : minpoly F x ∣ (minpoly k x).map (algebraMap k F) :=
    minpoly.dvd F x (by rw [aeval_map_algebraMap]; exact minpoly.aeval k x)
  -- The coefficients of `minpoly F x` are integral over `k`, hence constants.
  obtain ⟨r, hr⟩ := (Polynomial.mem_lifts _).1 <| (Polynomial.lifts_iff_coeff_lifts _).2 fun n ↦
    IsIntegrallyClosedIn.isIntegral_iff.1
      (Polynomial.isIntegral_coeff_of_dvd _ _ hmk hmF hdvd n)
  have hr0 : r ≠ 0 := fun h ↦ hmF.ne_zero (by rw [← hr, h, Polynomial.map_zero])
  have haev : aeval x r = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F x r, hr]; exact minpoly.aeval F x
  -- so `minpoly k x` divides it too, and the two degrees squeeze together
  have h1 : (minpoly k x).natDegree ≤ r.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd k x haev) hr0
  have hdeg : r.natDegree = (minpoly F x).natDegree := by
    rw [← hr, Polynomial.natDegree_map_eq_of_injective hinj]
  refine (Polynomial.eq_of_monic_of_associated hmF (hmk.map _) ?_).symm
  refine Polynomial.associated_of_dvd_of_natDegree_le hdvd hmap0 ?_
  rw [Polynomial.natDegree_map_eq_of_injective hinj]
  omega

/-- If `k` is relatively algebraically closed in `F`, then adjoining an element algebraic over `k`
to `F` raises the degree by exactly as much as adjoining it to `k` does. -/
theorem finrank_adjoin_eq_finrank_adjoin (hex : IsIntegrallyClosedIn k F) {x : E}
    (hx : IsIntegral k x) : Module.finrank F F⟮x⟯ = Module.finrank k k⟮x⟯ := by
  rw [adjoin.finrank hx.tower_top, adjoin.finrank hx,
    ← map_minpoly_eq_minpoly hex hx,
    Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective]

end TauCeti
