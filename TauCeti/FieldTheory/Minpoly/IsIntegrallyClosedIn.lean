/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Minimal polynomials over a relatively algebraically closed base field

Let `F / k` be a field extension in which `k` is relatively algebraically closed, that is,
`IsIntegrallyClosedIn k F` — equivalently `algebraicClosure k F = ⊥` — and let `E` be a further
commutative `F`-algebra.  An element `x` of `E` algebraic over `k` then has the same minimal
polynomial over `F` as over `k`: the coefficients of `minpoly F x` are integral over `k`, because
that polynomial divides the monic polynomial `(minpoly k x).map (algebraMap k F)`, and relative
algebraic closedness puts them back into `k`.

Consequently, for `E` a field, `F⟮x⟯ / F` and `k⟮x⟯ / k` have the same degree.  This is the
mechanism behind the degree behaviour of a constant field extension: adjoining constants to `F`
costs exactly what adjoining them to `k` costs.

## Main results

* `TauCeti.minpoly.map_algebraMap_of_isIntegrallyClosedIn`: `minpoly F x` is the image of
  `minpoly k x`.
* `TauCeti.IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn`
  : `[F⟮x⟯ : F] = [k⟮x⟯ : k]`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.  This is the field theory behind the persistence of linear independence under a
  constant field extension (Proposition 3.6.1(b)); it is stated here for an arbitrary extension
  `F / k` with `k` relatively algebraically closed, with no function field involved.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

universe u v w

variable {k : Type u} {F : Type v} {E : Type w} [Field k] [Field F] [Algebra k F]

section CommRing

variable [CommRing E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then an element of an extension of `F` that
is algebraic over `k` has the same minimal polynomial over `F` as over `k`.

Without the hypothesis only the divisibility `minpoly F x ∣ (minpoly k x).map (algebraMap k F)`
holds; the content is that the coefficients of the left-hand factor, being integral over `k` and
lying in `F`, are constants. -/
theorem minpoly.map_algebraMap_of_isIntegrallyClosedIn (hex : IsIntegrallyClosedIn k F) {x : E}
    (hx : IsIntegral k x) : (minpoly k x).map (algebraMap k F) = minpoly F x := by
  -- make the exactness hypothesis available to instance search
  have := hex
  -- the coefficients of `minpoly F x` are integral over `k`, hence constants
  refine minpoly.map_algebraMap hx ((Polynomial.lifts_iff_coeff_lifts _).2 fun n ↦
    IsIntegrallyClosedIn.isIntegral_iff.1 ?_)
  exact Polynomial.isIntegral_coeff_of_dvd _ _ (minpoly.monic hx) (minpoly.monic hx.tower_top)
    (minpoly.dvd_map_of_isScalarTower k F x) n

end CommRing

section Field

variable [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- If `k` is relatively algebraically closed in `F`, then adjoining an element algebraic over `k`
to `F` raises the degree by exactly as much as adjoining it to `k` does. -/
theorem IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) {x : E} (hx : IsIntegral k x) :
    Module.finrank F F⟮x⟯ = Module.finrank k k⟮x⟯ := by
  rw [adjoin.finrank hx.tower_top, adjoin.finrank hx,
    ← minpoly.map_algebraMap_of_isIntegrallyClosedIn hex hx,
    Polynomial.natDegree_map_eq_of_injective (algebraMap k F).injective]

end Field

end TauCeti
