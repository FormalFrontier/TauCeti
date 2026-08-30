/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Complex conjugation on exact cyclotomic integers

For positive `e`, complex conjugation preserves `ℤ[ζ_e]` and is determined by
`ζ_e ↦ ζ_e⁻¹ = ζ_e ^ (e - 1)`.  This file implements that substitution directly on the
coefficient-vector type `TauCeti.Cyclotomic e`, proves that it agrees with complex conjugation
under the distinguished embedding into `ℂ`, and equips the exact ring with its canonical
star-ring structure.

The operation is a genuine computation: it evaluates the canonical coefficient list at
`ζ_e ^ (e - 1)` using `TauCeti.Cyclotomic.evalCoeffs`.  In particular, exact Hermitian products
can be checked before any passage to `ℂ`; this is needed by the cyclotomic stage of the
Burnside--Dixon--Schneider character-table solver.

## Main definitions

* `TauCeti.Cyclotomic.instStar`: computable conjugation on exact cyclotomic integers, given by the
  substitution `ζ_e ↦ ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.instStarRing`: the canonical star-ring structure for positive conductor.

## Main results

* `TauCeti.Cyclotomic.star_def`: `star` evaluates the canonical coefficient vector at
  `ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.star_zeta`: conjugation sends `ζ_e` to `ζ_e ^ (e - 1)`.
* `TauCeti.Cyclotomic.complexEmbedding_star`: the distinguished complex embedding intertwines
  exact and complex conjugation.
* `TauCeti.Cyclotomic.reduce_star`: reducing a conjugate at a cyclotomic root `r` is reduction of
  the original exact integer at `r ^ (e - 1)`.

## References

This supplies the exact conjugation needed by Layer 6, “The assembled solver”, of the character
theory roadmap: the exact checker must verify the Hermitian row-orthogonality relation in
`Cyclotomic e` before embedding its output into `ℂ`.
-/

public section

namespace TauCeti.Cyclotomic

variable {e : ℕ}

/-- `star` on exact cyclotomic integers evaluates the canonical coefficient vector after replacing
`ζ_e` by `ζ_e ^ (e - 1)`.  For positive `e` this power is `ζ_e⁻¹`, so the substitution is complex
conjugation on exact `e`-th cyclotomic integers. -/
instance instStar : Star (Cyclotomic e) where
  star x := evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ (e - 1)) x

/-- `star` is the computable substitution `ζ_e ↦ ζ_e ^ (e - 1)`: it evaluates the canonical
coefficient vector at that power.  This is the defining equation of `Star (Cyclotomic e)`; it is
not `simp`, since it unfolds into coefficient lists. -/
theorem star_def (x : Cyclotomic e) :
    star x = evalCoeffs (Int.castRingHom (Cyclotomic e)) (zeta e ^ (e - 1)) x :=
  rfl

private theorem map_evalCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (f : ℤ →+* R) (r : R) (x : Cyclotomic e) :
    g (evalCoeffs f r x) = evalCoeffs (g.comp f) (g r) x := by
  rw [evalCoeffs_eq_eval₂, evalCoeffs_eq_eval₂, Polynomial.hom_eval₂]

variable [NeZero e]

private theorem complexEmbedding_eq_evalCoeffs (x : Cyclotomic e) :
    complexEmbedding x = evalCoeffs (Int.castRingHom ℂ) (complexRoot e) x := by
  rw [complexEmbedding_apply, evalCoeffs_eq_eval₂, Polynomial.aeval_def, algebraMap_int_eq]

/-- **The distinguished complex embedding intertwines exact conjugation with complex
conjugation.** -/
@[simp]
theorem complexEmbedding_star (x : Cyclotomic e) :
    complexEmbedding (star x) = star (complexEmbedding x) := by
  calc
    complexEmbedding (star x) =
        evalCoeffs (complexEmbedding.comp (Int.castRingHom (Cyclotomic e)))
          (complexEmbedding (zeta e ^ (e - 1))) x := by
      rw [star_def, map_evalCoeffs]
    _ = evalCoeffs (Int.castRingHom ℂ) (complexRoot e ^ (e - 1)) x := by
      congr 1
      · exact RingHom.ext_int _ _
      · rw [map_pow, complexEmbedding_zeta]
    _ = evalCoeffs (Int.castRingHom ℂ) (star (complexRoot e)) x := by
      congr 1
      simpa only [starRingEnd_apply] using
        (conj_complexRoot_eq_pow_sub_one (e := e)).symm
    _ = star (evalCoeffs (Int.castRingHom ℂ) (complexRoot e) x) := by
      have h := (map_evalCoeffs (e := e) (starRingEnd ℂ) (Int.castRingHom ℂ)
        (complexRoot e) x).symm
      rw [RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
        (Int.castRingHom ℂ)] at h
      exact h
    _ = star (complexEmbedding x) := by rw [complexEmbedding_eq_evalCoeffs]

/-- Exact cyclotomic integers form a star ring under complex conjugation. -/
instance instStarRing : StarRing (Cyclotomic e) where
  star_involutive x := complexEmbedding_injective <| calc
    complexEmbedding (star (star x)) = star (complexEmbedding (star x)) :=
      complexEmbedding_star _
    _ = star (star (complexEmbedding x)) := by rw [complexEmbedding_star]
    _ = complexEmbedding x := star_star _
  star_add x y := complexEmbedding_injective <| calc
    complexEmbedding (star (x + y)) = star (complexEmbedding (x + y)) :=
      complexEmbedding_star _
    _ = star (complexEmbedding x + complexEmbedding y) := by rw [map_add]
    _ = star (complexEmbedding x) + star (complexEmbedding y) := star_add _ _
    _ = complexEmbedding (star x) + complexEmbedding (star y) := by
      rw [complexEmbedding_star, complexEmbedding_star]
    _ = complexEmbedding (star x + star y) := (map_add _ _ _).symm
  star_mul x y := complexEmbedding_injective <| calc
    complexEmbedding (star (x * y)) = star (complexEmbedding (x * y)) :=
      complexEmbedding_star _
    _ = star (complexEmbedding x * complexEmbedding y) := by rw [map_mul]
    _ = star (complexEmbedding y) * star (complexEmbedding x) := star_mul _ _
    _ = complexEmbedding (star y) * complexEmbedding (star x) := by
      rw [complexEmbedding_star, complexEmbedding_star]
    _ = complexEmbedding (star y * star x) := (map_mul _ _ _).symm

/-- Conjugation sends the distinguished generator to `ζ_e ^ (e - 1)`. -/
@[simp]
theorem star_zeta : star (zeta e) = zeta e ^ (e - 1) := by
  apply complexEmbedding_injective
  rw [complexEmbedding_star, ← starRingEnd_apply, complexEmbedding_zeta,
    conj_complexRoot_eq_pow_sub_one, map_pow, complexEmbedding_zeta]

omit [NeZero e] in
/-- Evaluation at a cyclotomic root `r` intertwines `star` with substituting `r ^ (e - 1)`, the
inverse of `r` when `e` is positive. -/
theorem evalRingHom_star {R : Type*} [CommRing R] (f : ℤ →+* R) (r : R)
    (hr : (Polynomial.cyclotomic e ℤ).eval₂ f r = 0) (x : Cyclotomic e) :
    evalRingHom f r hr (star x) = evalCoeffs f (r ^ (e - 1)) x := by
  rw [star_def, map_evalCoeffs]
  congr 1
  · exact RingHom.ext_int _ _
  · rw [map_pow, evalRingHom_zeta]

omit [NeZero e] in
/-- **Reduction intertwines `star` with passing to the `(e - 1)`-st power of the chosen cyclotomic
root.** Reducing `star x` at `r` is the same as reducing `x` at `r ^ (e - 1)`, which for positive
`e` and primitive `r` is `r⁻¹`. This is the exact relation between conjugate cyclotomic entries
and the residue tuples used by the Dixon lift. -/
theorem reduce_star (p : ℕ) (r : ZMod p)
    (hr : (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (ZMod p)) r = 0)
    (x : Cyclotomic e) :
    reduce p r (star x) = reduce p (r ^ (e - 1)) x := by
  rw [reduce, evalCoeffs_eq_eval₂, ← evalRingHom_apply _ _ hr, evalRingHom_star, reduce]

/-! The exact operation reduces in the kernel. -/

example : star (zeta 3) = zeta 3 ^ 2 := by decide

example : star (zeta 4 + 1) = -(zeta 4) + 1 := by decide

end TauCeti.Cyclotomic
