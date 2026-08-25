/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
-- `intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0`: the diagonal entries of a `Γ₀(N)`
-- matrix are mutually inverse mod `N`.
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate

/-!
# The upper-left unit character of `Δ₀(N)`

An element of `Δ₀(N)` is an integral matrix, upper-triangular modulo `N`, whose upper-left
entry is a unit mod `N`. Reducing that entry gives a map

```
Δ₀(N) → (ZMod N)ˣ
```

which is multiplicative, because the lower-left entry vanishes mod `N` and so the cross term
in the product drops out. This is the `Δ₀(N)` counterpart of Mathlib's `Gamma0Map`, which
takes the *lower-right* entry of an element of `Γ₀(N)`; on `Γ₀(N)` the two are inverse to one
another, since `ad ≡ 1` there.

Composing with `χ : (ZMod N)ˣ →* ℂˣ` gives the twisting character of the `χ`-twisted Hecke
ring. It is **not** an extension of the nebentypus: `Delta0UpperUnit_mapGL` says that on
`Γ₀(N)` the composite `χ ∘ Delta0UpperUnit` restricts to the *inverse* of
`χ ∘ (Gamma0Map N).toHomUnits`, which is the character `modFormCharSpace` is defined by.

The inverse is the convention, not an accident. The twisted double-coset operator *divides*
by the character — each representative contributes `χ(·)⁻¹ • (f ∣[k] ·)` — so the value that
has to be attached to a monoid element is the reciprocal of the one attached to a group
element acting on forms. Reading `Delta0UpperUnit` as an extension of the nebentypus and
dropping the inverse would negate every twist downstream.

## Main definitions

* `HeckeRing.GL2.Delta0UpperUnit`: the monoid homomorphism `Δ₀(N) →* (ZMod N)ˣ`.

## Main results

* `HeckeRing.GL2.Delta0UpperUnit_apply_val`: *any* integral witness computes it. The
  definition has to choose a witness, but the witness is unique, so no consumer needs the
  chosen one.
* `HeckeRing.GL2.mapGL_mem_Delta0`: `Γ₀(N)` lands in `Δ₀(N)`, so the comparison below needs
  no membership hypothesis.
* `HeckeRing.GL2.Delta0UpperUnit_mapGL`: on `Γ₀(N)` it is inverse to `Gamma0Map`.
* `HeckeRing.GL2.adjugateGL_mapGL_mem_Delta0`: the adjugate of a `Γ₀(N)` matrix
  is again in `Δ₀(N)`, being the image of another `Γ₀(N)` element.
* `HeckeRing.GL2.Delta0UpperUnit_adjugateGL_mapGL`: on the adjugate the upper-left unit is
  `Gamma0Map` itself rather than its inverse — the second, non-inverted face of the
  character.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5 (Hecke operators with nebentypus).
* Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`](https://github.com/CBirkbeck/AINTLIB) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, declarations `delta0IntegralMatrix`,
  `delta0UpperUnit` and `delta0NebentypusDeltaChar`. Twelve source declarations are bundled
  here into one `MonoidHom` with a witness-free eliminator; the source states its API against
  a chosen `Classical.choose` witness instead.
* The adjugate comparison `Delta0UpperUnit_adjugateGL_mapGL` follows `char_bridge` in the same
  project's
  [`HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean`](https://github.com/CBirkbeck/AINTLIB)
  at the same commit. The source works with an explicit integral adjugate; here
  `adjugateGL_eq_inv` reduces it to the already-proved `Delta0UpperUnit_mapGL` at `γ⁻¹`.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **On `Γ₀(N)` the upper-left unit inverts `Gamma0Map`.** The determinant is one and the
lower-left entry vanishes mod `N`, so `ad ≡ 1`: the upper-left unit of `γ` viewed in `Δ₀(N)`
is the inverse of the lower-right unit Mathlib's `Gamma0Map` records.

So `Delta0UpperUnit` does **not** extend the nebentypus along `Gamma0Map`; it restricts to the
inverse of it. That is the convention the twisted Hecke ring wants, because the twisted
double-coset operator divides by the character rather than multiplying by it. -/
@[simp] lemma Delta0UpperUnit_mapGL (γ : Gamma0 N) :
    Delta0UpperUnit N ⟨_, mapGL_mem_Delta0 N γ⟩ = ((Gamma0Map N).toHomUnits γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  ext
  rw [Units.val_mul, Units.val_one,
    Delta0UpperUnit_apply_val N (A := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [mapGL_coe_matrix, algebraMap_int_eq]),
    MonoidHom.coe_toHomUnits, Gamma0Map]
  simpa only [MonoidHom.coe_mk, OneHom.coe_mk] using
    intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 (M := N) γ.2

/-- The adjugate of a `Γ₀(N)` matrix again lies in `Δ₀(N)`: it is the image of `γ⁻¹`, which is
in `Γ₀(N)` because that is a subgroup. -/
lemma adjugateGL_mapGL_mem_Delta0 (γ : Gamma0 N) :
    (adjugateGL (mapGL ℚ (γ : SL(2, ℤ))) : GL (Fin 2) ℚ) ∈ Delta0 N := by
  rw [adjugateGL_mapGL]
  exact mapGL_mem_Delta0 N γ⁻¹

/-- **The adjugate half of the comparison.** On `Γ₀(N)` the upper-left unit of the *adjugate*
is `Gamma0Map` itself, not its inverse: the adjugate is the image of `γ⁻¹`, and
`Delta0UpperUnit_mapGL` inverts once more. Together the two pin down both faces of the
character. -/
-- This is the `@[simp]` half of the pair and `TauCeti.adjugateGL_mapGL` is not: that lemma's
-- left-hand side occurs inside this one's, so tagging both would leave this statement
-- non-normal. Do not add the tag there.
@[simp] lemma Delta0UpperUnit_adjugateGL_mapGL (γ : Gamma0 N) :
    Delta0UpperUnit N ⟨_, adjugateGL_mapGL_mem_Delta0 N γ⟩ = (Gamma0Map N).toHomUnits γ := by
  -- The first step replaces one `Delta0 N` element by another. They have *equal values* —
  -- that is `adjugateGL_mapGL` — but different membership proofs, and the proof component's
  -- type mentions the value, so rewriting the value alone leaves an ill-typed motive.
  -- `Subtype.ext` is the eliminator for exactly that: it discharges the pair from the value
  -- equality, membership in a `Submonoid` being a proposition. A bare `rw [adjugateGL_mapGL]`
  -- fails here for the motive reason, which is why the equality is supplied wholesale.
  rw [show (⟨_, adjugateGL_mapGL_mem_Delta0 N γ⟩ : Delta0 N)
      = ⟨_, mapGL_mem_Delta0 N γ⁻¹⟩ from Subtype.ext (adjugateGL_mapGL _),
    Delta0UpperUnit_mapGL, map_inv, inv_inv]

end HeckeRing.GL2
