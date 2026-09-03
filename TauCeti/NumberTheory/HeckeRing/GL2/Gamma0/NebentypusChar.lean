/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperUnit
public import Mathlib.Data.Complex.Basic

/-!
# The twisting character of the `χ`-twisted `Γ₀(N)` Hecke ring

`Delta0UpperUnit` sends an element of `Δ₀(N)` to the unit its integral witness has in the
upper-left corner mod `N`. Composing with a Dirichlet character `χ : (ZMod N)ˣ →* ℂˣ` gives

```
delta0NebentypusChar χ : Δ₀(N) →* ℂˣ
```

the coefficient the `χ`-twisted double-coset operator attaches to a monoid element.

It is **not** an extension of the nebentypus along `Γ₀(N) → Δ₀(N)`, and the direction matters:
`delta0NebentypusChar_mapGL` records that on `Γ₀(N)` it restricts to the *inverse* of
`χ ∘ Gamma0Map`, the character `modFormCharSpace` is defined by. That is the convention rather
than an accident — the twisted operator *divides* by the character, each representative
contributing `χ(·)⁻¹ • (f ∣[k] ·)`, so the value attached to a monoid element is the reciprocal
of the one attached to a group element acting on forms. It is inherited directly from
`Delta0UpperUnit_mapGL`, where the inverse first appears.

## Main definitions

* `HeckeRing.GL2.delta0NebentypusChar`: the twisting character `Δ₀(N) →* ℂˣ`.

## Main results

* `HeckeRing.GL2.delta0NebentypusChar_apply`: the defining equation, `@[simp]`. It is the only
  route to that equation from outside this file: the definition's body is not exposed, so
  downstream neither `rfl`, `unfold`, `simp [delta0NebentypusChar]` nor `MonoidHom.comp_apply`
  can recover it — but plain `simp` does, *through this lemma*.
* `HeckeRing.GL2.delta0NebentypusChar_mapGL`: on `Γ₀(N)` it is inverse to `χ ∘ Gamma0Map`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5 (Hecke operators with nebentypus).
* Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`](https://github.com/CBirkbeck/AINTLIB) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, declaration
  `delta0NebentypusDeltaChar`. The source builds the character as a bare `MonoidHom` with
  `map_one'`/`map_mul'` discharged by hand from its `Classical.choose` witness API; here those
  obligations are already carried by `Delta0UpperUnit`, so the character is a composition.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **The twisting character of the `χ`-twisted `Γ₀(N)` Hecke ring**: `χ` of the upper-left
unit of an integral witness. Multiplicativity is inherited from `Delta0UpperUnit`, which is
already a `MonoidHom`, so no hypothesis is needed on `χ` beyond being one. -/
noncomputable def delta0NebentypusChar (χ : (ZMod N)ˣ →* ℂˣ) : Delta0 N →* ℂˣ :=
  χ.comp (Delta0UpperUnit N)

-- Why this lemma exists at all, and why the proof is written `(rfl)`: the definition sits in a
-- `public section` without `@[expose]`, so its body is sealed to any module that exports a
-- theorem — which is every module here. Downstream, `rfl`, `unfold` and
-- `simp [delta0NebentypusChar]` all fail (the last with "Expected a definition with an exposed
-- body"), and `MonoidHom.comp_apply` finds no occurrence to rewrite, so this is the only route
-- to the equation from outside the file. Inside the defining module the body is visible, and the
-- parenthesised `(rfl)` elaborates against it where a bare `rfl` would export the defeq and be
-- refused.
/-- **The defining equation**: the twisting character is `χ` of the upper-left unit. -/
@[simp] lemma delta0NebentypusChar_apply (χ : (ZMod N)ˣ →* ℂˣ) (g : Delta0 N) :
    delta0NebentypusChar N χ g = χ (Delta0UpperUnit N g) := (rfl)

-- Deliberately not `@[simp]`, and it does not need to be: with `delta0NebentypusChar_apply`
-- tagged, `simp` reaches this statement on its own through the already-`@[simp]`
-- `Delta0UpperUnit_mapGL` and `map_inv`. Measured — tagging both makes `simpNF` report
-- "simp can prove this" on this lemma. It is kept as the named specialization because that is
-- the form the twisted Hecke ring cites.
/-- **On `Γ₀(N)` the twisting character is inverse to the nebentypus.** `Delta0UpperUnit`
restricts to the inverse of `Gamma0Map` there, because `ad ≡ 1`; applying `χ` carries the
inverse across. Reading this character as an extension of the nebentypus and dropping the
inverse would negate every twist downstream. -/
lemma delta0NebentypusChar_mapGL (χ : (ZMod N)ˣ →* ℂˣ) (γ : Gamma0 N) :
    delta0NebentypusChar N χ ⟨_, mapGL_mem_Delta0 N γ⟩ =
      (χ ((Gamma0Map N).toHomUnits γ))⁻¹ := by
  rw [delta0NebentypusChar_apply, Delta0UpperUnit_mapGL, map_inv]

end HeckeRing.GL2
