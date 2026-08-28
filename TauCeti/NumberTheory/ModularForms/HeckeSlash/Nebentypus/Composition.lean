/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Composition
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Invariance

/-!
# The composite of two nebentypus-twisted slash sums

`HeckeSlash/Composition.lean` computes the composite of two *unweighted* slash sums over the
representatives they are defined with, in `heckeSlashSum_slash` and
`heckeSlashSum_heckeSlashSum`, with no hypothesis on `f` at all. This file is the weighted
counterpart of those two, and it is the computational core of the multiplicativity that will make
the twisted assignment a *ring* homomorphism rather than merely `ℤ`-linear —
`HeckeSlash/Nebentypus/Ring.lean` flags that gap in as many words.

## Why the weights multiply, and why that is the whole point

`delta0NebentypusChar N χ` is a `MonoidHom` on `Δ₀(N)`, so the weight of a product of
representatives is the product of their weights. The composite of the two twisted sums is
therefore a sum over *products* `a_v b_w` weighted by the character of that product — exactly the
shape a single twisted sum over a third double coset has. Collapsing it onto such a sum is what
multiplicativity will be, and it is *not* proved here: it needs the twisted analogue of
`heckeSlashSum_eq_sum_of_rightCosets`, since changing representatives changes the weights
attached to them.

## Where the positivity hypothesis comes from

Unlike the unweighted statements, the weighted ones carry `0 < det x`: the weight has to pass
through the slash by `x`, which is `ModularForm.rat_smul_slash_of_det_pos`. No caller is
inconvenienced — the composite applies it at a `rightCosetRep`, whose determinant is positive
outright by `det_rightCosetRep_pos_of_delta0`.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSum_slash`: slashing a twisted sum multiplies the
  representatives on the right, the weights riding along unchanged.
* `HeckeRing.GL2.twistedHeckeSlashSum_twistedHeckeSlashSum`: the composite of two twisted sums, as
  a double sum over products of representatives weighted by the character of the product.

## Provenance

The weight-multiplication that `twistedHeckeSlashSum_twistedHeckeSlashSum` turns on is the content
of `delta0NebentypusWeight_mul_eq_tripleDelta` (line 478) in the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`). It is not
ported: with `Delta0UpperUnit` a `MonoidHom` — and hence `delta0NebentypusChar` one too — it is
`map_mul`, so it appears inline in the proof rather than as a declaration. That is the same
substitution which removed the source's `delta0UpperUnit_mul` and `delta0IntegralMatrix_mul` from
the invariance rung.

`twistedHeckeSlashSum_slash` has no counterpart in the source to adapt: it is the weighted
analogue of this repository's own `heckeSlashSum_slash`. AINTLIB reaches the same effect through
`twistedHeckeSlashGen_slash_distrib` (`:399`), which sits inside the adjugate-and-correction block
that the campaign routes around because this repository's substrate supersedes it.

⚠ What this file does **not** contain, so that the source line numbers are not read as a wider
claim: `twisted_weighted_slash_product_eq` (`:494`) is the per-pair step that carries a summand
into a *third* double coset, and it already assumes the twisted invariance of `f`; the payoff
`twistedHeckeSlashGen_comp` (`:801`) is the collapse onto a single twisted sum. Neither is proved
here. Both need the twisted analogue of `heckeSlashSum_eq_sum_of_rightCosets`, because changing
representatives changes the weights attached to them, and that is the next rung.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: the displayed computation preceding Proposition 3.37 is the composite below.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

-- The enumeration `∑` needs. `HeckeSlash/Composition.lean` does exactly this for the unweighted
-- sums, and it is what `Basic.lean`'s own `local instance` resolves to, so the `∑`s here and the
-- ones `twistedHeckeSlashSum_def` unfolds to are the same term. Declaring a bespoke instance
-- instead would need one per section, and the second would be auto-named with an underscore.
attribute [local instance] Fintype.ofFinite

section Chosen

variable (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- **Slashing a twisted slash sum multiplies the representatives on the right**, the weights
riding along unchanged. The weighted counterpart of `heckeSlashSum_slash`, which needs no
hypothesis at all; here `0 < det x` is what lets each weight pass through the slash by `x`. -/
theorem twistedHeckeSlashSum_slash (f : ℍ → ℂ) {x : GL (Fin 2) ℚ}
    (hx : 0 < (x : Matrix (Fin 2) (Fin 2) ℚ).det) :
    twistedHeckeSlashSum k χ D f ∣[k] x =
      ∑ v, (nebentypusWeight χ D v : ℂ) • (f ∣[k] (rightCosetRep D v * x)) := by
  rw [twistedHeckeSlashSum_def, SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [ModularForm.rat_smul_slash_of_det_pos k hx _ _,
    ← SlashAction.slash_mul k (rightCosetRep D v) x f]

end Chosen

section Composite

variable (D₁ D₂ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- **The composite of two twisted slash sums**, over the representatives they are defined with,
for an arbitrary `f : ℍ → ℂ`.

The weight on the summand at `(v, w)` is the character of the *product* `a_v b_w`, because
`delta0NebentypusChar` is a `MonoidHom` and the two weights therefore multiply. That is what makes
this a candidate for collapsing onto a single twisted sum over a third double coset; the collapse
itself needs twisted representative-independence and is not proved here. -/
theorem twistedHeckeSlashSum_twistedHeckeSlashSum (f : ℍ → ℂ) :
    twistedHeckeSlashSum k χ D₂ (twistedHeckeSlashSum k χ D₁ f) =
      ∑ v, ∑ w, (delta0NebentypusChar N χ
          ⟨rightCosetRep D₁ v * rightCosetRep D₂ w,
            mul_mem (rightCosetRep_mem_Delta0 D₁ v) (rightCosetRep_mem_Delta0 D₂ w)⟩ : ℂ) •
        (f ∣[k] (rightCosetRep D₁ v * rightCosetRep D₂ w)) := by
  rw [twistedHeckeSlashSum_def k χ D₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [twistedHeckeSlashSum_slash k χ D₁ f (det_rightCosetRep_pos_of_delta0 D₂ w),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- The two weights multiply because `delta0NebentypusChar` is a `MonoidHom` on `Δ₀(N)`, and
  -- `map_mul` needs its argument as a product of bundled elements rather than the single bundled
  -- product the statement carries. `MulMemClass.mk_mul_mk` is the submonoid API for that step; it
  -- holds by `rfl`, but naming it keeps the proof independent of how `Δ₀(N)`'s multiplication is
  -- built, which an inline `rfl` here would silently depend on.
  rw [smul_smul, nebentypusWeight_def, nebentypusWeight_def, ← MulMemClass.mk_mul_mk,
    map_mul, Units.val_mul, mul_comm]

end Composite

end HeckeRing.GL2

end
