/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Invariance

/-!
# The twisted slash sum extended over the Hecke ring, on the character space

`Nebentypus/Invariance.lean` shows the twisted slash sum preserves `functionCharSpace` and
restricts each double coset to `twistedHeckeSlashSumCharEnd`. This file takes the `ℤ`-linear
extension of that assignment over the Hecke ring, exactly as `Nebentypus/Ring.lean` does for the
unrestricted operator.

It is a separate module from `Invariance.lean` because the topic is different — that file is about
preservation of the character space, this one is ring-level API — and it sits *below*
`Nebentypus/Composition.lean`, which imports it in order to state the basis-element identity that
consumes both this extension and its own composition theorem.

## Two carriers, neither a specialisation of the other

`twistedHeckeSlashRingLinearMap` (`Nebentypus/Ring.lean`) is the same `Finsupp.linearCombination`
extension of the same per-coset assignment, valued in `Module.End ℂ (ℍ → ℂ)`. The two are not
interchangeable: the composition results of `Nebentypus/Composition.lean` hold only on the
character space, so the carrier is what distinguishes them and neither restricts to the other by
a general principle.

## Main definitions

* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap`: the `ℤ`-linear extension of
  `twistedHeckeSlashSumCharEnd` over `𝕋 Δ₀(N) Γ₀(N) ℤ`, valued in
  `Module.End ℂ (functionCharSpace k χ)`.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_single`: the value on a basis element is the
  scaled twisted operator of that double coset. With `map_zero`/`map_add` this determines the map.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), whose
`twistedHeckeSumFunction` (line 842) is the extension below. The source states it over its own
`gamma0TwistedInvariantFunctionSubmodule`; this repository's name for that carrier is
`functionCharSpace`, and the double-coset indexing and the `HeckeCosetModule.single` spelling are
this repository's, not the source's. The statement shape follows `main`'s own untwisted
`heckeSlashGamma1RingModularFormLinearMap` (`HeckeSlash/Ring.lean`).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 (the action of the Hecke ring on automorphic forms).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

/-- The `ℤ`-linear extension of `twistedHeckeSlashSumCharEnd` to formal `ℤ`-combinations of double
cosets of `Γ₀(N)`, on the carrier the twisted sum preserves.

`twistedHeckeSlashRingLinearMap` (`Nebentypus/Ring.lean`) is the same extension on all of
`ℍ → ℂ`. The two are not interchangeable: the composition results of
`Nebentypus/Composition.lean` are available only on the character space, so the carrier is what
distinguishes them, and neither is a specialisation of the other.

`𝕋 Δ H ℤ` unfolds to `HeckeCoset Δ H H →₀ ℤ` carrying the transported module structure, which is
why `Finsupp.linearCombination` applies at this type. -/
noncomputable def twistedHeckeSlashRingCharLinearMap :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (functionCharSpace k χ) :=
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashSumCharEnd k χ D

/-- The value on a basis element is the scaled twisted operator of that double coset. -/
@[simp] lemma twistedHeckeSlashRingCharLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) (c : ℤ) :
    twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashSumCharEnd k χ D :=
  -- As in `twistedHeckeSlashRingLinearMap_single`: `Finsupp.linearCombination_single` does not
  -- apply, since `HeckeCosetModule.single` is a separate, non-exposed `def`.
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ twistedHeckeSlashSumCharEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

end HeckeRing.GL2

end
