/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1

/-!
# The `ℤ`-linear extension of the Hecke slash operators to the Hecke ring

`heckeSlashGamma1ModularFormEnd` attaches a `ℂ`-linear endomorphism of `M_k(Γ₁(N))` to a
single double coset. This file extends that assignment `ℤ`-linearly over the basis of the
Hecke ring `𝕋 Δ₀(N) Γ₁(N) ℤ`, assigning an endomorphism of `M_k(Γ₁(N))` to each ring element.

This is **not** yet a ring action: multiplicativity is Shimura §3.4 and is not proved here,
and the value on `1` is recorded only as the operator of the identity double coset, not as
the identity endomorphism. What is delivered is the `ℤ`-linear assignment.

The extension is `Finsupp.linearCombination` at the coefficient ring `ℤ`, so linearity in the
ring element is inherited rather than reproved — `map_zero` and `map_add` apply directly. The
one lemma proved here is the one specific to this setting: the value on a basis element.

## Main definitions

* `heckeSlashGamma1RingModularFormLinearMap`: the `ℤ`-linear extension of
  `heckeSlashGamma1ModularFormEnd` to the Hecke ring.

## Main results

* `heckeSlashGamma1RingModularFormLinearMap_single`: the value on a basis element is the
  scaled operator of that double coset. Together with `map_zero`/`map_add` and
  `HeckeCosetModule.one_def` this determines the map, so no further computation rules are
  restated here.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 (the action of the Hecke ring on automorphic forms).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule

namespace HeckeRing.GL2

public section

variable {N : ℕ} [NeZero N] (k : ℤ)

/-- The `ℤ`-linear extension of `heckeSlashGamma1ModularFormEnd` to formal `ℤ`-combinations of
double cosets: `ℤ`-linear in the ring element, but not known to be multiplicative, so this is
not yet a ring action.

`𝕋 Δ H ℤ` unfolds to `HeckeCoset Δ H H →₀ ℤ` carrying the transported module structure, which
is why `Finsupp.linearCombination` applies at this type: the ascription below crosses the
`HeckeCosetModule` wrapper. -/
noncomputable def heckeSlashGamma1RingModularFormLinearMap :
    𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ →ₗ[ℤ]
      Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Finsupp.linearCombination ℤ (heckeSlashGamma1ModularFormEnd k)

/-- The value on a basis element is the scaled operator of that double coset. -/
@[simp] lemma heckeSlashGamma1RingModularFormLinearMap_single
    (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
    (c : ℤ) :
    heckeSlashGamma1RingModularFormLinearMap (N := N) k (HeckeCosetModule.single ℤ D c) =
      c • heckeSlashGamma1ModularFormEnd k D :=
  -- `Finsupp.linearCombination_apply` names the step to the `Finsupp.sum` shape, rather than
  -- leaving it to delta-unfolding of `linearCombination`; the side goal is then explicit.
  -- `Finsupp.linearCombination_single` does NOT apply here: `HeckeCosetModule.single` is a
  -- separate, non-exposed `def`, so that lemma's left-hand side does not match — which is why
  -- the wrapper `HeckeCosetModule.sum_single_index` exists.
  (Finsupp.linearCombination_apply (R := ℤ) (v := heckeSlashGamma1ModularFormEnd k) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

end

end HeckeRing.GL2
