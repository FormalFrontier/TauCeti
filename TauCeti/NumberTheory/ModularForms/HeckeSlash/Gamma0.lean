/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.ModularForm

/-!
# The Hecke operators of level `Γ₀(N)`

`HeckeSlash/ModularForm.lean` builds, for a subgroup `G ≤ SL(2, ℤ)` and a double coset of a Hecke
triple whose two flanks are `G.map (mapGL ℚ)`, the `ℂ`-linear endomorphisms of
`ModularForm (G.map (mapGL ℝ)) k` and `CuspForm (G.map (mapGL ℝ)) k` that the coset induces. This
file instantiates that at `G = Γ₀(N)` and `Δ = Δ₀(N)`, the companion of `HeckeSlash/Gamma1.lean`
at the larger group.

Both side conditions the general construction carries are discharged once, and neither is specific
to the level: the Hecke triple is `HeckeRing/GL2/Gamma0/Basic.lean`'s instance, which also supplies
the finiteness of the right-coset index, and the positivity hypothesis is
`out_mem_glpos_of_delta0` from that same file — every element of `Δ₀(N)` has positive determinant
by definition, so no double coset of this triple ever fails it.

The operators belong to the double coset itself, not to the representatives `heckeSlashSum` sums
over: `coe_heckeSlashGamma0ModularFormEnd` and `coe_heckeSlashGamma0CuspFormEnd` rewrite the
modular-form and cusp-form operator respectively to `heckeSlashSum`, and
`heckeSlashSum_coe_eq_sum_of_rightCosets` (`HeckeSlash/Independence.lean`) then evaluates that on
*any* decomposition of `Γ₀(N) δ Γ₀(N)` into right cosets.

⚠ These are the operators of an *arbitrary* double coset, and they carry **no character**.
`Γ₀(N)` is where the nebentypus lives, so the twisted operators — the ones weighted by
`χ ∘ Delta0UpperUnit`, acting on `modFormCharSpace k χ` rather than on all of
`M_k(Γ₀(N))` — are a different construction built on top of these. This file deliberately stops
short of that: it is the untwisted `Γ₀(N)` instantiation, matching `Gamma1.lean` declaration for
declaration.

⚠ Identifying particular cosets with the classical `Tₙ` is likewise a separate milestone and is
not proved here.

## Main definitions

* `HeckeRing.GL2.heckeSlashGamma0ModularFormEnd`: the operator on `M_k(Γ₀(N))`.
* `HeckeRing.GL2.heckeSlashGamma0CuspFormEnd`: the operator on `S_k(Γ₀(N))`.

## Main results

* `HeckeRing.GL2.coe_heckeSlashGamma0ModularFormEnd`,
  `HeckeRing.GL2.coe_heckeSlashGamma0CuspFormEnd`: both operators are `heckeSlashSum` on
  underlying functions.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4, Proposition 3.37, instantiated at `Γ₁ = Γ₂ = Γ₀(N)`.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- **The Hecke operator of a double coset on `M_k(Γ₀(N))`**: a `ℂ`-linear endomorphism of the
space of modular forms of level `Γ₀(N)` attached to an arbitrary double coset of the Hecke triple
`(Γ₀(N), Δ₀(N))`, with no condition relating `N` to the determinant of the coset. -/
noncomputable def heckeSlashGamma0ModularFormEnd :
    Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  heckeSlashModularFormEnd k D (out_mem_glpos_of_delta0 N D)

/-- **The Hecke operator of a double coset on `S_k(Γ₀(N))`** — the statement that the operator
above preserves cuspidality. -/
noncomputable def heckeSlashGamma0CuspFormEnd :
    Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  heckeSlashCuspFormEnd k D (out_mem_glpos_of_delta0 N D)

/-- The operator is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashGamma0ModularFormEnd (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma0ModularFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashModularFormEnd k D (out_mem_glpos_of_delta0 N D) f

/-- The operator is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashGamma0CuspFormEnd (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma0CuspFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashCuspFormEnd k D (out_mem_glpos_of_delta0 N D) f

end HeckeRing.GL2

end
