/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.ModularForm

/-!
# The Hecke operators of level `Γ₁(N)`

`HeckeSlash/ModularForm.lean` builds, for a subgroup `G ≤ SL(2, ℤ)` and a double coset of a Hecke
triple whose two flanks are `G.map (mapGL ℚ)`, the `ℂ`-linear endomorphisms of
`ModularForm (G.map (mapGL ℝ)) k` and `CuspForm (G.map (mapGL ℝ)) k` that the coset induces. This
file instantiates that at `G = Γ₁(N)` and `Δ = Δ₀(N)` — the roadmap's Layer 2(b) setting — and
discharges, once, the two side conditions the general construction carries.

The Hecke triple itself is `HeckeRing/GL2/Gamma1.lean`'s instance, and the finiteness of the
right-coset index follows from it. What is left is the positivity hypothesis, and that is
`Δ₀(N) ≤ posDetInt 2` composed with `posDetInt_le_glpos`: every element of `Δ₀(N)` has positive
determinant by definition, so no double coset of this triple ever fails it.

⚠ These are the operators of an *arbitrary* double coset. Identifying particular cosets with the
classical `Tₙ` — the normalisation lemma for `Γ₁(N) · diag(1, p) · Γ₁(N)`, and the `q`-expansion
recurrences — is a separate milestone and is not proved here.

## Main definitions

* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd`: the operator on `M_k(Γ₁(N))`.
* `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd`: the operator on `S_k(Γ₁(N))`.

## Main results

* `HeckeRing.GL2.mem_glpos_out_of_delta0`: a double coset of `Δ₀(N)` has a representative of
  positive determinant.
* `HeckeRing.GL2.coe_heckeSlashGamma1ModularFormEnd`,
  `HeckeRing.GL2.coe_heckeSlashGamma1CuspFormEnd`: both operators are `heckeSlashSum` on
  underlying functions.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ}

/-- The chosen representative of a double coset of `Δ₀(N)` has positive determinant: `Δ₀(N)`
consists of integral matrices of positive determinant. This is the hypothesis
`heckeSlashModularFormEnd` carries, discharged once for this triple. -/
lemma mem_glpos_out_of_delta0 {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
    (D : HeckeCoset (Delta0 N) Γ₁ Γ₂) :
    (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ :=
  posDetInt_le_glpos 2 (Delta0_le_posDetInt N D.out.2)

variable [NeZero N] (k : ℤ)
  (D : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))

/-- **The Hecke operator of a double coset on `M_k(Γ₁(N))`.** This is the roadmap's Layer 2(b)
target for `ModularForm`: a `ℂ`-linear endomorphism of the space of modular forms of level
`Γ₁(N)` attached to an arbitrary double coset of the Hecke triple `(Γ₁(N), Δ₀(N))`, with no
condition relating `N` to the determinant of the coset. -/
noncomputable def heckeSlashGamma1ModularFormEnd :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeSlashModularFormEnd k D (mem_glpos_out_of_delta0 D)

/-- **The Hecke operator of a double coset on `S_k(Γ₁(N))`** — the statement that the operator
above preserves cuspidality. -/
noncomputable def heckeSlashGamma1CuspFormEnd :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeSlashCuspFormEnd k D (mem_glpos_out_of_delta0 D)

/-- The operator is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashGamma1ModularFormEnd (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma1ModularFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashModularFormEnd k D (mem_glpos_out_of_delta0 D) f

/-- The operator is `heckeSlashSum` on underlying functions. -/
@[simp] lemma coe_heckeSlashGamma1CuspFormEnd (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeSlashGamma1CuspFormEnd k D f) = heckeSlashSum k D f :=
  coe_heckeSlashCuspFormEnd k D (mem_glpos_out_of_delta0 D) f

end HeckeRing.GL2

end
