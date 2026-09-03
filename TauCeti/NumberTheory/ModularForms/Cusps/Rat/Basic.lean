/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Rational matrices carry cusps to cusps

`IsCusp.smul` moves a cusp of `Γ` to a cusp of the conjugate `ConjAct.toConjAct g • Γ`, and for
a rational `g` that conjugate is again arithmetic (`Subgroup.IsArithmetic.conj`). Since every
arithmetic subgroup has the same cusps as `𝒮ℒ`
(`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`), the cusp transports straight back to `Γ`.

This is what the Hecke operators need. A rational representative need not lie in `Γ` at all, so
`IsCusp.smul_of_mem` does not apply to it, and the general `IsCusp.smul` only places the image
cusp in a *conjugate* subgroup. What repairs that is arithmeticity of the conjugate, as above;
nothing is asked of the determinant beyond invertibility.

## Main results

* `IsCusp.smul_map_ratCast`: if `c` is a cusp of an arithmetic `Γ` then so is `g • c`, for any
  `g : GL (Fin 2) ℚ` pushed forward to `ℝ`.

## Provenance

The need for this lemma, and its role as the cusp-stability step under a Hecke representative,
come from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, where it is packaged as `glMap_smul_isCusp_Gamma1`.

The **proof is not ported**: that declaration is specific to `Γ₁(N)`, whereas this one is stated
for an arbitrary arithmetic subgroup and is a three-line composition of mathlib's
`IsCusp.smul`, `Subgroup.IsArithmetic.conj` and
`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, none of which the source uses.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

/-- **Rational matrices carry cusps to cusps**: a `g : GL (Fin 2) ℚ`, pushed forward to `ℝ`,
sends a cusp of an arithmetic `Γ` to a cusp of `Γ`. -/
lemma IsCusp.smul_map_ratCast {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {c : OnePoint ℝ}
    (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g • c) Γ := by
  -- `algebraMap ℚ ℝ` and `Rat.castHom ℝ` are the same term (`DivisionRing.toRatAlgebra` defines
  -- the former as the latter), but the two spellings do not match syntactically, so the bridge
  -- is made explicit here rather than left to elaboration.
  rw [show (algebraMap ℚ ℝ) = (Rat.castHom ℝ) from rfl]
  have : (ConjAct.toConjAct (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g) • Γ).IsArithmetic :=
    Subgroup.IsArithmetic.conj Γ g
  exact Subgroup.IsArithmetic.isCusp_of_isCusp _ (hc.smul _)

end
