/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic

-- Proof-only: the zero set's codiscreteness comes from
-- `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`, which Mathlib declares in its order module.
-- The statement below mentions no order, so this import is not public.
import Mathlib.Analysis.Analytic.Order

/-!
# The zero set of an analytic function

An analytic function that does not vanish identically has isolated zeros, and this file records
what that gives on a compact set: only finitely many zeros lie there. It is the fact any zero
count rests on, and it mentions neither the analytic order nor any particular field, so it lives
apart from both the order calculus of `TauCeti.Analysis.Analytic.Order` and the complex-specific
estimates of `TauCeti.Analysis.Complex.IsolatedZero`. The name follows Mathlib's own
`Mathlib.Analysis.Analytic.IsolatedZeros`, where the identity principle and the codiscreteness of
the zero set live.

## Main declarations

* `TauCeti.finite_setOf_mem_and_eq_zero_of_isCompact`: an analytic function somewhere nonzero on
  a preconnected set has finitely many zeros in any compact subset of it.

## References

* The AINTLIB `LeanModularForms` valence-formula development
  (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`), whose modular-form-specific
  finiteness this generalises.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **An analytic function somewhere nonzero has finitely many zeros in a compact.** If `f` is
analytic on a neighbourhood of a preconnected set `U` and nonzero at some point of `U`, then
every compact subset of `U` contains only finitely many zeros of `f`.

Generalized from the modular-form-specific finiteness of the AINTLIB `LeanModularForms`
valence-formula development (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`) to
arbitrary analytic functions on a preconnected set. -/
theorem finite_setOf_mem_and_eq_zero_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {U K : Set 𝕜} {x : 𝕜}
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (hx : x ∈ U) (hgx : g x ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) : {z ∈ K | g z = 0}.Finite := by
  have hcod : g ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono hKU
      (hg.preimage_zero_mem_codiscreteWithin hgx hx ⟨⟨x, hx⟩, hU⟩)
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcod).subset fun z hz =>
    ⟨hz.1, by simpa using hz.2⟩

end TauCeti

end
