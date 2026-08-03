/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.ExteriorFiltration

/-!
# The degree quotients of a Clifford filtration

Mathlib's `CliffordAlgebra.equivExterior` identifies a Clifford algebra with its exterior-algebra
model when `2` is invertible. This file proves that the equivalence respects the degree filtration,
then transports the zero-form calculation of each successive quotient to an arbitrary quadratic
form.

This is the degree-quotient part of the Layer 0 `filtrationGradedEquiv` target in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean#L62-L68).
It does not construct the total associated-graded algebra or prove multiplication compatibility.

## Main definitions

* `TauCeti.CliffordAlgebra.equivExteriorFiltration`: `equivExterior` restricted to one filtration
  step.
* `TauCeti.CliffordAlgebra.filtrationGradedEquiv`: the corresponding degree-quotient equivalence
  with the exterior power.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The degree filtration".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- `equivExterior` maps every Clifford filtration step to the corresponding zero-form step. -/
theorem equivExterior_map_filtration (Q : QuadraticForm R M) [Invertible (2 : R)] (k : ℕ) :
    (filtration Q k).map (equivExterior Q).toLinearMap = filtration (0 : QuadraticForm R M) k :=
  changeFormEquiv_map_filtration Q changeForm.associated_neg_proof k

/-- `equivExterior` restricted to a Clifford filtration step. -/
noncomputable def equivExteriorFiltration (Q : QuadraticForm R M) [Invertible (2 : R)] (k : ℕ) :
    filtration Q k ≃ₗ[R] filtration (0 : QuadraticForm R M) k :=
  (equivExterior Q).ofSubmodules _ _ (equivExterior_map_filtration Q k)

/-- The restricted equivalence agrees with `equivExterior` after coercion from a filtration step. -/
@[simp]
theorem coe_equivExteriorFiltration_apply (Q : QuadraticForm R M) [Invertible (2 : R)] (k : ℕ)
    (x : filtration Q k) :
    (equivExteriorFiltration Q k x : CliffordAlgebra (0 : QuadraticForm R M)) = equivExterior Q x :=
  LinearEquiv.ofSubmodules_apply (equivExterior Q) (equivExterior_map_filtration Q k) x

private theorem equivExteriorFiltration_map_previous (Q : QuadraticForm R M) [Invertible (2 : R)]
    (k : ℕ) :
    (Submodule.comap (filtration Q (k + 1)).subtype (filtration Q k)).map
        (equivExteriorFiltration Q (k + 1)).toLinearMap =
      Submodule.comap (filtration (0 : QuadraticForm R M) (k + 1)).subtype
        (filtration (0 : QuadraticForm R M) k) := by
  ext x
  rw [Submodule.mem_map_equiv]
  -- The two submodules are over filtration subtypes, so expose their ambient carrier predicates.
  change (equivExterior Q).symm (x : CliffordAlgebra (0 : QuadraticForm R M)) ∈ filtration Q k ↔
    (x : CliffordAlgebra (0 : QuadraticForm R M)) ∈ filtration (0 : QuadraticForm R M) k
  rw [← equivExterior_map_filtration Q k, Submodule.mem_map_equiv]

private noncomputable def equivExteriorFiltrationQuotient (Q : QuadraticForm R M)
    [Invertible (2 : R)] (k : ℕ) :
    (filtration Q (k + 1) ⧸
      Submodule.comap (filtration Q (k + 1)).subtype (filtration Q k)) ≃ₗ[R]
      (filtration (0 : QuadraticForm R M) (k + 1) ⧸
        Submodule.comap (filtration (0 : QuadraticForm R M) (k + 1)).subtype
          (filtration (0 : QuadraticForm R M) k)) :=
  Submodule.Quotient.equiv _ _ (equivExteriorFiltration Q (k + 1))
    (equivExteriorFiltration_map_previous Q k)

/-- The successive degree quotient of a Clifford algebra is the corresponding exterior power. -/
noncomputable def filtrationGradedEquiv (Q : QuadraticForm R M) [Invertible (2 : R)] (k : ℕ) :
    (filtration Q (k + 1) ⧸
      Submodule.comap (filtration Q (k + 1)).subtype (filtration Q k)) ≃ₗ[R] ⋀[R]^(k + 1) M :=
  (equivExteriorFiltrationQuotient Q k).trans (zeroFormFiltrationQuotientEquivExteriorPower k)

/-- On quotient representatives, `filtrationGradedEquiv` first applies `equivExterior`. -/
@[simp]
theorem filtrationGradedEquiv_apply_mk (Q : QuadraticForm R M) [Invertible (2 : R)] (k : ℕ)
    (x : filtration Q (k + 1)) :
    filtrationGradedEquiv Q k (Submodule.Quotient.mk x) =
      zeroFormFiltrationQuotientEquivExteriorPower k
        (Submodule.Quotient.mk (equivExteriorFiltration Q (k + 1) x)) := by
  rw [filtrationGradedEquiv, equivExteriorFiltrationQuotient]
  rfl

end CliffordAlgebra

end TauCeti
