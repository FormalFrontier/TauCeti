/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Addition
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order

/-!
# Effective monotonicity of complete linear systems

This file records the elementary monotonicity calculus for complete linear systems of Weil
divisors. If `D ≤ D'` coefficientwise, then adding the effective difference `D' - D` sends
`|D|` into `|D'|`; in particular nonemptiness of complete linear systems is monotone under
the divisor order.

This is the divisor-level bookkeeping behind the later symmetric-power and Abel-map lane in
the Jacobian roadmap: increasing an effective divisor by fixed effective base conditions
should not destroy the existence of effective representatives.  It advances
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve" and "Degree", as
a clean prerequisite for the Layer C/D Abel-map construction from symmetric powers.  No
external mathematics is vendored; the proofs reuse Tau Ceti's existing complete-linear-system
addition API and the coefficientwise order on formal Weil divisors.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-! ### Monotonicity for the divisor order -/

/-- If `D ≤ D'`, then translating a member of `|D|` by the effective difference `D' - D`
gives a member of `|D'|`. -/
lemma add_sub_mem_completeLinearSystem_of_le {D D' E : WeilDivisor X} (hDD' : D ≤ D')
    (hE : E ∈ S.completeLinearSystem D) :
    E + (D' - D) ∈ S.completeLinearSystem D' := by
  have hdiff : IsEffective (D' - D) := le_iff_isEffective_sub.mp hDD'
  have hmem : E + (D' - D) ∈ S.completeLinearSystem (D + (D' - D)) :=
    S.add_effective_mem_completeLinearSystem hdiff hE
  rwa [add_sub_cancel] at hmem

/-- The order-induced translation map sends `|D|` into `|D'|` whenever `D ≤ D'`. -/
lemma mapsTo_add_sub_completeLinearSystem_of_le {D D' : WeilDivisor X} (hDD' : D ≤ D') :
    Set.MapsTo (fun E => E + (D' - D)) (S.completeLinearSystem D)
      (S.completeLinearSystem D') :=
  fun _ hE => S.add_sub_mem_completeLinearSystem_of_le hDD' hE

/-- Nonemptiness of complete linear systems is monotone for the divisor order. -/
lemma nonempty_completeLinearSystem_of_le {D D' : WeilDivisor X} (hDD' : D ≤ D')
    (hD : (S.completeLinearSystem D).Nonempty) : (S.completeLinearSystem D').Nonempty := by
  have hdiff : IsEffective (D' - D) := le_iff_isEffective_sub.mp hDD'
  have hnonempty : (S.completeLinearSystem (D + (D' - D))).Nonempty :=
    S.nonempty_completeLinearSystem_add_effective hdiff hD
  rwa [add_sub_cancel] at hnonempty

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
