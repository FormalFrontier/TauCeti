/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.LeastGreatest
public import TauCeti.FieldTheory.FunctionField.Differential.Weil
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty

/-!
# The divisor of a Weil differential

A nonzero Weil differential `ω` of an algebraic function field `F / k` with exact constant field
is bounded by many divisors, and among them there is a largest one: there is a divisor `(ω)` with

`ω ∈ Ω_F(D) ↔ D ≤ (ω)`.

This file constructs `(ω)` and proves that characterization.  It is Stichtenoth, *Algebraic
Function Fields and Codes*, 2nd ed., Lemma 1.5.10 and Definition 1.5.11, together with the first
half of Proposition 1.5.13, the translation rule `(x · ω) = div x + (ω)`.

Two facts drive the construction.  Degrees are bounded on the divisors bounding `ω`, because a
divisor `D` with `A_F(D) + F = A_F` bounds no nonzero Weil differential at all, and every divisor
of large enough degree is of that kind by Riemann's theorem.  And the divisors bounding `ω` are
closed under the pointwise maximum, by `TauCeti.weilDifferentialFiltration_sup`.  A divisor of
maximal degree among them is therefore the largest of them, because a strictly larger divisor of
a function field has a strictly larger degree.

## Main definitions

* `TauCeti.Divisor.ofWeilDifferential`: the divisor `(ω)` of a Weil differential (Stichtenoth,
  Definition 1.5.11), the greatest divisor bounding it, with the junk value `0` when there is
  none — that is, for `ω = 0` and for the linear forms that are not Weil differentials.

## Main results

* `TauCeti.exists_isGreatest_setOf_mem_weilDifferentialFiltration`: **Stichtenoth, Lemma 1.5.10**,
  the existence of a greatest divisor bounding a nonzero Weil differential.
* `TauCeti.mem_weilDifferentialFiltration_iff_le_ofWeilDifferential`: the characterization
  `ω ∈ Ω_F(D) ↔ D ≤ (ω)`.
* `TauCeti.Divisor.ofWeilDifferential_repartitionDualMul`: **Stichtenoth, Proposition 1.5.13**,
  first half — `(x · ω) = (ω) + div x` for a nonzero function `x`.
* `TauCeti.mem_riemannRochSpace_ofWeilDifferential_sub_iff`: `x ∈ L((ω) - D)` exactly when
  `x · ω ∈ Ω_F(D)`, the elementwise form of the map of Stichtenoth's Duality Theorem 1.5.14.

The complementary halves of Propositions 1.5.13 and 1.5.14 — that any two canonical divisors are
linearly equivalent, and that `x ↦ x · ω` is onto `Ω_F(D)` — are exactly the statements that need
`dim_F Ω_F = 1` (Proposition 1.5.9), and are not proved here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 (Lemma 1.5.10, Definition 1.5.11, Proposition 1.5.13).
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  {ω : Module.Dual k ↥(repartitionSpace k F)}

/-! ### The divisors bounding a nonzero Weil differential -/

/-- **The divisors bounding a nonzero Weil differential have bounded degree** (Stichtenoth, in the
proof of Lemma 1.5.10).  A divisor `D` bounding a nonzero Weil differential has
`A_F(D) + F ≠ A_F`, so it is special; and by Riemann's theorem every divisor of large enough
degree is nonspecial. -/
theorem exists_forall_degree_le_of_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k F, ω ∈ weilDifferentialFiltration D → Divisor.degree D ≤ c := by
  obtain ⟨c, hc⟩ := exists_forall_indexOfSpecialty_eq_zero hF hex
  refine ⟨c, fun D hD ↦ not_lt.mp fun hlt ↦ hω ?_⟩
  have hbot : weilDifferentialFiltration D = ⊥ :=
    (weilDifferentialFiltration_eq_bot_iff hF D).mpr
      ((adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff hF hex D).mpr
        (hc D hlt.le))
  rwa [hbot, Submodule.mem_bot] at hD

/-- **Stichtenoth, Lemma 1.5.10**: among the divisors bounding a nonzero Weil differential there
is a greatest one.  The set is nonempty by the definition of a Weil differential, closed under the
pointwise maximum by `TauCeti.weilDifferentialFiltration_sup`, and of bounded degree; a member of
maximal degree is therefore its greatest element. -/
theorem exists_isGreatest_setOf_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    ∃ W : Divisor k F, IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W := by
  obtain ⟨c, hc⟩ := exists_forall_degree_le_of_mem_weilDifferentialFiltration hF hex hω
  obtain ⟨D₀, hD₀⟩ := mem_weilDifferentialSpace_iff.mp hωΩ
  -- pick a divisor `W` bounding `ω` of maximal degree among those bounding `ω`
  obtain ⟨n, ⟨W, hW, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n ↦ ∃ D : Divisor k F, ω ∈ weilDifferentialFiltration D ∧ Divisor.degree D = n)
    ⟨c, by rintro n ⟨D, hD, rfl⟩; exact hc D hD⟩ ⟨_, D₀, hD₀, rfl⟩
  refine ⟨W, hW, fun B hB ↦ ?_⟩
  have hsup : ω ∈ weilDifferentialFiltration (W ⊔ B) := by
    rw [weilDifferentialFiltration_sup]
    exact Submodule.mem_inf.mpr ⟨hW, hB⟩
  have heq : W = W ⊔ B :=
    Divisor.eq_of_le_of_degree_eq hF le_sup_left
      (le_antisymm (Divisor.degree_le_of_le le_sup_left) (hmax _ ⟨W ⊔ B, hsup, rfl⟩))
  exact le_sup_right.trans heq.ge

/-! ### The divisor of a Weil differential -/

open scoped Classical in
/-- **The divisor `(ω)` of a Weil differential** (Stichtenoth, Definition 1.5.11): the greatest
divisor `D` with `ω ∈ Ω_F(D)`.

For a nonzero Weil differential of a function field with exact constant field such a divisor
exists, by `TauCeti.exists_isGreatest_setOf_mem_weilDifferentialFiltration`, and
`TauCeti.mem_weilDifferentialFiltration_iff_le_ofWeilDifferential` is the resulting
characterization.  Otherwise — for `ω = 0`, which every divisor bounds, and for a linear form no
divisor bounds — this is the junk value `0`. -/
noncomputable def Divisor.ofWeilDifferential (ω : Module.Dual k ↥(repartitionSpace k F)) :
    Divisor k F :=
  if h : ∃ W : Divisor k F, IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W then
    h.choose
  else 0

/-- The divisor of a Weil differential is *the* greatest divisor bounding it: exhibiting one such
greatest divisor identifies it, with no further hypotheses. -/
theorem Divisor.ofWeilDifferential_eq_of_isGreatest {W : Divisor k F}
    (h : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) :
    Divisor.ofWeilDifferential ω = W := by
  have hgr : ∃ W : Divisor k F,
      IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W := ⟨W, h⟩
  rw [Divisor.ofWeilDifferential, dite_eq_left_of_eq_true (eq_true hgr)]
  exact hgr.choose_spec.unique h

/-- **Stichtenoth, Lemma 1.5.10**, in terms of `TauCeti.Divisor.ofWeilDifferential`: `(ω)` is the
greatest divisor bounding a nonzero Weil differential `ω`. -/
theorem isGreatest_ofWeilDifferential (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D}
      (Divisor.ofWeilDifferential ω) := by
  obtain ⟨W, hW⟩ := exists_isGreatest_setOf_mem_weilDifferentialFiltration hF hex hωΩ hω
  rw [Divisor.ofWeilDifferential_eq_of_isGreatest hW]
  exact hW

/-- A nonzero Weil differential is bounded by its own divisor. -/
theorem mem_weilDifferentialFiltration_ofWeilDifferential (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    ω ∈ weilDifferentialFiltration (Divisor.ofWeilDifferential ω) :=
  (isGreatest_ofWeilDifferential hF hex hωΩ hω).1

/-- **The characterization of the divisor of a Weil differential**: a divisor bounds a nonzero
Weil differential exactly when it is at most the divisor of that differential. -/
theorem mem_weilDifferentialFiltration_iff_le_ofWeilDifferential
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) (D : Divisor k F) :
    ω ∈ weilDifferentialFiltration D ↔ D ≤ Divisor.ofWeilDifferential ω :=
  ⟨fun hD ↦ (isGreatest_ofWeilDifferential hF hex hωΩ hω).2 hD, fun hD ↦
    weilDifferentialFiltration_antitone hD
      (mem_weilDifferentialFiltration_ofWeilDifferential hF hex hωΩ hω)⟩

/-! ### Multiplication by a function -/

/-- **Stichtenoth, Proposition 1.5.13**, first half: multiplying a nonzero Weil differential by a
nonzero function translates its divisor by the principal divisor of that function,
`(x · ω) = (ω) + div x`.  So the divisors of the nonzero multiples of `ω` form one full linear
equivalence class. -/
theorem Divisor.ofWeilDifferential_repartitionDualMul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0)
    (z : Fˣ) :
    Divisor.ofWeilDifferential (repartitionDualMul hF (z : F) ω) =
      Divisor.ofWeilDifferential ω + Divisor.principal hF z := by
  refine Divisor.ofWeilDifferential_eq_of_isGreatest
    ⟨(repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mpr
      (mem_weilDifferentialFiltration_ofWeilDifferential hF hex hωΩ hω),
    fun D hD ↦ sub_le_iff_le_add.mp ?_⟩
  refine (mem_weilDifferentialFiltration_iff_le_ofWeilDifferential hF hex hωΩ hω _).mp
    ((repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mp ?_)
  rwa [sub_add_cancel]

/-- **The elementwise Duality map** (Stichtenoth, in the proof of Theorem 1.5.14): a nonzero
function lies in `L((ω) - D)` exactly when multiplying `ω` by it gives a Weil differential bounded
by `D`.  The remaining content of the Duality Theorem is that `x ↦ x · ω` is onto `Ω_F(D)`, which
needs the one-dimensionality of `Ω_F` over `F`. -/
theorem mem_riemannRochSpace_ofWeilDifferential_sub_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hωΩ : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0)
    (z : Fˣ) (D : Divisor k F) :
    (z : F) ∈ riemannRochSpace (Divisor.ofWeilDifferential ω - D) ↔
      repartitionDualMul hF (z : F) ω ∈ weilDifferentialFiltration D := by
  have hrearrange : Divisor.principal hF z + (Divisor.ofWeilDifferential ω - D) =
      Divisor.ofWeilDifferential ω + Divisor.principal hF z - D := by abel
  rw [mem_riemannRochSpace_units_iff hF,
    mem_weilDifferentialFiltration_iff_le_ofWeilDifferential hF hex
      (repartitionDualMul_mem_weilDifferentialSpace hF (z : F) hωΩ)
      (repartitionDualMul_ne_zero hF z hω) D,
    Divisor.ofWeilDifferential_repartitionDualMul hF hex hωΩ hω z, hrearrange, sub_nonneg]

end TauCeti
