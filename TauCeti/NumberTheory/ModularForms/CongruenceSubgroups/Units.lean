/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The diamond label of `Γ₀(N)` under reduction of the level

`CongruenceSubgroup.Gamma0Map` reads off the lower-right entry of a matrix of `Γ₀(N)` in
`ZMod N`, and `Gamma0Map_toHomUnits` is its unit-valued form. This file records the one fact
about that label which needs the reduction map `ZMod.unitsMap`: for `M ∣ N`, reading a matrix
of `Γ₀(N)` as a matrix of `Γ₀(M)` reduces its label along `(ZMod N)ˣ → (ZMod M)ˣ`.

It is a separate module from `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic`
because the statement is the only thing in the congruence-subgroup API that mentions
`ZMod.unitsMap`. Keeping it out of `Basic` keeps that foundational module from re-exporting
`Mathlib.Data.ZMod.Units` to its whole downstream cone.

## Main results

* `CongruenceSubgroup.Gamma0Map_toHomUnits_of_dvd`: for `M ∣ N`, the diamond label of a
  `Γ₀(N)` matrix read in `Γ₀(M)` is the reduction of its label at level `N`.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

/-- **The diamond label is compatible with reduction.** For `M ∣ N`, a matrix of `Γ₀(N)` read as
a matrix of `Γ₀(M)` has lower-right entry the reduction of its lower-right entry at level `N`,
so a nebentypus character pulls back along `(ZMod N)ˣ → (ZMod M)ˣ`.

The membership proof is an explicit argument rather than `Gamma0_le_Gamma0_of_dvd h γ.2`, so that
the left-hand side mentions `h` nowhere: both `M` and `N` are still fixed by the left-hand side,
which leaves `M ∣ N` as an ordinary side condition simp can discharge from context. Written the
other way the divisibility is reachable only inside a proof term, and the `@[simp]` rule is
inert. -/
@[simp]
lemma Gamma0Map_toHomUnits_of_dvd {M N : ℕ} (h : M ∣ N) (γ : ↥(Gamma0 N))
    (hγ : (γ : SL(2, ℤ)) ∈ Gamma0 M) :
    (Gamma0Map M).toHomUnits ⟨(γ : SL(2, ℤ)), hγ⟩ =
      ZMod.unitsMap h ((Gamma0Map N).toHomUnits γ) := by
  ext
  simp [Gamma0Map_apply, ZMod.unitsMap_def]

end CongruenceSubgroup
