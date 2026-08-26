/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Rank is additive along a tower of submodules

For submodules `p ≤ q ≤ r` of a module `M`, the relative quotient `r / p` is filtered by `q / p`,
and `TauCeti.rank_quotient_submoduleOf_tower` records that its rank is the sum of the ranks of the
two steps.  Relative quotients are spelled with `Submodule.submoduleOf`, so that `q / p` means
`↥q ⧸ p.submoduleOf q`.

The proof is Noether's third isomorphism theorem (`Submodule.quotientQuotientEquivQuotient`)
together with rank–nullity, which is why the base ring is asked only for `HasRankNullity`.
-/

public section

universe u v

namespace TauCeti

/-- Rank is additive along a tower `p ≤ q ≤ r` of submodules: the relative quotients of the two
steps add up to the relative quotient of the composite.  This is Noether's third isomorphism
theorem together with rank–nullity. -/
theorem rank_quotient_submoduleOf_tower {R : Type v} {M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] [HasRankNullity.{u} R] {p q r : Submodule R M} (hpq : p ≤ q) (hqr : q ≤ r) :
    Module.rank R (↥r ⧸ p.submoduleOf r) =
      Module.rank R (↥q ⧸ p.submoduleOf q) + Module.rank R (↥r ⧸ q.submoduleOf r) := by
  have hAB : p.submoduleOf r ≤ q.submoduleOf r := Submodule.comap_mono hpq
  set A := p.submoduleOf r with hA
  set f : ↥q →ₗ[R] (↥r ⧸ A) := A.mkQ ∘ₗ Submodule.inclusion hqr with hf
  have hker : LinearMap.ker f = p.submoduleOf q := by
    ext z
    simp [hf, hA, Submodule.submoduleOf, Submodule.inclusion]
  have hrange : LinearMap.range f = (q.submoduleOf r).map A.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_inclusion]
    rfl
  have e₁ : (↥q ⧸ p.submoduleOf q) ≃ₗ[R] ↥((q.submoduleOf r).map A.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((f.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ hrange))
  have e₂ : ((↥r ⧸ A) ⧸ (q.submoduleOf r).map A.mkQ) ≃ₗ[R] (↥r ⧸ q.submoduleOf r) :=
    Submodule.quotientQuotientEquivQuotient A (q.submoduleOf r) hAB
  have key := Submodule.rank_quotient_add_rank ((q.submoduleOf r).map A.mkQ)
  rw [e₂.rank_eq, ← e₁.rank_eq] at key
  rw [← key, add_comm]

end TauCeti
