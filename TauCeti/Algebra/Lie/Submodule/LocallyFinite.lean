/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.RingTheory.Finiteness.Bilinear

/-!
# Locally nilpotent and locally finite vectors of a Lie module

Let `L` be a Lie algebra over a commutative ring `R` and let `M` be an `L`-module. Two
finiteness conditions on a vector of `M` are collected here, both of them conditions that hold on a
Lie submodule and are therefore either vacuous or universal on an irreducible module.

* `x : L` acts **locally nilpotently** at `m` when `x^k` annihilates `m` for some `k`. The set of
  such `m` is the generalized `0`-eigenspace of the action of `x`, and it is a Lie submodule as
  soon as `ad x` acts locally nilpotently on `L`: this is Mathlib's
  `LieModule.lie_mem_maxGenEigenspace_toEnd` at the eigenvalue `0 + 0`.
* A set `S ⊆ L` acts **locally finitely** at `m` when `m` lies in a finitely generated
  `R`-submodule of `M` stable under bracketing with every element of `S`. The set of such `m` is a
  Lie submodule whenever `L` itself is a finite `R`-module: if `N` is finitely generated and
  `S`-stable then so is `N + ⁅L, N⁆`, and the latter contains `⁅y, m⁆` for every `y : L`.

Both statements are the mechanism behind an "integrability" argument: an irreducible module
containing a *single* vector with the finiteness property has the property everywhere. The
motivating instance is the highest weight vector of an irreducible highest weight module, which is
annihilated by a power of each simple root vector; see
`TauCeti/Algebra/Lie/HighestWeight/Integrable.lean`.

## Main definitions

* `TauCeti.locallyNilpotentSubmodule`: the vectors annihilated by a power of a fixed element whose
  adjoint action is locally nilpotent, as a Lie submodule.
* `TauCeti.locallyFiniteSubmodule`: the vectors lying in a finitely generated subspace stable under
  a fixed set of elements, as a Lie submodule.

## Main results

* `TauCeti.exists_pow_toEnd_eq_zero_of_isIrreducible`: on an irreducible module, an element whose
  adjoint action is locally nilpotent and which is locally nilpotent at one nonzero vector is
  locally nilpotent everywhere.
* `TauCeti.locallyFiniteSubmodule_span`: only the span of `S` matters, so the condition may be
  stated against a generating set and consumed against the subalgebra it generates.
* `TauCeti.locallyFiniteSubmodule_eq_top_of_isIrreducible`: on an irreducible module, a set that
  acts locally finitely at one nonzero vector acts locally finitely everywhere.

## Implementation notes

The underlying subspace of `TauCeti.locallyNilpotentSubmodule` is Mathlib's
`Module.End.maxGenEigenspace` of the action of `x` at the eigenvalue `0`, which Mathlib itself
promotes to a Lie submodule only as `LieModule.genWeightSpaceOf`, under the hypothesis that `L` is
a *nilpotent* Lie algebra. That hypothesis fails for the semisimple Lie algebras this file is
written for, and the local nilpotence of `ad x` replaces it: it is what makes every element of `L`
lie in the generalized `0`-eigenspace of `ad x`, which is all the argument of `genWeightSpaceOf`
ever uses.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., §3.6.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-! ### Locally nilpotent vectors -/

variable (R M) in
/-- The vectors of `M` annihilated by some power of the action of `x`, as a Lie submodule.

The underlying subspace is the generalized `0`-eigenspace of `x` acting on `M`; it is stable under
all of `L` because `ad x` is assumed locally nilpotent, so that every element of `L` lies in the
generalized `0`-eigenspace of `ad x`. -/
def locallyNilpotentSubmodule (x : L)
    (hx : ∀ y : L, ∃ k : ℕ, ((ad R L x) ^ k) y = 0) : LieSubmodule R L M where
  __ := (toEnd R L M x).maxGenEigenspace 0
  lie_mem {y m} hm := by
    have hy : y ∈ (ad R L x).maxGenEigenspace 0 := by
      simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
      exact hx y
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid] at hm ⊢
    rw [← zero_add (0 : R)]
    exact LieModule.lie_mem_maxGenEigenspace_toEnd hy hm

@[simp]
theorem mem_locallyNilpotentSubmodule {x : L}
    {hx : ∀ y : L, ∃ k : ℕ, ((ad R L x) ^ k) y = 0} {m : M} :
    m ∈ locallyNilpotentSubmodule R M x hx ↔ ∃ k : ℕ, ((toEnd R L M x) ^ k) m = 0 := by
  -- The constructor has no named lemma for its inherited carrier, so expose the definitionally
  -- equal generalized eigenspace before applying its membership simp lemma.
  change m ∈ (toEnd R L M x).maxGenEigenspace 0 ↔ _
  simp

/-- **Local nilpotence spreads over an irreducible module.** If `ad x` is locally nilpotent and
some nonzero vector of an irreducible module `M` is annihilated by a power of `x`, then every
vector of `M` is. -/
theorem exists_pow_toEnd_eq_zero_of_isIrreducible [LieModule.IsIrreducible R L M] {x : L}
    (hx : ∀ y : L, ∃ k : ℕ, ((ad R L x) ^ k) y = 0) {m₀ : M} (hm₀ : m₀ ≠ 0) {k₀ : ℕ}
    (hk₀ : ((toEnd R L M x) ^ k₀) m₀ = 0) (m : M) :
    ∃ k : ℕ, ((toEnd R L M x) ^ k) m = 0 := by
  have : Nontrivial (locallyNilpotentSubmodule R M x hx) :=
    nontrivial_of_ne ⟨m₀, mem_locallyNilpotentSubmodule.mpr ⟨k₀, hk₀⟩⟩ 0
      (by simpa [Subtype.ext_iff] using hm₀)
  have htop := (locallyNilpotentSubmodule R M x hx).eq_top_of_isIrreducible R L M
  exact mem_locallyNilpotentSubmodule.mp (htop ▸ LieSubmodule.mem_top m)

/-! ### Locally finite vectors -/

/-- A subspace is stable under bracketing with `x` exactly when its image under the action of `x`
is contained in it. -/
private theorem map_toEnd_le_iff {x : L} {N : Submodule R M} :
    N.map (toEnd R L M x) ≤ N ↔ ∀ u ∈ N, ⁅x, u⁆ ∈ N := by
  simp [SetLike.le_def]

variable (R M) in
/-- The vectors of `M` lying in some finitely generated `R`-submodule stable under bracketing with
every element of `S`, as a Lie submodule of `M`.

Stability under all of `L` uses that `L` is a finite `R`-module: if `N` is finitely generated and
`S`-stable, then `N + ⁅L, N⁆` is again finitely generated and `S`-stable, and it contains `⁅y, m⁆`
for every `y : L` and `m ∈ N`. -/
def locallyFiniteSubmodule [Module.Finite R L] (S : Set L) : LieSubmodule R L M where
  carrier := {m | ∃ N : Submodule R M, N.FG ∧ (∀ x ∈ S, ∀ u ∈ N, ⁅x, u⁆ ∈ N) ∧ m ∈ N}
  zero_mem' := ⟨⊥, Submodule.fg_bot, by simp, Submodule.zero_mem ⊥⟩
  add_mem' := by
    rintro a c ⟨N₁, hfg₁, hst₁, ha⟩ ⟨N₂, hfg₂, hst₂, hc⟩
    refine ⟨N₁ ⊔ N₂, hfg₁.sup hfg₂, fun x hx => ?_,
      add_mem (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hc)⟩
    rw [← map_toEnd_le_iff, Submodule.map_sup]
    exact sup_le_sup ((map_toEnd_le_iff).mpr (hst₁ x hx)) ((map_toEnd_le_iff).mpr (hst₂ x hx))
  smul_mem' := by
    rintro c a ⟨N, hfg, hst, ha⟩
    exact ⟨N, hfg, hst, N.smul_mem c ha⟩
  lie_mem := by
    rintro y m ⟨N, hfg, hst, hm⟩
    let br : L →ₗ[R] M →ₗ[R] M :=
      LinearMap.mk₂ R (fun (z : L) (u : M) => ⁅z, u⁆) add_lie smul_lie lie_add lie_smul
    set Q : Submodule R M := Submodule.map₂ br ⊤ N with hQ
    have hbr : ∀ (z : L) {u : M}, u ∈ N → ⁅z, u⁆ ∈ Q := fun z u hu =>
      Submodule.apply_mem_map₂ br Submodule.mem_top hu
    have hQfg : Q.FG := by
      rw [hQ]
      exact Module.Finite.fg_top.map₂ br hfg
    refine ⟨N ⊔ Q, hfg.sup hQfg, fun x hx => ?_, Submodule.mem_sup_right (hbr y hm)⟩
    rw [← map_toEnd_le_iff, Submodule.map_sup]
    refine sup_le (((map_toEnd_le_iff).mpr (hst x hx)).trans le_sup_left) ?_
    rw [hQ, Submodule.map_le_iff_le_comap, Submodule.map₂_le]
    intro z _ u hu
    -- `Submodule.map₂_le` exposes the locally defined bilinear map `br`; unfold its
    -- definitional action to put the Jacobi identity into bracket notation.
    change ⁅x, ⁅z, u⁆⁆ ∈ N ⊔ Q
    rw [leibniz_lie]
    exact add_mem (Submodule.mem_sup_right (hbr ⁅x, z⁆ hu))
      (Submodule.mem_sup_right (hbr z (hst x hx u hu)))

@[simp]
theorem mem_locallyFiniteSubmodule [Module.Finite R L] {S : Set L} {m : M} :
    m ∈ locallyFiniteSubmodule R M S ↔
      ∃ N : Submodule R M, N.FG ∧ (∀ x ∈ S, ∀ u ∈ N, ⁅x, u⁆ ∈ N) ∧ m ∈ N :=
  Iff.rfl

/-- Only the span of `S` matters: a subspace stable under `S` is stable under the `R`-submodule
that `S` generates, the stability condition being linear in the bracketing element. -/
@[simp]
theorem locallyFiniteSubmodule_span [Module.Finite R L] (S : Set L) :
    locallyFiniteSubmodule R M (Submodule.span R S : Set L) = locallyFiniteSubmodule R M S := by
  refine le_antisymm ?_ ?_
  · rintro m ⟨N, hfg, hst, hm⟩
    exact ⟨N, hfg, fun x hx => hst x (Submodule.subset_span hx), hm⟩
  · rintro m ⟨N, hfg, hst, hm⟩
    refine ⟨N, hfg, fun x hx => ?_, hm⟩
    induction hx using Submodule.span_induction with
    | mem z hz => exact hst z hz
    | zero => simp
    | add a c _ _ ha hc => exact fun u hu => by rw [add_lie]; exact add_mem (ha u hu) (hc u hu)
    | smul c a _ ha => exact fun u hu => by rw [smul_lie]; exact N.smul_mem c (ha u hu)

/-- **Local finiteness spreads over an irreducible module.** If some nonzero vector of an
irreducible module lies in a finitely generated `S`-stable subspace, then every vector does. -/
theorem locallyFiniteSubmodule_eq_top_of_isIrreducible [Module.Finite R L]
    [LieModule.IsIrreducible R L M] {S : Set L} {N₀ : Submodule R M} (hfg₀ : N₀.FG)
    (hst₀ : ∀ x ∈ S, ∀ u ∈ N₀, ⁅x, u⁆ ∈ N₀) {m₀ : M} (hm₀ : m₀ ≠ 0) (hmem₀ : m₀ ∈ N₀) :
    locallyFiniteSubmodule R M S = ⊤ :=
  have : Nontrivial (locallyFiniteSubmodule R M S) :=
    nontrivial_of_ne ⟨m₀, mem_locallyFiniteSubmodule.mpr ⟨N₀, hfg₀, hst₀, hmem₀⟩⟩ 0
      (by simpa [Subtype.ext_iff] using hm₀)
  (locallyFiniteSubmodule R M S).eq_top_of_isIrreducible R L M

end TauCeti
