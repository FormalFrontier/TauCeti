/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `Subalgebra`, `Subalgebra.centralizer` and the lattice of subalgebras, together with
-- `IsMulCommutative` and `Module.finrank`, all occur in the statements below.
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: used only inside the proofs. `Algebra.isMulCommutative_adjoin` comes with the lattice
-- import above; `Subalgebra.eq_of_le_of_finrank_le` turns an inclusion of subalgebras of equal
-- dimension into an equality, and `Submodule.finrank_le` bounds the dimension of a subalgebra by
-- that of the ambient algebra.
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Commutative subalgebras of maximal dimension

Let `A` be a finite-dimensional algebra over a field `K`. Dimensions of subalgebras of `A` are
bounded by `finrank K A`, so among the commutative subalgebras there is one of largest dimension,
and such a subalgebra is its own centralizer: an element commuting with all of it generates,
together with it, a commutative subalgebra, which maximal dimension forces to be it again.

Neither statement needs anything of `A` beyond finite-dimensionality. They become interesting in a
division algebra, where a commutative subalgebra of maximal dimension is a maximal subfield
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg` in
`TauCeti/Algebra/CentralSimple/MaximalSubfield.lean`).

## Main results

* `TauCeti.exists_isMulCommutative_forall_finrank_le`: a finite-dimensional algebra has a
  commutative subalgebra of maximal dimension.
* `TauCeti.centralizer_eq_self_of_forall_finrank_le`: such a subalgebra is its own centralizer.

## Implementation notes

Commutativity of a subalgebra is Mathlib's `IsMulCommutative` on its coercion to a type, which is
what `Algebra.isMulCommutative_adjoin` produces, rather than a hand-rolled
`∀ x ∈ L, ∀ y ∈ L, x * y = y * x`; `setLike_mul_comm` is the lemma that reads the second off the
first.

Maximality is in dimension over `K`, stated as a bound on every commutative subalgebra, and not as
maximality for inclusion; the two agree here, but the dimension form is what the count in a central
simple algebra consumes.
-/

public section

namespace TauCeti

open Module

section Maximal

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **A finite-dimensional algebra has a commutative subalgebra of maximal dimension.**

Maximality is in dimension over `K` and is stated as a bound on every commutative subalgebra of
`A`, not as maximality for inclusion.

No hypothesis beyond finite-dimensionality is needed; it is in a division algebra that such a
subalgebra becomes interesting
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`). -/
theorem exists_isMulCommutative_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative ↥L ∧
      ∀ M : Subalgebra K A, IsMulCommutative ↥M → finrank K ↥M ≤ finrank K ↥L := by
  classical
  set P : ℕ → Prop := fun n ↦ ∃ M : Subalgebra K A, IsMulCommutative ↥M ∧ finrank K ↥M = n
  -- The bottom subalgebra is commutative, so `P` is satisfied below the bound `finrank K A`.
  have hbot : IsMulCommutative ↥(⊥ : Subalgebra K A) :=
    Algebra.adjoin_empty K A ▸ Algebra.isMulCommutative_adjoin K (by simp)
  have hle : ∀ M : Subalgebra K A, finrank K ↥M ≤ finrank K A := fun M ↦
    Submodule.finrank_le (Subalgebra.toSubmodule M)
  have hstart : P (finrank K ↥(⊥ : Subalgebra K A)) := ⟨⊥, hbot, rfl⟩
  obtain ⟨L, hL, hLn⟩ := Nat.findGreatest_spec (hle ⊥) hstart
  refine ⟨L, hL, fun M hM ↦ ?_⟩
  rw [hLn]
  exact Nat.le_findGreatest (hle M) ⟨M, hM, rfl⟩

variable {K A}

/-- **A commutative subalgebra of maximal dimension is its own centralizer.**

Maximality enters as the hypothesis `hmax`, the dimension bound over all commutative subalgebras
of `A` that `TauCeti.exists_isMulCommutative_forall_finrank_le` produces.

Nothing beyond finite-dimensionality is asked of `A`; it is in a division algebra that the
conclusion becomes the maximality of a subfield
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`). -/
theorem centralizer_eq_self_of_forall_finrank_le {L : Subalgebra K A} [IsMulCommutative ↥L]
    (hmax : ∀ M : Subalgebra K A, IsMulCommutative ↥M → finrank K ↥M ≤ finrank K ↥L) :
    Subalgebra.centralizer K (L : Set A) = L := by
  refine le_antisymm (fun x hx ↦ ?_)
    (fun y hy ↦ (Subalgebra.mem_centralizer_iff K).2 fun z hz ↦ setLike_mul_comm hz hy)
  -- The elements of `insert x L` commute pairwise.
  have hcomm : ∀ a ∈ insert x (L : Set A), ∀ b ∈ insert x (L : Set A), a * b = b * a := by
    rintro a (rfl | ha) b (rfl | hb)
    · rfl
    · exact ((Subalgebra.mem_centralizer_iff K).1 hx b hb).symm
    · exact (Subalgebra.mem_centralizer_iff K).1 hx a ha
    · exact setLike_mul_comm ha hb
  have hM : IsMulCommutative ↥(Algebra.adjoin K (insert x (L : Set A))) :=
    Algebra.isMulCommutative_adjoin K hcomm
  have hsub : L ≤ Algebra.adjoin K (insert x (L : Set A)) := fun a ha ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)
  have := Subalgebra.eq_of_le_of_finrank_le hsub (hmax _ hM)
  exact this ▸ Algebra.subset_adjoin (Set.mem_insert _ _)

end Maximal

end TauCeti

end
