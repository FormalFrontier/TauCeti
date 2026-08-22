/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray
public import TauCeti.Probability.Recurrent

/-!
# Recurrence and successor arrays

For a recurrent path, every row indexed by a visited state is an infinite list of genuine
transitions. Rows indexed by unvisited states remain unconstrained and may contain
`Nat.nth`'s junk values.

The results identify visit times and visit counts for visited states and show that every cell of
a visited successor-array row is realized by an actual transition.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".
-/

public section

noncomputable section

open Filter MeasureTheory

namespace TauCeti

namespace Probability

section SuccessorArray

variable {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **The visit times of a visited state are genuine visits.** Off a recurrent path the later
entries of `visitTime` are `Nat.nth`'s junk value; on one they are the times at which the process
really is at that state. -/
theorem Recurrent.ae_visitTime_apply (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, X (visitTime (fun n => X n ω) (X k ω) j) ω = X k ω := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  simpa only [visitTime_def] using Nat.nth_mem_of_infinite (hω k) j

/-- The visit times of a visited state of a recurrent process are strictly increasing, so the
corresponding row of the successor array lists distinct times in order. -/
theorem Recurrent.ae_strictMono_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, StrictMono (visitTime (fun n => X n ω) (X k ω)) := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k
  have hfun : visitTime (fun n => X n ω) (X k ω) = Nat.nth fun i => X i ω = X k ω := by
    funext j
    exact visitTime_def _ _ _
  rw [hfun]
  exact Nat.nth_strictMono (hω k)

/-- The `j`-th visit of a recurrent process to one of its states really is preceded by exactly
`j` earlier visits. -/
theorem Recurrent.ae_visitCount_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ,
      visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) j) = j := by
  classical
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  rw [visitCount_eq_count, visitTime_def]
  exact Nat.count_nth_of_infinite (hω k) j

/-- **Each visited row of the successor array is infinite.** A recurrent process accumulates
unboundedly many visits to every state it attains. -/
theorem Recurrent.ae_tendsto_visitCount_atTop (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, Tendsto (visitCount (fun n => X n ω) (X k ω)) atTop atTop := by
  filter_upwards [h.ae_visitCount_visitTime] with ω hω k
  refine tendsto_atTop_atTop.2 fun b => ⟨visitTime (fun n => X n ω) (X k ω) b, fun n hn => ?_⟩
  calc b = visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) b) :=
        (hω k b).symm
    _ ≤ visitCount (fun n => X n ω) (X k ω) n := visitCount_monotone _ _ hn

/-- **Every cell of a visited row is realized by a time.** For a recurrent process the index `j`
of a row of the successor array is the number of earlier visits at an actual time. -/
theorem Recurrent.ae_exists_visitCount_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, ∃ n, X n ω = X k ω ∧ visitCount (fun n => X n ω) (X k ω) n = j := by
  filter_upwards [h.ae_visitTime_apply, h.ae_visitCount_visitTime] with ω h₁ h₂ k j
  exact ⟨_, h₁ k j, h₂ k j⟩

/-- **No junk in a visited row of the successor array.** Every entry of the row of a visited state
is the value the process takes right after an actual visit to that state. -/
theorem Recurrent.ae_exists_successorArray_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ,
      ∃ n, X n ω = X k ω ∧ successorArray (fun n => X n ω) (X k ω) j = X (n + 1) ω := by
  filter_upwards [h.ae_visitTime_apply] with ω h₁ k j
  exact ⟨_, h₁ k j, successorArray_def _ _ _⟩

end SuccessorArray

end Probability

end TauCeti

end

end
