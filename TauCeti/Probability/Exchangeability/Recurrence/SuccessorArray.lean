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

For a recurrent path, the visit times of a visited state are genuine, strictly increasing visits,
and the visit counts along them run through every natural number; so the successor-array row of
such a state is an infinite list of genuine transitions, read off at those times. Rows indexed by
unvisited states remain unconstrained and may contain `Nat.nth`'s junk values.

Combined with `successorArray_def`, which reads a row entry off the visit time, these are the
facts that make every entry of a visited-state row a genuine transition of the path. Recovering
the path from its successor array needs none of this — `pathOfSuccessors_successorArray` inverts
the decomposition of an arbitrary sequence — but the later probabilistic argument, which permutes
the entries within a row, does need them to be real transitions rather than junk.

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
theorem Recurrent.ae_apply_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, X (visitTime (fun n => X n ω) (X k ω) j) ω = X k ω := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  simpa only [visitTime_def] using Nat.nth_mem_of_infinite (hω k) j

/-- The visit times of a visited state of a recurrent process are strictly increasing, so the
successor-array row of that state is read off at distinct times, in order. -/
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

end SuccessorArray

end Probability

end TauCeti

end

end
