/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- Public: dissociation and array-tail σ-algebras appear in theorem statements here.
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
public import TauCeti.Probability.Exchangeability.Arrays.Tail
-- Non-public: the zero-one law for a self-independent event is used only inside a proof.
import Mathlib.Probability.Independence.ZeroOne

/-!
# The zero-one law for a dissociated array

A dissociated array has no global randomness left to remember: the events readable from the entries
`X (i, j)` with both indices arbitrarily large are almost surely trivial.

The proof is Kolmogorov's. Fix a cutoff `n` past which the entries are measurable and read the
array from there on. The corners `[n, n + k] × [n, n + k]` and the tail block
`[n + k + 1, ∞) × [n + k + 1, ∞)` have disjoint index sets, so joint dissociation makes each corner
independent of the tail block, hence of `arrayTail X`, which the tail blocks contain. The corners
increase to the σ-algebra of all entries with both indices at least `n`, that is to
`arrayTailFamily X n`, which contains `arrayTail X`. So the array tail is independent of everything
readable above the cutoff, in particular of itself, and is therefore trivial.

Two disjointness conditions per pair of blocks is what dissociation asks for, and `arrayTail` is
built to supply them: it is the **corner** tail, cutting *both* index axes at `n`. The row tail
`⨅ n, blockSigma X ([n, ∞) × ℕ)` is genuinely not trivial for a dissociated array — an array whose
rows are all one common i.i.d. random path is separately dissociated, and its row tail carries the
whole path.

These results advance the exchangeable-arrays milestone of
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8: the ergodic form of the Aldous--Hoover
representation is the dissociated one, and this is the zero-one law separating it from the general
form.

## Main results

* `TauCeti.Probability.JointlyDissociated.indep_arrayTailFamily_arrayTail` — the array tail of a
  jointly dissociated array is independent of everything readable above the cutoff, and in
  particular `TauCeti.Probability.JointlyDissociated.indep_arrayTail_self` of itself;
* `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_arrayTail` — **the zero-one
  law**: the tail σ-algebra of a jointly dissociated array is trivial;
* `TauCeti.Probability.SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail` — the same for the
  stronger dissociation hypothesis;
* `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag` — the
  corollary for the diagonal process, whose tail is an array tail event.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}
  {X : ℕ × ℕ → Ω → α}

/-- **The tail σ-algebra of a jointly dissociated array is independent of everything readable
above the cutoff.** The corners above `n` are independent of the tail and increase to the tail
family at `n`. Only entries beyond that cutoff need to be measurable. -/
theorem JointlyDissociated.indep_arrayTailFamily_arrayTail [IsZeroOrProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) :
    Indep (arrayTailFamily X n) (arrayTail X) μ := by
  let corner : ℕ → Set ℕ := fun k => Set.Icc n (n + k)
  have hle : ∀ k : ℕ,
      blockSigma X (corner k ×ˢ corner k) ≤ (inferInstance : MeasurableSpace Ω) :=
    fun _ => blockSigma_le _ fun p hp => hX p hp.1.1 hp.2.1
  have hmono : Monotone fun k : ℕ => blockSigma X (corner k ×ˢ corner k) := fun a b hab =>
    blockSigma_mono (Set.prod_mono
      (Set.Icc_subset_Icc le_rfl (Nat.add_le_add_left hab n))
      (Set.Icc_subset_Icc le_rfl (Nat.add_le_add_left hab n)))
  have hindep : ∀ k : ℕ, Indep (blockSigma X (corner k ×ˢ corner k)) (arrayTail X) μ := by
    intro k
    apply indep_of_indep_of_le_right _ (arrayTail_le_arrayTailFamily X (n + k + 1))
    rw [arrayTailFamily_eq_blockSigma]
    exact h.indep_blockSigma_prod
      (Set.disjoint_of_subset_left Set.Icc_subset_Iic_self
        ((Set.Iic_disjoint_Ici).2 (Nat.not_succ_le_self (n + k))))
  have hsup := indep_iSup_of_monotone hindep hle
    (arrayTail_le_ambient n hX) hmono
  refine indep_of_indep_of_le_left hsup ?_
  rw [arrayTailFamily_eq_blockSigma]
  refine blockSigma_le_iff.mpr fun p hp => ?_
  exact (measurable_blockSigma_of_mem (Z := X)
    (S := corner (max p.1 p.2) ×ˢ corner (max p.1 p.2))
    ⟨⟨hp.1,
        (le_max_left p.1 p.2).trans (Nat.le_add_left _ _)⟩,
      ⟨hp.2,
        (le_max_right p.1 p.2).trans (Nat.le_add_left _ _)⟩⟩).mono
      (le_iSup (fun k : ℕ => blockSigma X (corner k ×ˢ corner k)) (max p.1 p.2)) le_rfl

/-- **The tail σ-algebra of a jointly dissociated array is independent of itself**, the special
case of `JointlyDissociated.indep_arrayTailFamily_arrayTail` in which the left σ-algebra is cut
down to the array tail. -/
theorem JointlyDissociated.indep_arrayTail_self [IsZeroOrProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) :
    Indep (arrayTail X) (arrayTail X) μ :=
  indep_of_indep_of_le_left (h.indep_arrayTailFamily_arrayTail n hX)
    (arrayTail_le_arrayTailFamily X n)

/-- **The zero-one law for a dissociated array.** Every event in the tail σ-algebra of a jointly
dissociated array has probability `0` or `1`.

The tail cuts both index axes, as dissociation requires: for the row tail alone the statement is
false, an array all of whose rows are one common i.i.d. random path being dissociated with a row
tail that carries the whole path. -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_arrayTail [IsZeroOrProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  measure_eq_zero_or_one_of_indep_self (h.indep_arrayTail_self n hX) hs

/-- **The zero-one law for a separately dissociated array**, the corollary of the jointly
dissociated form under the stronger dissociation hypothesis. -/
theorem SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail [IsZeroOrProbabilityMeasure μ]
    (h : SeparatelyDissociated μ X) (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  h.jointlyDissociated.measure_eq_zero_or_one_of_arrayTail n hX hs

/-- **The diagonal of a jointly dissociated array has a trivial tail.** The tail of the diagonal
process is an array tail event, so this is the zero-one law read along the diagonal. -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag
    [IsZeroOrProbabilityMeasure μ] (h : JointlyDissociated μ X) (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[tailProcess (arrayDiag X)] s) : μ s = 0 ∨ μ s = 1 :=
  h.measure_eq_zero_or_one_of_arrayTail n hX (tailProcess_arrayDiag_le_arrayTail X s hs)

end Probability

end TauCeti

end

end
