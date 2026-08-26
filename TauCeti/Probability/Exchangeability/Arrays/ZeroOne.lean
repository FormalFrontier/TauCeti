/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- Public: dissociation is the hypothesis of every zero-one statement here.
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
-- Public: the zero-one criterion for i.i.d.-ness, of which the diagonal theorem is an instance.
public import TauCeti.Probability.DeFinetti.ZeroOne
-- Non-public: the zero-one law for a self-independent event is used only inside a proof.
import Mathlib.Probability.Independence.ZeroOne

/-!
# The zero-one law for a dissociated array

A dissociated array has no global randomness left to remember: the events readable from the entries
`X (i, j)` with both indices arbitrarily large are almost surely trivial.

The proof is Kolmogorov's. Split the index square at `n` into the corner `[0, n] × [0, n]` and the
shell `[n + 1, ∞) × [n + 1, ∞)`. The two index sets are disjoint, so joint dissociation makes the
corner independent of the shell; the shells decrease to `arrayTail X`, which is therefore
independent of every corner, hence of the σ-algebra the corners generate, which is all of the array.
Being independent of itself, the array tail is trivial.

Two disjointness conditions per pair of blocks is what dissociation asks for, and `arrayTail` is
built to supply them: it is the **diagonal** tail, cutting *both* index axes at `n`. The row tail
`⨅ n, blockSigma X ([n, ∞) × ℕ)` is genuinely not trivial for a dissociated array — an array whose
rows are all one common i.i.d. random path is separately dissociated, and its row tail carries the
whole path.

The application is the diagonal. Dissociation makes the diagonal entries **pairwise** independent
by inspection (`JointlyDissociated.indepFun_arrayDiag`), which for a general family is far short of
independence; but the diagonal of a jointly exchangeable array is an exchangeable sequence with tail
inside `arrayTail X`, so the zero-one law above and the de Finetti criterion
`iIndepFun_of_exchangeable_of_tailProcess_trivial` together make it i.i.d.
(`JointlyDissociated.iIndepFun_arrayDiag`). This is the array analogue of a product law's being the
extreme case of an exchangeable law, and it matches the ergodic Aldous--Hoover coding
`X (i, j) = f (U_vert i) (U_vert j) (U_cell {i, j})` in `Arrays/AldousHoover.lean`, whose diagonal
reads a fresh vertex and cell variable at each index.

These results advance the exchangeable-arrays milestone of
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8: the ergodic form of the Aldous--Hoover
representation is the dissociated one, and this is the zero-one law separating it from the general
form.

## Main definitions

* `TauCeti.Probability.arrayShell` — the σ-algebra of the entries with both indices at least `n`;
* `TauCeti.Probability.arrayTail` — the tail σ-algebra of an array, the infimum of the shells.

## Main results

* `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_arrayTail` — **the zero-one
  law**: the tail σ-algebra of a jointly dissociated array is trivial;
* `TauCeti.Probability.SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail` — the same for the
  stronger symmetry;
* `TauCeti.Probability.JointlyDissociated.iIndepFun_arrayDiag` — the diagonal of a jointly
  exchangeable, jointly dissociated array over a standard Borel state space is i.i.d.

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

/-- The **shell σ-algebra** of an array at time `n`: the events readable from the entries
`X (i, j)` with `n ≤ i` and `n ≤ j`. It is the array analogue of the future σ-algebra `tailFamily`
of a process, cutting both index axes at once. -/
@[expose, implicit_reducible]
def arrayShell (X : ℕ × ℕ → Ω → α) (n : ℕ) : MeasurableSpace Ω :=
  blockSigma X (Set.Ici n ×ˢ Set.Ici n)

/-- The **tail σ-algebra of an array**: the events readable from the entries with both indices
arbitrarily large. It is the array analogue of `tailProcess`. -/
@[expose, implicit_reducible]
def arrayTail (X : ℕ × ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ n, arrayShell X n

omit [MeasurableSpace Ω] in
/-- Normal form for the shell σ-algebra. -/
@[simp]
theorem arrayShell_eq_blockSigma (X : ℕ × ℕ → Ω → α) (n : ℕ) :
    arrayShell X n = blockSigma X (Set.Ici n ×ˢ Set.Ici n) :=
  (rfl)

omit [MeasurableSpace Ω] in
/-- Normal form for the tail σ-algebra of an array. -/
@[simp]
theorem arrayTail_eq_iInf_arrayShell (X : ℕ × ℕ → Ω → α) :
    arrayTail X = ⨅ n, arrayShell X n :=
  (rfl)

omit [MeasurableSpace Ω] in
/-- An entry with both indices at least `n` is measurable for the shell σ-algebra at `n`. -/
theorem measurable_arrayShell_of_le {n i j : ℕ} (hi : n ≤ i) (hj : n ≤ j) :
    Measurable[arrayShell X n] (X (i, j)) :=
  measurable_blockSigma_of_mem ⟨hi, hj⟩

omit [MeasurableSpace Ω] in
/-- The shells decrease. -/
theorem arrayShell_antitone (X : ℕ × ℕ → Ω → α) : Antitone (arrayShell X) := fun _ _ hab =>
  blockSigma_mono (Set.prod_mono (Set.Ici_subset_Ici.mpr hab) (Set.Ici_subset_Ici.mpr hab))

omit [MeasurableSpace Ω] in
/-- The tail σ-algebra of an array sits inside every shell. -/
theorem arrayTail_le_arrayShell (X : ℕ × ℕ → Ω → α) (n : ℕ) : arrayTail X ≤ arrayShell X n :=
  iInf_le _ n

/-- The shell σ-algebra of an array with measurable entries is a sub-σ-algebra of the ambient
one. -/
theorem arrayShell_le_ambient (hX : ∀ p, Measurable (X p)) (n : ℕ) :
    arrayShell X n ≤ (inferInstance : MeasurableSpace Ω) :=
  blockSigma_le _ fun p _ => hX p

/-- The tail σ-algebra of an array with measurable entries is a sub-σ-algebra of the ambient
one. -/
theorem arrayTail_le_ambient (hX : ∀ p, Measurable (X p)) :
    arrayTail X ≤ (inferInstance : MeasurableSpace Ω) :=
  (arrayTail_le_arrayShell X 0).trans (arrayShell_le_ambient hX 0)

omit [MeasurableSpace Ω] in
/-- **The tail of the diagonal is an array tail event.** The diagonal entries from time `n` on have
both indices at least `n`, so they generate a sub-σ-algebra of the shell at `n`. -/
theorem tailProcess_arrayDiag_le_arrayTail (X : ℕ × ℕ → Ω → α) :
    tailProcess (arrayDiag X) ≤ arrayTail X := by
  refine le_iInf fun n => (tailProcess_le_tailFamily _ n).trans (tailFamily_le_iff.mpr ?_)
  intro k hk
  simpa only [arrayDiag_apply] using measurable_arrayShell_of_le (X := X) hk hk

omit [MeasurableSpace Ω] in
/-- Implementation: the entries read by a block of the array all lie in the σ-algebra that block
generates as a random element of array space. The hypothesis says every index in `S` is reached by
the index map `e`. -/
private theorem blockSigma_le_comap_squareBlock {e : ℕ → ℕ} {S : Set (ℕ × ℕ)}
    (hS : ∀ p ∈ S, ∃ q : ℕ × ℕ, (e q.1, e q.2) = p) :
    blockSigma X S ≤
      MeasurableSpace.comap (fun ω (q : ℕ × ℕ) => X (e q.1, e q.2) ω) inferInstance := by
  refine blockSigma_le_iff.mpr fun p hp => ?_
  obtain ⟨q, hq⟩ := hS p hp
  have hblock : Measurable[MeasurableSpace.comap
      (fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω) inferInstance]
      fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω :=
    Measurable.of_comap_le le_rfl
  have hmeas : Measurable[MeasurableSpace.comap
      (fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω) inferInstance]
      fun ω => X (e q.1, e q.2) ω := (measurable_pi_apply q).comp hblock
  rwa [hq] at hmeas

/-- **A corner of a jointly dissociated array is independent of the complementary shell.** The
corner `[0, n] × [0, n]` and the shell `[n + 1, ∞) × [n + 1, ∞)` are square blocks over disjoint
sets of indices. -/
theorem JointlyDissociated.indep_blockSigma_Iic_arrayShell (h : JointlyDissociated μ X) (n : ℕ) :
    Indep (blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (arrayShell X (n + 1)) μ := by
  have hrange₁ : (Set.range fun i => min i n) = Set.Iic n := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      exact min_le_right i n
    · exact fun hm => ⟨m, min_eq_left hm⟩
  have hrange₂ : (Set.range fun i => n + 1 + i) = Set.Ici (n + 1) := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      exact Nat.le_add_right _ _
    · exact fun hm => ⟨m - (n + 1), Nat.add_sub_cancel' hm⟩
  have hdisj : Disjoint (Set.range fun i => min i n) (Set.range fun i => n + 1 + i) := by
    rw [hrange₁, hrange₂]
    exact Set.disjoint_left.mpr fun x hx hx' =>
      absurd (le_trans (Set.mem_Ici.mp hx') (Set.mem_Iic.mp hx)) (Nat.not_succ_le_self n)
  have hindep := jointlyDissociated_iff.mp h (fun i => min i n) (fun i => n + 1 + i) hdisj
  rw [IndepFun_iff_Indep] at hindep
  have hcorner : blockSigma X (Set.Iic n ×ˢ Set.Iic n) ≤
      MeasurableSpace.comap (fun ω (q : ℕ × ℕ) => X (min q.1 n, min q.2 n) ω) inferInstance :=
    blockSigma_le_comap_squareBlock (X := X) (e := fun i => min i n)
      (S := Set.Iic n ×ˢ Set.Iic n)
      fun p hp => ⟨p, by rw [min_eq_left hp.1, min_eq_left hp.2]⟩
  have hshell : arrayShell X (n + 1) ≤ MeasurableSpace.comap
      (fun ω (q : ℕ × ℕ) => X (n + 1 + q.1, n + 1 + q.2) ω) inferInstance :=
    blockSigma_le_comap_squareBlock (X := X) (e := fun i => n + 1 + i)
      (S := Set.Ici (n + 1) ×ˢ Set.Ici (n + 1))
      fun p hp => ⟨(p.1 - (n + 1), p.2 - (n + 1)), by
        rw [Nat.add_sub_cancel' hp.1, Nat.add_sub_cancel' hp.2]⟩
  exact indep_of_indep_of_le hindep hcorner hshell

/-- **The tail σ-algebra of a jointly dissociated array is independent of itself.** Every corner is
independent of the tail, the corners are increasing and generate the whole array σ-algebra, and the
tail sits inside it. -/
theorem JointlyDissociated.indep_arrayTail_self [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) :
    Indep (arrayTail X) (arrayTail X) μ := by
  have hle : ∀ n : ℕ,
      blockSigma X (Set.Iic n ×ˢ Set.Iic n) ≤ (inferInstance : MeasurableSpace Ω) :=
    fun _ => blockSigma_le _ fun p _ => hX p
  have hmono : Monotone fun n : ℕ => blockSigma X (Set.Iic n ×ˢ Set.Iic n) := fun a b hab =>
    blockSigma_mono (Set.prod_mono (Set.Iic_subset_Iic.mpr hab) (Set.Iic_subset_Iic.mpr hab))
  have hindep : ∀ n : ℕ, Indep (blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (arrayTail X) μ := fun n =>
    indep_of_indep_of_le_right (h.indep_blockSigma_Iic_arrayShell n)
      (arrayTail_le_arrayShell X (n + 1))
  have hsup := indep_iSup_of_monotone hindep hle (arrayTail_le_ambient hX) hmono
  refine indep_of_indep_of_le_left hsup ((arrayTail_le_arrayShell X 0).trans ?_)
  rw [arrayShell_eq_blockSigma]
  refine blockSigma_le_iff.mpr fun p _ => ?_
  exact (measurable_blockSigma_of_mem (Z := X)
    (S := Set.Iic (max p.1 p.2) ×ˢ Set.Iic (max p.1 p.2))
    ⟨Set.mem_Iic.mpr (le_max_left p.1 p.2), Set.mem_Iic.mpr (le_max_right p.1 p.2)⟩).mono
      (le_iSup (fun n : ℕ => blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (max p.1 p.2)) le_rfl

/-- **The zero-one law for a dissociated array.** Every event in the tail σ-algebra of a jointly
dissociated array has probability `0` or `1`.

The tail cuts both index axes, as dissociation requires: for the row tail alone the statement is
false, an array all of whose rows are one common i.i.d. random path being dissociated with a row
tail that carries the whole path. -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_arrayTail [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    ((h.indep_arrayTail_self hX).indepSet_of_measurableSet hs hs)

/-- **The zero-one law for a separately dissociated array**, the corollary of the jointly
dissociated form at the stronger symmetry. -/
theorem SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail [IsProbabilityMeasure μ]
    (h : SeparatelyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  h.jointlyDissociated.measure_eq_zero_or_one_of_arrayTail hX hs

/-- **The diagonal of a jointly dissociated array has a trivial tail.** -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[tailProcess (arrayDiag X)] s) : μ s = 0 ∨ μ s = 1 :=
  h.measure_eq_zero_or_one_of_arrayTail hX (tailProcess_arrayDiag_le_arrayTail X s hs)

/-- **The diagonal of a jointly exchangeable, jointly dissociated array is i.i.d.**, with its common
law named: over a standard Borel state space there is a probability measure `P` with `fun _ => P` a
mixing representative of the diagonal, so the diagonal entries are independent with common law `P`.

Dissociation alone gives only pairwise independence of the diagonal
(`JointlyDissociated.indepFun_arrayDiag`). What upgrades it is exchangeability: the diagonal of a
jointly exchangeable array is an exchangeable sequence, its tail is trivial by the zero-one law
above, and a tail-trivial exchangeable sequence is i.i.d. -/
theorem JointlyDissociated.exists_mixedIIDWith_const_arrayDiag [StandardBorelSpace α]
    [IsProbabilityMeasure μ] (h : JointlyDissociated μ X) (hexch : JointlyExchangeable μ X)
    (hX : ∀ p, Measurable (X p)) :
    ∃ P : ProbabilityMeasure α, MixedIIDWith μ (arrayDiag X) fun _ => P :=
  exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial
    (fun n => by simpa only [arrayDiag_apply] using hX (n, n))
    (hexch.exchangeable_arrayDiag fun p => (hX p).aemeasurable)
    fun _ hs => h.measure_eq_zero_or_one_of_tailProcess_arrayDiag hX hs

/-- **The diagonal entries of a jointly exchangeable, jointly dissociated array are independent**,
the independence half of `JointlyDissociated.exists_mixedIIDWith_const_arrayDiag`. -/
theorem JointlyDissociated.iIndepFun_arrayDiag [StandardBorelSpace α] [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hexch : JointlyExchangeable μ X)
    (hX : ∀ p, Measurable (X p)) :
    iIndepFun (arrayDiag X) μ := by
  obtain ⟨_, hP⟩ := h.exists_mixedIIDWith_const_arrayDiag hexch hX
  exact hP.iIndepFun_of_const

end Probability

end TauCeti

end

end
