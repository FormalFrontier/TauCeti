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
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.Probability.Martingale.Convergence
import TauCeti.Probability.Exchangeability.PermutationExtension

/-!
# Joint dissociation and the corner tail of an array

A dissociated array has no global randomness left to remember: the events readable from the entries
`X (i, j)` with both indices arbitrarily large are almost surely trivial.

The proof is Kolmogorov's. Fix a cutoff `n` past which the entries are measurable and read the
array from there on. The corners `[n, n + k] × [n, n + k]` and the tail block
`[n + k + 1, ∞) × [n + k + 1, ∞)` have disjoint index sets, so joint dissociation makes each corner
independent of the tail block, hence of `arrayTail X`, which the tail blocks contain. The corners
increase to the σ-algebra of all entries with both indices at least `n`, that is to
`arrayTailFamily X n`, which contains `arrayTail X`. So the array tail is independent of everything
readable above the cutoff, in particular of itself, and is therefore trivial.

The same argument run along the diagonal — corners `{(i, i) : n ≤ i ≤ n + k}` against the square
block over `[n + k + 1, ∞)` — makes the tail of the diagonal process `arrayDiag X` trivial as well,
and it asks only the diagonal entries beyond the cutoff to be measurable.

Two disjointness conditions per pair of blocks is what dissociation asks for, and `arrayTail` is
built to supply them: it is the **corner** tail, cutting *both* index axes at `n`. The row tail
`⨅ n, blockSigma X ([n, ∞) × ℕ)` is genuinely not trivial for a dissociated array — an array whose
rows are all one common i.i.d. random path is separately dissociated, and its row tail carries the
whole path.

**The converse holds for a jointly exchangeable array.** If the corner tail is trivial, the array
is jointly dissociated. The argument is representation-free. Independence of two blocks over
disjoint index sets is checked on the cylinders generating their σ-algebras; a permutation of the
indices, the identity on the finitely many indices the first cylinder reads and carrying the
finitely many the second reads past a cutoff `n`, moves the second cylinder into
`arrayTailFamily X n` without changing either mass or the joint mass, by joint exchangeability;
and along the corner tail filtration Lévy's downward theorem drives the conditional expectation of
the first cylinder's indicator to its tail conditional expectation, which triviality makes the
constant `μ A`, so in the limit the joint mass factorizes.

The ergodic form of the Aldous--Hoover representation is the dissociated one, and this is the
zero-one law separating it from the general form, together with its converse.

## Main results

* `TauCeti.Probability.JointlyDissociated.indep_arrayTailFamily_arrayTail` — the array tail of a
  jointly dissociated array is independent of everything readable above the cutoff, and in
  particular `TauCeti.Probability.JointlyDissociated.indep_arrayTail_self` of itself;
* `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_arrayTail` — **the zero-one
  law**: the tail σ-algebra of a jointly dissociated array is trivial;
* `TauCeti.Probability.JointlyDissociated.indep_tailProcess_arrayDiag_self` and
  `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag` — the
  same argument along the diagonal, giving a trivial tail for the diagonal process under
  measurability of the diagonal entries alone;
* `TauCeti.Probability.jointlyDissociated_of_forall_arrayTail_measure_eq_zero_or_one` — **the
  converse**: a jointly exchangeable array with trivial corner tail is jointly dissociated;
* `TauCeti.Probability.jointlyDissociated_iff_forall_arrayTail_measure_eq_zero_or_one` — the two
  together, **joint dissociation ↔ corner-tail triviality** for a coordinatewise measurable jointly
  exchangeable array under a zero-or-probability measure.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

The converse adapts the representation-free strategy of `Graphon/RelRestrictionIndependence.lean`
(`VertexTailTrivial.isDissociated` and its private Lévy-downward factorization step) in
`cameronfreer/graphon` (Apache 2.0) at commit `175911f9d2e053f2a33d966658dfce0e4ae2811d`; the
array-level assembly — cylinders of the block σ-algebras, the window shift by joint
exchangeability, and the π-system passage to `Indep` — is developed here. No material is adapted
from `cameronfreer/exchangeability`, which treats exchangeable sequences rather than exchangeable
arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TauCeti.MeasureTheory
open scoped Topology

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
    exact h.indep_blockSigma_prod_self
      (Set.disjoint_of_subset_left Set.Icc_subset_Iic_self
        ((Set.Iic_disjoint_Ici).2 (Nat.not_succ_le_self (n + k))))
  have hsup := indep_iSup_of_monotone hindep hle
    (arrayTail_le_ambient n hX) hmono
  exact indep_of_indep_of_le_left hsup (arrayTailFamily_eq_iSup_Icc X n).le

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

/-- **The tail σ-algebra of the diagonal of a jointly dissociated array is independent of
itself.** This is the corner argument of `JointlyDissociated.indep_arrayTail_self` run along the
diagonal: the diagonal corners `{(i, i) : n ≤ i ≤ n + k}` are read by the square block over
`[n, n + k]`, the diagonal tail by the square block over `[n + k + 1, ∞)`
(`tailProcess_arrayDiag_le_arrayTail`), and the corners exhaust the diagonal tail. Only the
*diagonal* entries beyond the cutoff need to be measurable. -/
theorem JointlyDissociated.indep_tailProcess_arrayDiag_self [IsZeroOrProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (n : ℕ) (hX : ∀ i, n ≤ i → Measurable (X (i, i))) :
    Indep (tailProcess (arrayDiag X)) (tailProcess (arrayDiag X)) μ := by
  let corner : ℕ → MeasurableSpace Ω := fun k => blockSigma (arrayDiag X) (Set.Icc n (n + k))
  have hle : ∀ k, corner k ≤ (inferInstance : MeasurableSpace Ω) := fun _ =>
    blockSigma_le _ fun i hi => by
      simpa only [arrayDiag_apply] using hX i hi.1
  have hmono : Monotone corner := fun a b hab =>
    blockSigma_mono (Set.Icc_subset_Icc le_rfl (Nat.add_le_add_left hab n))
  have hexhaust : tailProcess (arrayDiag X) ≤ ⨆ k, corner k := by
    refine (tailProcess_le_tailFamily _ n).trans (tailFamily_le_iff.mpr fun i hi => ?_)
    exact (measurable_blockSigma_of_mem (Z := arrayDiag X) (S := Set.Icc n (n + (i - n)))
      ⟨hi, by omega⟩).mono (le_iSup corner (i - n)) le_rfl
  have hindep : ∀ k, Indep (corner k) (tailProcess (arrayDiag X)) μ := by
    intro k
    have htail : tailProcess (arrayDiag X) ≤
        blockSigma X (Set.Ici (n + k + 1) ×ˢ Set.Ici (n + k + 1)) := by
      rw [← arrayTailFamily_eq_blockSigma]
      exact (tailProcess_arrayDiag_le_arrayTail X).trans
        (arrayTail_le_arrayTailFamily X (n + k + 1))
    exact indep_of_indep_of_le (h.indep_blockSigma_prod_self
        (Set.disjoint_of_subset_left Set.Icc_subset_Iic_self
          ((Set.Iic_disjoint_Ici).2 (Nat.not_succ_le_self (n + k)))))
      (blockSigma_arrayDiag_le_blockSigma_prod_self X _) htail
  exact indep_of_indep_of_le_left
    (indep_iSup_of_monotone hindep hle (hexhaust.trans (iSup_le hle)) hmono) hexhaust

/-- **The diagonal of a jointly dissociated array has a trivial tail.** Every event in the tail
σ-algebra of the diagonal process has probability `0` or `1`. Unlike the zero-one law for the
array tail, this needs only the *diagonal* entries beyond the cutoff to be measurable. -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag
    [IsZeroOrProbabilityMeasure μ] (h : JointlyDissociated μ X) (n : ℕ)
    (hX : ∀ i, n ≤ i → Measurable (X (i, i))) {s : Set Ω}
    (hs : MeasurableSet[tailProcess (arrayDiag X)] s) : μ s = 0 ∨ μ s = 1 :=
  measure_eq_zero_or_one_of_indep_self (h.indep_tailProcess_arrayDiag_self n hX) hs

/-! ## From tail triviality back to dissociation -/

/-- **The core factorization.** For a cylinder `A` of the block over `S = range e × range e` and a
cylinder `B` of the block over `T = range e' × range e'`, with `e`, `e'` of disjoint range,
`μ (A ∩ B) = μ A * μ B`: fix the finitely many `S`-indices of `A`, push the finitely many
`T`-indices of `B` past `n` by a permutation, and apply the Lévy factorization along the corner
tail filtration. -/
private theorem measure_inter_eq_mul_of_cylinders [IsProbabilityMeasure μ]
    {X : ℕ × ℕ → Ω → α} (hX : ∀ p, Measurable (X p)) (hexch : JointlyExchangeable μ X)
    (htriv : ∀ s, MeasurableSet[arrayTail X] s → μ s = 0 ∨ μ s = 1)
    {e e' : ℕ → ℕ} (hd : Disjoint (Set.range e) (Set.range e'))
    {A B : Set Ω}
    (hA : A ∈ piiUnionInter
      (fun p => {s | MeasurableSet[MeasurableSpace.comap (X p) inferInstance] s})
      (Set.range e ×ˢ Set.range e))
    (hB : B ∈ piiUnionInter
      (fun p => {s | MeasurableSet[MeasurableSpace.comap (X p) inferInstance] s})
      (Set.range e' ×ˢ Set.range e')) :
    μ (A ∩ B) = μ A * μ B := by
  classical
  -- unpack the two cylinders: finite index sets and one measurable coordinate set per index
  obtain ⟨tA, htA, fA, hfA, rfl⟩ := hA
  obtain ⟨tB, htB, fB, hfB, rfl⟩ := hB
  have hfA' : ∀ p ∈ tA, ∃ C : Set α, MeasurableSet C ∧ X p ⁻¹' C = fA p := fun p hp =>
    MeasurableSpace.measurableSet_comap.1 (hfA p hp)
  have hfB' : ∀ p ∈ tB, ∃ C : Set α, MeasurableSet C ∧ X p ⁻¹' C = fB p := fun p hp =>
    MeasurableSpace.measurableSet_comap.1 (hfB p hp)
  choose! CA hCA hCAeq using hfA'
  choose! CB hCB hCBeq using hfB'
  -- the cylinders on array space, and the two events as preimages of them
  have hcyl_meas : ∀ (t : Finset (ℕ × ℕ)) (C : ℕ × ℕ → Set α), (∀ p ∈ t, MeasurableSet (C p)) →
      MeasurableSet (Set.pi (↑t) C) := fun t C hC =>
    MeasurableSet.pi t.countable_toSet fun p hp => hC p (Finset.mem_coe.1 hp)
  have hpre : ∀ (ρ : Equiv.Perm ℕ) (t : Finset (ℕ × ℕ)) (C : ℕ × ℕ → Set α),
      (fun ω p => X (ρ p.1, ρ p.2) ω) ⁻¹' Set.pi (↑t) C = ⋂ p ∈ t, X (ρ p.1, ρ p.2) ⁻¹' C p := by
    intro ρ t C; ext ω; simp [Set.mem_pi]
  have hpre1 : ∀ (t : Finset (ℕ × ℕ)) (C : ℕ × ℕ → Set α),
      (fun ω p => X p ω) ⁻¹' Set.pi (↑t) C = ⋂ p ∈ t, X p ⁻¹' C p := by
    intro t C; ext ω; simp [Set.mem_pi]
  -- the index sets touched by the two cylinders are finite and disjoint
  set I : Finset ℕ := tA.image Prod.fst ∪ tA.image Prod.snd with hI
  set J : Finset ℕ := tB.image Prod.fst ∪ tB.image Prod.snd with hJ
  have hI_e : ∀ i ∈ I, i ∈ Set.range e := by
    intro i hi
    simp only [I, Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (htA (Finset.mem_coe.2 hp)).1
    · exact (htA (Finset.mem_coe.2 hp)).2
  have hJ_e' : ∀ j ∈ J, j ∈ Set.range e' := by
    intro j hj
    simp only [J, Finset.mem_union, Finset.mem_image] at hj
    rcases hj with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (htB (Finset.mem_coe.2 hp)).1
    · exact (htB (Finset.mem_coe.2 hp)).2
  have hIJ : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact Set.disjoint_left.mp hd (hI_e i hi) (hJ_e' i hj)
  -- for each `n`, a permutation fixing `I` and pushing `J` past `n`
  choose ρ hρI hρJ using fun n => I.exists_perm_fixOn_le_apply J hIJ n
  have hρ_fixA : ∀ n, ∀ p ∈ tA, (ρ n p.1, ρ n p.2) = p := by
    intro n p hp
    have h1 : p.1 ∈ I := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    have h2 : p.2 ∈ I := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
    rw [hρI n _ h1, hρI n _ h2]
  -- the shifted copies of `B`, each readable above the cutoff `n`
  let B' : ℕ → Set Ω := fun n => ⋂ p ∈ tB, X (ρ n p.1, ρ n p.2) ⁻¹' CB p
  have hB'_meas : ∀ n, MeasurableSet[arrayTailFamily X n] (B' n) := by
    intro n
    refine Finset.measurableSet_biInter _ fun p hp => ?_
    have h1 : n ≤ ρ n p.1 := hρJ n _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
    have h2 : n ≤ ρ n p.2 := hρJ n _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
    exact (measurable_arrayTailFamily_of_le (X := X) h1 h2) (hCB p hp)
  -- the events as preimages of array-space cylinders
  have hAeq : (⋂ p ∈ tA, fA p) = (fun ω p => X p ω) ⁻¹' Set.pi (↑tA) CA := by
    rw [hpre1]; exact Set.iInter₂_congr fun p hp => (hCAeq p hp).symm
  have hBeq : (⋂ p ∈ tB, fB p) = (fun ω p => X p ω) ⁻¹' Set.pi (↑tB) CB := by
    rw [hpre1]; exact Set.iInter₂_congr fun p hp => (hCBeq p hp).symm
  have hAeq' : ∀ n, (⋂ p ∈ tA, fA p) = (fun ω p => X (ρ n p.1, ρ n p.2) ω) ⁻¹' Set.pi (↑tA) CA := by
    intro n; rw [hpre]
    exact Set.iInter₂_congr fun p hp => by rw [hρ_fixA n p hp, hCAeq p hp]
  have hB'eq : ∀ n, B' n = (fun ω p => X (ρ n p.1, ρ n p.2) ω) ⁻¹' Set.pi (↑tB) CB := fun n =>
    (hpre _ _ _).symm
  have hcylA := hcyl_meas tA CA hCA
  have hcylB := hcyl_meas tB CB hCB
  -- the Lévy factorization along the corner tail filtration
  refine measure_inter_eq_mul_of_forall_zero_or_one_iInf (arrayTailFamily_antitone X)
    (fun n => arrayTailFamily_le_ambient n (fun p _ _ => hX p))
    (by rw [← arrayTail_eq_iInf_arrayTailFamily]; exact htriv)
    (Finset.measurableSet_biInter _ fun p hp => by rw [← hCAeq p hp]; exact hX p (hCA p hp))
    hB'_meas ?_ ?_
  · intro n
    rw [hB'eq, hBeq, ← Measure.map_apply (Measurable.of_eval fun p => hX _) hcylB,
      ← Measure.map_apply (Measurable.of_eval fun p => hX _) hcylB]
    exact congrArg (fun m : Measure (ℕ × ℕ → α) => m (Set.pi (↑tB) CB))
      (hexch.map_comp (fun p => (hX p).aemeasurable) (ρ n) measurable_id)
  · intro n
    have hL : (⋂ p ∈ tA, fA p) ∩ B' n
        = (fun ω p => X (ρ n p.1, ρ n p.2) ω) ⁻¹' (Set.pi (↑tA) CA ∩ Set.pi (↑tB) CB) := by
      rw [hAeq' n, hB'eq, Set.preimage_inter]
    have hR : (⋂ p ∈ tA, fA p) ∩ (⋂ p ∈ tB, fB p)
        = (fun ω p => X p ω) ⁻¹' (Set.pi (↑tA) CA ∩ Set.pi (↑tB) CB) := by
      rw [hAeq, hBeq, Set.preimage_inter]
    rw [hL, hR]
    rw [← Measure.map_apply (Measurable.of_eval fun p => hX _) (hcylA.inter hcylB),
      ← Measure.map_apply (Measurable.of_eval fun p => hX _) (hcylA.inter hcylB)]
    exact congrArg (fun m : Measure (ℕ × ℕ → α) => m (Set.pi (↑tA) CA ∩ Set.pi (↑tB) CB))
      (hexch.map_comp (fun p => (hX p).aemeasurable) (ρ n) measurable_id)

/-- **Corner-tail triviality implies joint dissociation.** A coordinatewise measurable, jointly
exchangeable array whose corner tail is `μ`-trivial is jointly dissociated. -/
theorem jointlyDissociated_of_forall_arrayTail_measure_eq_zero_or_one {X : ℕ × ℕ → Ω → α}
    [IsZeroOrProbabilityMeasure μ]
    (hX : ∀ p, Measurable (X p)) (hexch : JointlyExchangeable μ X)
    (htriv : ∀ s, MeasurableSet[arrayTail X] s → μ s = 0 ∨ μ s = 1) :
    JointlyDissociated μ X := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _
  · exact jointlyDissociated_iff.mpr fun e e' _ => by
      rw [indepFun_iff_measure_inter_preimage_eq_mul]; simp
  refine jointlyDissociated_iff.mpr fun e e' hd => ?_
  -- independence of the two block σ-algebras, from factorization on their generating π-systems
  have hindep : Indep (blockSigma X (Set.range e ×ˢ Set.range e))
      (blockSigma X (Set.range e' ×ˢ Set.range e')) μ := by
    refine IndepSets.indep (blockSigma_le _ fun p _ => hX p) (blockSigma_le _ fun p _ => hX p)
      (isPiSystem_piiUnionInter _ (fun p =>
        @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap (X p) inferInstance)) _)
      (isPiSystem_piiUnionInter _ (fun p =>
        @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap (X p) inferInstance)) _)
      (by rw [blockSigma_def]; exact (generateFrom_piiUnionInter_measurableSet _ _).symm)
      (by rw [blockSigma_def]; exact (generateFrom_piiUnionInter_measurableSet _ _).symm)
      ((IndepSets_iff _ _ _).2 fun A B hA hB =>
        measure_inter_eq_mul_of_cylinders hX hexch htriv hd hA hB)
  -- each sub-array map is measurable for the σ-algebra of its own block
  have hU : Measurable[blockSigma X (Set.range e ×ˢ Set.range e)]
      fun ω (p : ℕ × ℕ) => X (e p.1, e p.2) ω := by
    let : MeasurableSpace Ω := blockSigma X (Set.range e ×ˢ Set.range e)
    exact Measurable.of_eval fun p => measurable_blockSigma_of_mem (Z := X)
      (Set.mem_prod.2 ⟨Set.mem_range_self _, Set.mem_range_self _⟩)
  have hV : Measurable[blockSigma X (Set.range e' ×ˢ Set.range e')]
      fun ω (p : ℕ × ℕ) => X (e' p.1, e' p.2) ω := by
    let : MeasurableSpace Ω := blockSigma X (Set.range e' ×ˢ Set.range e')
    exact Measurable.of_eval fun p => measurable_blockSigma_of_mem (Z := X)
      (Set.mem_prod.2 ⟨Set.mem_range_self _, Set.mem_range_self _⟩)
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hindep hV.comap_le) hU.comap_le

/-- **Joint dissociation ↔ array-tail triviality** for a coordinatewise measurable jointly
exchangeable array under a zero-or-probability measure. -/
theorem jointlyDissociated_iff_forall_arrayTail_measure_eq_zero_or_one {X : ℕ × ℕ → Ω → α}
    [IsZeroOrProbabilityMeasure μ]
    (hX : ∀ p, Measurable (X p)) (hexch : JointlyExchangeable μ X) :
    JointlyDissociated μ X ↔ ∀ s, MeasurableSet[arrayTail X] s → μ s = 0 ∨ μ s = 1 :=
  ⟨fun h _ hs => h.measure_eq_zero_or_one_of_arrayTail 0 (fun p _ _ => hX p) hs,
   jointlyDissociated_of_forall_arrayTail_measure_eq_zero_or_one hX hexch⟩

end Probability

end TauCeti

end

end
