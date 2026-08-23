/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
-- Non-public: the permutations transported along injections, the permutation combining two
-- disjoint injections, and the reduction of an array law to its finite-dimensional marginals, are
-- used only inside proofs.
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Rectangular blocks of an exchangeable array

A **jointly** exchangeable array is invariant only under the diagonal reindexing
`(i, j) ↦ (σ i, σ j)`, so its rows are not exchangeable and none of the separately exchangeable
theory applies to it directly. This file supplies the standard device that repairs this: read the
array on a **rectangular block** `arrayBlock X e f`, whose `(i, j)`-entry is `X (e i, f j)`, along
two injections `e, f : ℕ → ℕ` **with disjoint ranges**. On such a block the single permutation the
array is invariant under has two independent halves — one permutation may be prescribed on the
range of `e` and another, unrelated one on the range of `f`, because a permutation of `ℕ` is free to
act differently on two disjoint sets — and the block is therefore *separately* exchangeable
(`JointlyExchangeable.separatelyExchangeable_arrayBlock`). Every theorem about separately
exchangeable arrays is then available for it; in particular de Finetti's theorem makes the rows of
the block conditionally i.i.d.

The block only sees the entries `X (e i, f j)`, so it omits the reverse-orientation entries
`X (f j, e i)`. Reading the two together as an array of pairs retains both orientations of the
selected rectangular cross-block, and the pair array is separately exchangeable
(`JointlyExchangeable.separatelyExchangeable_arrayBlockPair`). For a *symmetric* array the two
coordinates of each such pair agree.

## Main definitions

* `TauCeti.Probability.arrayBlock` — the rectangular block of an array along two index maps;
* `TauCeti.Probability.arrayBlockPair` — the same block, read together with its transpose.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.arrayBlock` — separate exchangeability passes to
  every block along injections, no disjointness needed;
* `TauCeti.Probability.JointlyExchangeable.arrayBlock_diag` — joint exchangeability passes to the
  diagonal blocks `arrayBlock X e e`;
* `TauCeti.Probability.JointlyExchangeable.separatelyExchangeable_arrayBlock` — **the block
  theorem**: a block of a jointly exchangeable array along injections with disjoint ranges is
  separately exchangeable;
* `TauCeti.Probability.JointlyExchangeable.separatelyExchangeable_arrayBlockPair` — the same for
  the block read together with its transpose;
* `TauCeti.Probability.JointlyExchangeable.separatelyExchangeable_arrayBlock_evenOdd` — the
  canonical instance, along the even and the odd indices;
* `TauCeti.Probability.not_separatelyExchangeable_arrayBlock_id_id` — the disjointness hypothesis
  is necessary;
* `TauCeti.Probability.JointlyExchangeable.map_arrayBlock_eq` — the block law does not depend on
  the chosen pair of index maps;
* `TauCeti.Probability.JointlyExchangeable.map_arrayBlockPair_eq` — the corresponding canonical-law
  theorem for the pair-valued block;
* `TauCeti.Probability.JointlyExchangeable.conditionallyIID_arrayRow_arrayBlock` and
  `TauCeti.Probability.JointlyExchangeable.conditionallyIID_arrayRow_arrayBlockPair` — de Finetti
  for the rows of a block of a jointly exchangeable array.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, *Representations for partially exchangeable arrays of random variables*, Journal of
  Multivariate Analysis 11 (1981), 581–598.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*}

/-! ## Blocks of an array -/

/-- The rectangular block of the array `X` along the index maps `e` and `f`: its `(i, j)`-entry is
the `(e i, f j)`-entry of `X`. -/
def arrayBlock (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α :=
  fun p => X (e p.1, f p.2)

@[simp]
theorem arrayBlock_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) :
    arrayBlock X e f p = X (e p.1, f p.2) :=
  (rfl)

/-- The rectangular block of `X` along `e` and `f`, read together with its transpose: its
`(i, j)`-entry is the pair of the `(e i, f j)`-entry and the `(f j, e i)`-entry of `X`. -/
def arrayBlockPair (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α × α :=
  fun p ω => (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω)

@[simp]
theorem arrayBlockPair_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) (ω : Ω) :
    arrayBlockPair X e f p ω = (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω) :=
  (rfl)

/-- The block along the identity index maps is the array itself. -/
@[simp]
theorem arrayBlock_id_id (X : ℕ × ℕ → Ω → α) : arrayBlock X id id = X :=
  (rfl)

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

theorem aemeasurable_arrayBlock (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlock X e f p) μ :=
  hX _

theorem aemeasurable_arrayBlockPair (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlockPair X e f p) μ :=
  (hX _).prodMk (hX _)

/-- Reading a block off an array's sample path is measurable. -/
theorem measurable_blockReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x (e p.1, f p.2) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Reading a block together with its transpose off an array's sample path is measurable. -/
theorem measurable_blockPairReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => (x (e p.1, f p.2), x (f p.2, e p.1)) :=
  measurable_pi_lambda _ fun _ => (measurable_pi_apply _).prodMk (measurable_pi_apply _)

/-! ## Blocks inherit the symmetry of the array -/

/-- **Separate exchangeability passes to every block along injections.** No relation between the
two ranges is needed. -/
theorem SeparatelyExchangeable.arrayBlock (h : SeparatelyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) (hf : Function.Injective f) :
    SeparatelyExchangeable μ (arrayBlock X e f) := by
  refine separatelyExchangeable_iff.mpr fun σ τ => ?_
  let ι : ℕ ↪ ℕ := ⟨e, he⟩
  let κ : ℕ ↪ ℕ := ⟨f, hf⟩
  have key := h.map_comp hX (σ.viaEmbedding ι) (τ.viaEmbedding κ)
    (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => x (ι p.1, κ p.2))
    (measurable_blockReadOff ι κ)
  change (μ.map fun ω (p : ℕ × ℕ) => X ((σ.viaEmbedding ι) (ι p.1),
    (τ.viaEmbedding κ) (κ p.2)) ω) = μ.map fun ω (p : ℕ × ℕ) => X (ι p.1, κ p.2) ω at key
  have hσ : ∀ i, (σ.viaEmbedding ι) (ι i) = ι (σ i) :=
    fun i => Equiv.Perm.viaEmbedding_apply (ι := ι) σ i
  have hτ : ∀ j, (τ.viaEmbedding κ) (κ j) = κ (τ j) :=
    fun j => Equiv.Perm.viaEmbedding_apply (ι := κ) τ j
  have hfun : (fun ω (p : ℕ × ℕ) => X ((σ.viaEmbedding ι) (ι p.1),
      (τ.viaEmbedding κ) (κ p.2)) ω) = fun ω (p : ℕ × ℕ) => X (ι (σ p.1), κ (τ p.2)) ω := by
    funext ω p
    exact congrArg (fun q => X q ω) (Prod.ext (hσ p.1) (hτ p.2))
  have key' := (congrArg (fun g => Measure.map g μ) hfun).symm.trans key
  simpa [ι, κ, arrayBlock] using key'

/-- **Joint exchangeability passes to diagonal blocks along an injection.** -/
theorem JointlyExchangeable.arrayBlock_diag (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) :
    JointlyExchangeable μ (arrayBlock X e e) := by
  refine jointlyExchangeable_iff.mpr fun σ => ?_
  let ι : ℕ ↪ ℕ := ⟨e, he⟩
  have key := h.map_comp hX (σ.viaEmbedding ι)
    (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => x (ι p.1, ι p.2))
    (measurable_blockReadOff ι ι)
  change (μ.map fun ω (p : ℕ × ℕ) => X ((σ.viaEmbedding ι) (ι p.1),
    (σ.viaEmbedding ι) (ι p.2)) ω) = μ.map fun ω (p : ℕ × ℕ) => X (ι p.1, ι p.2) ω at key
  have hσ : ∀ i, (σ.viaEmbedding ι) (ι i) = ι (σ i) :=
    fun i => Equiv.Perm.viaEmbedding_apply (ι := ι) σ i
  have hfun : (fun ω (p : ℕ × ℕ) => X ((σ.viaEmbedding ι) (ι p.1),
      (σ.viaEmbedding ι) (ι p.2)) ω) = fun ω (p : ℕ × ℕ) => X (ι (σ p.1), ι (σ p.2)) ω := by
    funext ω p
    exact congrArg (fun q => X q ω) (Prod.ext (hσ p.1) (hσ p.2))
  have key' := (congrArg (fun g => Measure.map g μ) hfun).symm.trans key
  simpa [ι, arrayBlock] using key'

/-- **A block of a jointly exchangeable array along injections with disjoint ranges is separately
exchangeable.**

This makes separately exchangeable results, including de Finetti's theorem for the rows, available
to the selected block. -/
theorem JointlyExchangeable.separatelyExchangeable_arrayBlock (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    SeparatelyExchangeable μ (arrayBlock X e f) := by
  refine separatelyExchangeable_iff.mpr fun σ τ => ?_
  obtain ⟨ρ, hρe, hρf⟩ := exists_perm_apply_eq_of_disjoint_range he hf hd σ τ
  have key := h.map_comp hX ρ (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => x (e p.1, f p.2))
    (measurable_blockReadOff e f)
  simp only [hρe, hρf] at key
  simpa only [arrayBlock_apply] using key

/-- **A block of a jointly exchangeable array, read in both orientations, is separately
exchangeable.** Its `(i, j)`-entry is `(X (e i, f j), X (f j, e i))`. -/
theorem JointlyExchangeable.separatelyExchangeable_arrayBlockPair (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    SeparatelyExchangeable μ (arrayBlockPair X e f) := by
  refine separatelyExchangeable_iff.mpr fun σ τ => ?_
  obtain ⟨ρ, hρe, hρf⟩ := exists_perm_apply_eq_of_disjoint_range he hf hd σ τ
  have key := h.map_comp hX ρ
    (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => (x (e p.1, f p.2), x (f p.2, e p.1)))
    (measurable_blockPairReadOff e f)
  simp only [hρe, hρf] at key
  simpa only [arrayBlockPair_apply] using key

/-! ## The canonical block, along the even and the odd indices -/

-- The parity facts instantiating the canonical block below; they carry no exchangeability content.
private theorem injective_two_mul : Function.Injective fun i : ℕ => 2 * i := by
  intro a b h
  have h' : 2 * a = 2 * b := h
  omega

private theorem injective_two_mul_add_one : Function.Injective fun j : ℕ => 2 * j + 1 := by
  intro a b h
  have h' : 2 * a + 1 = 2 * b + 1 := h
  omega

private theorem disjoint_range_two_mul :
    Disjoint (Set.range fun i : ℕ => 2 * i) (Set.range fun j : ℕ => 2 * j + 1) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  have hj' : 2 * j + 1 = 2 * i := hj
  omega

/-- **The canonical separately exchangeable block of a jointly exchangeable array**: read the rows
along the even indices and the columns along the odd ones. Any pair of injections with disjoint
ranges would do; this one exists without further data, so it is the block a consumer with no
preferred index sets should use. -/
theorem JointlyExchangeable.separatelyExchangeable_arrayBlock_evenOdd
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ (arrayBlock X (fun i => 2 * i) fun j => 2 * j + 1) :=
  h.separatelyExchangeable_arrayBlock hX injective_two_mul injective_two_mul_add_one
    disjoint_range_two_mul

/-- **The canonical block of pairs of a jointly exchangeable array.** -/
theorem JointlyExchangeable.separatelyExchangeable_arrayBlockPair_evenOdd
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ (arrayBlockPair X (fun i => 2 * i) fun j => 2 * j + 1) :=
  h.separatelyExchangeable_arrayBlockPair hX injective_two_mul injective_two_mul_add_one
    disjoint_range_two_mul

/-- **The disjointness hypothesis of `JointlyExchangeable.separatelyExchangeable_arrayBlock` cannot
be omitted.** With identity index maps, the diagonal-indicator array gives a counterexample. -/
theorem not_separatelyExchangeable_arrayBlock_id_id (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ¬SeparatelyExchangeable μ (arrayBlock (diagIndicatorArray Ω) id id) := by
  rw [arrayBlock_id_id]
  exact not_separatelyExchangeable_diagIndicatorArray μ

/-! ## The block law is canonical -/

/-- **The law of a block does not depend on the chosen pair of index maps.** Any two pairs of
injections with disjoint ranges give the same law; in particular, the canonical even-odd block
computes it. -/
theorem JointlyExchangeable.map_arrayBlock_eq [IsFiniteMeasure μ] {e' f' : ℕ → ℕ}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    (μ.map fun ω p => arrayBlock X e f p ω) = μ.map fun ω p => arrayBlock X e' f' p ω := by
  have hmeas : ∀ u v : ℕ → ℕ, AEMeasurable (fun ω p => arrayBlock X u v p ω) μ :=
    fun _ _ => aemeasurable_pi_lambda _ fun _ => hX _
  refine (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (hmeas e f) (hmeas e' f')).mpr fun I => ?_
  -- Every index occurring in `I` is below `n`, so a permutation matching the two pairs of index
  -- maps below `n` already matches the marginal.
  obtain ⟨n, hbound⟩ : ∃ n : ℕ, ∀ p ∈ I, p.1 < n ∧ p.2 < n := by
    refine ⟨(I.sup fun p => max p.1 p.2) + 1, fun p hp => ?_⟩
    have hle := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    omega
  have hg₁ : Function.Injective
      (Sum.elim (fun i : Fin n => e i.val) fun j : Fin n => f j.val) :=
    (he.comp Fin.val_injective).sumElim (hf.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  have hg₂ : Function.Injective
      (Sum.elim (fun i : Fin n => e' i.val) fun j : Fin n => f' j.val) :=
    (he'.comp Fin.val_injective).sumElim (hf'.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd' ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hg₁ hg₂
  have hσe : ∀ i : Fin n, σ (e i.val) = e' i.val := fun i => hσ (Sum.inl i)
  have hσf : ∀ j : Fin n, σ (f j.val) = f' j.val := fun j => hσ (Sum.inr j)
  have key := h.map_comp hX σ
    (F := fun x : ℕ × ℕ → α => I.restrict fun p : ℕ × ℕ => x (e p.1, f p.2))
    ((Finset.measurable_restrict I).comp (measurable_blockReadOff e f))
  have hrew : ∀ ω : Ω, (I.restrict fun p : ℕ × ℕ => X (σ (e p.1), σ (f p.2)) ω)
      = I.restrict fun p : ℕ × ℕ => X (e' p.1, f' p.2) ω := by
    intro ω
    funext p
    obtain ⟨hp₁, hp₂⟩ := hbound p.1 p.2
    exact congrArg (fun q => X q ω)
      (Prod.ext (hσe ⟨(p : ℕ × ℕ).1, hp₁⟩) (hσf ⟨(p : ℕ × ℕ).2, hp₂⟩))
  exact key.symm.trans (congrArg (fun g => Measure.map g μ) (funext hrew))

/-- **The law of a pair-valued block does not depend on the chosen pair of index maps.** Any two
pairs of injections with disjoint ranges give the same law. -/
theorem JointlyExchangeable.map_arrayBlockPair_eq [IsFiniteMeasure μ] {e' f' : ℕ → ℕ}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    (μ.map fun ω p => arrayBlockPair X e f p ω) =
      μ.map fun ω p => arrayBlockPair X e' f' p ω := by
  have hmeas : ∀ u v : ℕ → ℕ, AEMeasurable (fun ω p => arrayBlockPair X u v p ω) μ :=
    fun _ _ => aemeasurable_pi_lambda _ fun _ => (hX _).prodMk (hX _)
  refine (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (hmeas e f) (hmeas e' f')).mpr fun I => ?_
  obtain ⟨n, hbound⟩ : ∃ n : ℕ, ∀ p ∈ I, p.1 < n ∧ p.2 < n := by
    refine ⟨(I.sup fun p => max p.1 p.2) + 1, fun p hp => ?_⟩
    have hle := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    omega
  have hg₁ : Function.Injective
      (Sum.elim (fun i : Fin n => e i.val) fun j : Fin n => f j.val) :=
    (he.comp Fin.val_injective).sumElim (hf.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  have hg₂ : Function.Injective
      (Sum.elim (fun i : Fin n => e' i.val) fun j : Fin n => f' j.val) :=
    (he'.comp Fin.val_injective).sumElim (hf'.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd' ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hg₁ hg₂
  have hσe : ∀ i : Fin n, σ (e i.val) = e' i.val := fun i => hσ (Sum.inl i)
  have hσf : ∀ j : Fin n, σ (f j.val) = f' j.val := fun j => hσ (Sum.inr j)
  have key := h.map_comp hX σ
    (F := fun x : ℕ × ℕ → α =>
      I.restrict fun p : ℕ × ℕ => (x (e p.1, f p.2), x (f p.2, e p.1)))
    ((Finset.measurable_restrict I).comp (measurable_blockPairReadOff e f))
  have hrew : ∀ ω : Ω,
      (I.restrict fun p : ℕ × ℕ =>
        (X (σ (e p.1), σ (f p.2)) ω, X (σ (f p.2), σ (e p.1)) ω)) =
        I.restrict fun p : ℕ × ℕ => (X (e' p.1, f' p.2) ω, X (f' p.2, e' p.1) ω) := by
    intro ω
    funext p
    obtain ⟨hp₁, hp₂⟩ := hbound p.1 p.2
    exact Prod.ext
      (congrArg (fun q => X q ω)
        (Prod.ext (hσe ⟨(p : ℕ × ℕ).1, hp₁⟩) (hσf ⟨(p : ℕ × ℕ).2, hp₂⟩)))
      (congrArg (fun q => X q ω)
        (Prod.ext (hσf ⟨(p : ℕ × ℕ).2, hp₂⟩) (hσe ⟨(p : ℕ × ℕ).1, hp₁⟩)))
  exact key.symm.trans (congrArg (fun g => Measure.map g μ) (funext hrew))

/-! ## De Finetti for the rows of a block -/

/-- **De Finetti's theorem for the rows of a block of a jointly exchangeable array.** Over a
nonempty standard Borel state space, the rows of a block along injections with disjoint ranges are
conditionally i.i.d. as random elements of path space. -/
theorem JointlyExchangeable.conditionallyIID_arrayRow_arrayBlock [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    ConditionallyIID μ (arrayRow (arrayBlock X e f)) :=
  (h.separatelyExchangeable_arrayBlock hX he hf hd).conditionallyIID_arrayRow
    (aemeasurable_arrayBlock hX)

/-- **De Finetti's theorem for the rows of a block of pairs.** The conclusion simultaneously
describes both orientations of the selected rectangular cross-block. -/
theorem JointlyExchangeable.conditionallyIID_arrayRow_arrayBlockPair [StandardBorelSpace α]
    [Nonempty α] [IsFiniteMeasure μ] (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    ConditionallyIID μ (arrayRow (arrayBlockPair X e f)) :=
  (h.separatelyExchangeable_arrayBlockPair hX he hf hd).conditionallyIID_arrayRow
    (aemeasurable_arrayBlockPair hX)

end Probability

end TauCeti
