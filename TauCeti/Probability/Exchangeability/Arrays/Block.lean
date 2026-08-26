/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
-- Non-public: the permutation realizing one prescribed permutation along an injection, the one
-- realizing two along injections with disjoint ranges, and the reduction of an array law to its
-- finite-dimensional marginals, are used only inside proofs.
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Rectangular blocks of an exchangeable array

Joint exchangeability alone guarantees only invariance under the diagonal reindexing
`(i, j) ↦ (σ i, σ j)`, so the rows of a jointly exchangeable array need not be exchangeable and the
separately exchangeable theory does not apply to it in general. This file supplies the standard
device that repairs this: read the array on a **rectangular block** `arrayBlock X e f`, whose
`(i, j)`-entry is `X (e i, f j)`, along two injections `e, f : ℕ → ℕ` **with disjoint ranges**. On
such a block the single permutation the array is invariant under has two independent halves — one
permutation may be prescribed on the range of `e` and another, unrelated one on the range of `f`,
because a permutation of `ℕ` is free to act differently on two disjoint sets — and the block is
therefore *separately* exchangeable
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
* `TauCeti.Probability.not_separatelyExchangeable_arrayBlock_diagIndicatorArray` — the disjointness
  hypothesis is necessary;
* `TauCeti.Probability.JointlyExchangeable.map_arrayBlock_eq` — the block law does not depend on
  the chosen pair of index maps;
* `TauCeti.Probability.JointlyExchangeable.map_arrayBlockPair_eq` — the corresponding canonical-law
  theorem for the pair-valued block;

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

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

/-- Entrywise measurability passes to a block: the `p`-entry of `arrayBlock X e f` is the
`(e p.1, f p.2)`-entry of `X`. A consumer cannot read this off the hypothesis on its own, since
`arrayBlock` does not unfold outside this file. -/
theorem aemeasurable_arrayBlock (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlock X e f p) μ :=
  hX _

/-- Entrywise measurability passes to a block read together with its transpose: the `p`-entry of
`arrayBlockPair X e f` pairs two entries of `X`. -/
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
  obtain ⟨ρ, hρe⟩ := exists_perm_apply_eq he σ
  obtain ⟨ρ', hρf⟩ := exists_perm_apply_eq hf τ
  have key := h.map_comp hX ρ ρ' (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => x (e p.1, f p.2))
    (measurable_blockReadOff e f)
  simp only [hρe, hρf] at key
  simpa only [arrayBlock_apply] using key

/-- **Joint exchangeability passes to diagonal blocks along an injection.** -/
theorem JointlyExchangeable.arrayBlock_diag (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) :
    JointlyExchangeable μ (arrayBlock X e e) := by
  refine jointlyExchangeable_iff.mpr fun σ => ?_
  obtain ⟨ρ, hρe⟩ := exists_perm_apply_eq he σ
  have key := h.map_comp hX ρ (F := fun (x : ℕ × ℕ → α) (p : ℕ × ℕ) => x (e p.1, e p.2))
    (measurable_blockReadOff e e)
  simp only [hρe] at key
  simpa only [arrayBlock_apply] using key

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
private theorem injective_two_mul : Function.Injective fun i : ℕ => 2 * i :=
  mul_right_injective₀ two_ne_zero

private theorem injective_two_mul_add_one : Function.Injective fun j : ℕ => 2 * j + 1 :=
  (add_left_injective 1).comp injective_two_mul

private theorem disjoint_range_two_mul :
    Disjoint (Set.range fun i : ℕ => 2 * i) (Set.range fun j : ℕ => 2 * j + 1) := by
  simp [Set.disjoint_left]

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
be omitted.** Reading both axes along one and the same injection — the extreme case of overlapping
ranges — the diagonal-indicator array gives a counterexample: the block is again the
diagonal-indicator array, whose rows are not exchangeable. -/
theorem not_separatelyExchangeable_arrayBlock_diagIndicatorArray (μ : Measure Ω)
    [IsProbabilityMeasure μ] (he : Function.Injective e) :
    ¬SeparatelyExchangeable μ (arrayBlock (diagIndicatorArray Ω) e e) := by
  have hblock : arrayBlock (diagIndicatorArray Ω) e e = diagIndicatorArray Ω := by
    funext p ω
    simp [he.eq_iff]
  rw [hblock]
  exact not_separatelyExchangeable_diagIndicatorArray μ

/-! ## The block law is canonical -/

/-- **Below any bound, one permutation carries a pair of injections with disjoint ranges to
another such pair.** The agreement is only finite by necessity: a single permutation need not
carry one pair of index maps to another globally, since their ranges may have complements of
different sizes, as `(2 · , 2 · + 1)` and `(4 · , 4 · + 1)` do. -/
private theorem exists_perm_apply_eq_of_lt {e' f' : ℕ → ℕ} (n : ℕ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    ∃ σ : Equiv.Perm ℕ, (∀ i < n, σ (e i) = e' i) ∧ ∀ j < n, σ (f j) = f' j := by
  have hg : Function.Injective (Sum.elim (fun i : Fin n => e i.val) fun j : Fin n => f j.val) :=
    (he.comp Fin.val_injective).sumElim (hf.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  have hg' : Function.Injective (Sum.elim (fun i : Fin n => e' i.val) fun j : Fin n => f' j.val) :=
    (he'.comp Fin.val_injective).sumElim (hf'.comp Fin.val_injective)
      fun a b hab => Set.disjoint_left.mp hd' ⟨a.val, rfl⟩ ⟨b.val, hab.symm⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hg hg'
  exact ⟨σ, fun i hi => hσ (Sum.inl ⟨i, hi⟩), fun j hj => hσ (Sum.inr ⟨j, hj⟩)⟩

/-- The common argument behind the two canonical-law theorems below, stated for an arbitrary
read-off `B u v` of the array's sample path along the index maps `u` and `v`. Besides being
measurable, `B` has to commute with a permutation of both axes (`hBperm`) and to read the entry at
`p` through the index maps only at `p.1` and `p.2` (`hBapply`); the block and the block of pairs
both satisfy these by `rfl` and by congruence.

The two laws are compared one finite-dimensional marginal at a time, because a single permutation
matches the two pairs of index maps only below a finite bound (`exists_perm_apply_eq_of_lt`). -/
private theorem map_blockReadOff_eq {β : Type*} [MeasurableSpace β] [IsFiniteMeasure μ]
    {e' f' : ℕ → ℕ} {B : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ × ℕ → α) → ℕ × ℕ → β}
    (hBmeas : ∀ u v, Measurable (B u v))
    (hBperm : ∀ (σ : Equiv.Perm ℕ) (u v : ℕ → ℕ) (x : ℕ × ℕ → α),
      (B u v fun q => x (σ q.1, σ q.2)) = B (fun i => σ (u i)) (fun j => σ (v j)) x)
    (hBapply : ∀ (u v u' v' : ℕ → ℕ) (x : ℕ × ℕ → α) (p : ℕ × ℕ),
      u p.1 = u' p.1 → v p.2 = v' p.2 → B u v x p = B u' v' x p)
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    (μ.map fun ω => B e f fun q => X q ω) = μ.map fun ω => B e' f' fun q => X q ω := by
  have hmeas : ∀ u v : ℕ → ℕ, AEMeasurable (fun ω => B u v fun q => X q ω) μ :=
    fun u v => (hBmeas u v).comp_aemeasurable (aemeasurable_pi_lambda _ hX)
  refine (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
    (hmeas e f) (hmeas e' f')).mpr fun I => ?_
  -- Every index occurring in `I` is below `n`, so a permutation matching the two pairs of index
  -- maps below `n` already matches the marginal.
  obtain ⟨n, hbound⟩ : ∃ n : ℕ, ∀ p ∈ I, p.1 < n ∧ p.2 < n := by
    refine ⟨(I.sup fun p => max p.1 p.2) + 1, fun p hp => ?_⟩
    have hle := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    omega
  obtain ⟨σ, hσe, hσf⟩ := exists_perm_apply_eq_of_lt n he hf hd he' hf' hd'
  have key := h.map_comp hX σ (F := fun x : ℕ × ℕ → α => I.restrict (B e f x))
    ((Finset.measurable_restrict I).comp (hBmeas e f))
  have hrew : ∀ ω : Ω, (I.restrict (B e f fun q => X (σ q.1, σ q.2) ω))
      = I.restrict (B e' f' fun q => X q ω) := by
    intro ω
    funext p
    obtain ⟨hp₁, hp₂⟩ := hbound p.1 p.2
    exact (congrFun (hBperm σ e f fun q => X q ω) _).trans
      (hBapply _ _ _ _ _ _ (hσe _ hp₁) (hσf _ hp₂))
  exact key.symm.trans (congrArg (fun g => Measure.map g μ) (funext hrew))

/-- **The law of a block does not depend on the chosen pair of index maps.** Any two pairs of
injections with disjoint ranges give the same law; in particular, the canonical even-odd block
computes it. -/
theorem JointlyExchangeable.map_arrayBlock_eq [IsFiniteMeasure μ] {e' f' : ℕ → ℕ}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    (μ.map fun ω p => arrayBlock X e f p ω) = μ.map fun ω p => arrayBlock X e' f' p ω :=
  map_blockReadOff_eq (B := fun u v x p => x (u p.1, v p.2)) measurable_blockReadOff
    (fun _ _ _ _ => rfl) (fun _ _ _ _ x _ hu hv => congrArg x (Prod.ext hu hv))
    h hX he hf hd he' hf' hd'

/-- **The law of a pair-valued block does not depend on the chosen pair of index maps.** Any two
pairs of injections with disjoint ranges give the same law. -/
theorem JointlyExchangeable.map_arrayBlockPair_eq [IsFiniteMeasure μ] {e' f' : ℕ → ℕ}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f))
    (he' : Function.Injective e') (hf' : Function.Injective f')
    (hd' : Disjoint (Set.range e') (Set.range f')) :
    (μ.map fun ω p => arrayBlockPair X e f p ω) =
      μ.map fun ω p => arrayBlockPair X e' f' p ω :=
  map_blockReadOff_eq (B := fun u v x p => (x (u p.1, v p.2), x (v p.2, u p.1)))
    measurable_blockPairReadOff (fun _ _ _ _ => rfl)
    (fun _ _ _ _ x _ hu hv =>
      Prod.ext (congrArg x (Prod.ext hu hv)) (congrArg x (Prod.ext hv hu)))
    h hX he hf hd he' hf' hd'

end Probability

end TauCeti
