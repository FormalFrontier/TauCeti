/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Sigma
public import Mathlib.Probability.Independence.ZeroOne
-- Non-public: used only inside proofs.
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# The Hewitt–Savage zero-one law

Work in progress.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

/-- The finitely supported permutation of `ℕ` that swaps the block `[0, N)` with `[N, 2N)`
pointwise and fixes everything from `2 * N` on. -/
def blockSwap (N : ℕ) : Equiv.Perm ℕ :=
  Equiv.Perm.viaFintypeEmbedding
    (((finSumFinEquiv (m := N) (n := N)).symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv)
    ⟨Fin.val, Fin.val_injective⟩

theorem blockSwap_apply_of_lt {N i : ℕ} (hi : i < N) : blockSwap N i = N + i := by
  have key : ((finSumFinEquiv.symm.trans (Equiv.sumComm (Fin N) (Fin N))).trans finSumFinEquiv)
      (Fin.castAdd N ⟨i, hi⟩) = Fin.natAdd N ⟨i, hi⟩ := by
    rw [Equiv.trans_apply, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.castAdd N ⟨i, hi⟩) = i := rfl
  rw [blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, key]
  rfl

theorem blockSwap_apply_of_le {N n : ℕ} (hn : N + N ≤ n) : blockSwap N n = n := by
  refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact absurd j.isLt (not_lt.mpr hn)

/-- `blockSwap N` carries any index block inside `[0, N)` off itself: the moved copy lands in
`[N, 2N)`. This is the disjointness the independence step consumes. -/
theorem disjoint_map_blockSwap {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range N) :
    Disjoint F (F.map (Equiv.toEmbedding (blockSwap N))) := by
  rw [Finset.disjoint_left]
  intro a haF hamem
  obtain ⟨b, hbF, hb⟩ := Finset.mem_map.mp hamem
  have hbN : b < N := Finset.mem_range.mp (hF hbF)
  have haN : a < N := Finset.mem_range.mp (hF haF)
  rw [Equiv.coe_toEmbedding, blockSwap_apply_of_lt hbN] at hb
  omega

theorem blockSwap_finite_support (N : ℕ) :
    (MulAction.fixedBy ℕ (blockSwap N))ᶜ.Finite := by
  refine Set.Finite.subset (Set.finite_Iio (N + N)) ?_
  intro n hn
  by_contra hmem
  exact hn (blockSwap_apply_of_le (not_lt.mp hmem))

end Probability

end TauCeti
