/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Decomposition
public import TauCeti.Order.CompactlyGenerated

/-!
# Strictness of a morphism of mixed Hodge structures

A morphism of mixed Hodge structures is **strict**: an element of the target that lies in a step
of a filtration *and* in the image of the morphism is already the image of an element of the
corresponding step of the source. Filtration-preserving maps are not strict in general — this is
the theorem that makes the category of mixed Hodge structures abelian — and the proof is Deligne's
bigrading.

Both filtrations are recovered from the bigrading `I^{p,q}`
(`TauCeti.Hodge.MixedHodgeStructure.WC_eq_iSup_deligneSplitting` and
`TauCeti.Hodge.MixedHodgeStructure.F_eq_iSup_deligneSplitting`) as suprema of the pieces over a set
of bidegrees, a morphism carries `I^{p,q}` into `I^{p,q}`
(`TauCeti.Hodge.MixedHodgeStructure.Hom.map_deligneSplitting_le`), and the pieces of the target are
independent. Strictness for both filtrations at once is then the lattice statement that in a
family `B ≤ A` with `A` independent, the sum of the `B` over *all* indices meets the sum of the `A`
over a set `S` of indices in exactly the sum of the `B` over `S`: an element of the intersection
has no component of the target's bigrading outside `S`, so the source element producing it may be
truncated to its own components in `S`.

The weight filtration is a rational datum, and its strictness is stated rationally. It descends
from the complex statement because `ℂ` is faithfully flat over `ℚ`, so an inclusion of rational
subspaces can be tested after complexification
(`TauCeti.Hodge.rationalToComplexSubmodule_le_iff`); only the trivial half of the compatibility of
complexification with intersections is needed.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.Hom.range_inf_iSup_deligneSplittingFamily_eq_map_iSup`:
  strictness against an arbitrary set of bidegrees.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.range_inf_F_eq_map_F`: **strictness for the Hodge
  filtration**, `im f ∩ F'^p = f(F^p)`.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.range_inf_WQ_eq_map_WQ`: **strictness for the weight
  filtration**, `im f ∩ W'_k = f(W_k)`, rationally.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.range_inf_WC_eq_map_WC`: the complexification of the
  latter.

## References

Deligne, *Théorie de Hodge II*, 1.2.10 and 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*,
Theorem 3.13. This is the milestone of Layer L2 of the Hodge structures roadmap.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

namespace MixedHodgeStructure.Hom

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ} {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}

/-! ### The image of a morphism, bigraded -/

/-- The image of a morphism of mixed Hodge structures is the sum of the images of the bigrading
pieces of its source: the bigrading of the source spans. -/
theorem range_eq_iSup_map_deligneSplittingFamily (f : Hom source target) :
    LinearMap.range f.toLinearMap =
      ⨆ pq : ℤ × ℤ, (source.deligneSplittingFamily pq).map f.toLinearMap := by
  rw [← Submodule.map_iSup, source.iSup_deligneSplittingFamily_eq_top, Submodule.map_top]

/-- **Strictness against a set of bidegrees.** The image of a morphism meets the sum of the
target's bigrading pieces over the bidegrees satisfying `P` in exactly the image of the
corresponding sum for the source.

Both filtrations of a mixed Hodge structure are sums of bigrading pieces over such a set, so this
single statement carries every strictness assertion below. -/
theorem range_inf_iSup_deligneSplittingFamily_eq_map_iSup (f : Hom source target)
    (P : ℤ × ℤ → Prop) :
    LinearMap.range f.toLinearMap ⊓ ⨆ (pq) (_ : P pq), target.deligneSplittingFamily pq =
      (⨆ (pq) (_ : P pq), source.deligneSplittingFamily pq).map f.toLinearMap := by
  rw [f.range_eq_iSup_map_deligneSplittingFamily, inf_comm,
    TauCeti.iSupIndep.iSup₂_inf_iSup_eq_iSup₂ (A := target.deligneSplittingFamily)
      (B := fun pq ↦ (source.deligneSplittingFamily pq).map f.toLinearMap)
      target.iSupIndep_deligneSplittingFamily
      (fun pq ↦ by
        simpa only [deligneSplittingFamily_apply] using
          f.map_deligneSplitting_le pq.1 pq.2) P]
  simp only [Submodule.map_iSup]

/-! ### Strictness -/

/-- **Strictness of a morphism of mixed Hodge structures for the Hodge filtration.** A complex
vector lying both in the image of `f` and in the target's Hodge step `F^p` is the image of a
vector of the source's `F^p`.

The two filtration steps are the sums of the bigrading pieces of first index at least `p`, and `f`
respects the bigrading, so a preimage may be truncated to its components of first index at least
`p` without changing its image. -/
@[simp] theorem range_inf_F_eq_map_F (f : Hom source target) (p : ℤ) :
    LinearMap.range f.toLinearMap ⊓ target.F p = (source.F p).map f.toLinearMap := by
  simpa only [deligneSplittingFamily_apply, ← target.F_eq_iSup_deligneSplitting p,
    ← source.F_eq_iSup_deligneSplitting p] using
    f.range_inf_iSup_deligneSplittingFamily_eq_map_iSup fun pq ↦ p ≤ pq.1

/-- **Strictness of a morphism of mixed Hodge structures for the complexified weight
filtration.** -/
@[simp] theorem range_inf_WC_eq_map_WC (f : Hom source target) (k : ℤ) :
    LinearMap.range f.toLinearMap ⊓ target.WC k = (source.WC k).map f.toLinearMap := by
  simpa only [deligneSplittingFamily_apply, ← target.WC_eq_iSup_deligneSplitting k,
    ← source.WC_eq_iSup_deligneSplitting k] using
    f.range_inf_iSup_deligneSplittingFamily_eq_map_iSup fun pq ↦ pq.1 + pq.2 ≤ k

/-- **Strictness of a morphism of mixed Hodge structures for the weight filtration.** A rational
vector lying both in the image of `f` and in the target's weight step `W_k` is the image of a
vector of the source's `W_k`.

The weight filtration is rational, so this is the form the milestone takes; it descends from the
complex statement because complexification of rational subspaces reflects inclusions. Only the
inclusion `(A ∩ B)_ℂ ≤ A_ℂ ∩ B_ℂ` is used, which is monotonicity. -/
@[simp] theorem range_inf_WQ_eq_map_WQ (f : Hom source target) (k : ℤ) :
    LinearMap.range f.toRatLinearMap ⊓ target.WQ k = (source.WQ k).map f.toRatLinearMap := by
  refine le_antisymm ?_ (le_inf LinearMap.map_le_range (f.map_WQ_le k))
  rw [← rationalToComplexSubmodule_le_iff h'ℚ h'ℂ]
  have hrange : rationalToComplexSubmodule h'ℚ h'ℂ (LinearMap.range f.toRatLinearMap) =
      LinearMap.range f.toLinearMap := by
    rw [← Submodule.map_top f.toRatLinearMap, ← map_rationalToComplexSubmodule hℚ hℂ h'ℚ h'ℂ,
      rationalToComplexSubmodule_top, Submodule.map_top, toLinearMap_def]
  have hmap : rationalToComplexSubmodule h'ℚ h'ℂ ((source.WQ k).map f.toRatLinearMap) =
      (source.WC k).map f.toLinearMap := by
    rw [← map_rationalToComplexSubmodule hℚ hℂ h'ℚ h'ℂ, WC_def, toLinearMap_def]
  rw [hmap, ← f.range_inf_WC_eq_map_WC k, WC_def, ← hrange]
  exact le_inf (rationalToComplexSubmodule_mono h'ℚ h'ℂ inf_le_left)
    (rationalToComplexSubmodule_mono h'ℚ h'ℂ inf_le_right)

end MixedHodgeStructure.Hom

end TauCeti.Hodge
