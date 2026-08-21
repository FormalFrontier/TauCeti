/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Order.Filter.CountableInter

/-!
# Countable group actions: almost invariant events versus invariant events

Mathlib's `ErgodicSMul` is phrased with **almost** invariant events: an action is ergodic when
every measurable `s` with `(g • ·) ⁻¹' s =ᵐ[μ] s` for all `g` is null or conull.  Concrete
σ-algebras of invariant events — the invariant σ-algebra of a map, or the exchangeable σ-algebra
of path space — instead collect the **exactly** invariant events, those with
`(g • ·) ⁻¹' s = s`.

For a **countable** group the two formulations agree up to null sets: the saturation
`⋃ g, g • s` is exactly invariant and, being a countable union of sets each almost equal to `s`,
almost equal to `s`.  This file records that saturation
(`exists_smul_invariant_ae_eq`) and the resulting criterion
(`ergodicSMul_of_forall_smul_invariant`): to prove a countable action ergodic it suffices to
handle exactly invariant events.

Countability is essential and is not a technical convenience: the saturation of an almost
invariant set by an uncountable group need not be measurable, let alone almost equal to the
original set.

No measure invariance is needed for the saturation itself; `SMulInvariantMeasure` enters only
because `ErgodicSMul` extends it.
-/

public section

open Filter MeasureTheory Set

open scoped Pointwise

namespace TauCeti

namespace MeasureTheory

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] {μ : Measure X}

/-- **An almost invariant event of a countable group action is almost equal to an exactly
invariant one.**  The witness is the saturation `⋃ g, g • s`.

This needs no invariance hypothesis on `μ`: each `g • s` is already almost equal to `s`, because
`g • s` is the preimage of `s` under `(g⁻¹ • ·)`. -/
theorem exists_smul_invariant_ae_eq {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g • x) ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ g : G, (fun x => g • x) ⁻¹' t = t) ∧ t =ᵐ[μ] s := by
  have hsmul : ∀ g : G, g • s = (fun x => g⁻¹ • x) ⁻¹' s := fun g =>
    (Set.preimage_smul_inv g s).symm
  refine ⟨⋃ g : G, g • s, MeasurableSet.iUnion fun g => ?_, fun g => ?_, ?_⟩
  · exact hsmul g ▸ (measurable_const_smul (g⁻¹ : G)) hs
  · rw [Set.preimage_smul, Set.smul_set_iUnion]
    simp_rw [smul_smul]
    exact (Equiv.mulLeft (g⁻¹ : G)).surjective.iUnion_comp fun h : G => h • s
  · have hae : ∀ g : G, g • s =ᵐ[μ] s := fun g => (hsmul g) ▸ hinv g⁻¹
    have hunion := Filter.EventuallyEq.countable_iUnion (l := ae μ) hae
    rwa [Set.iUnion_const] at hunion

/-- **Ergodicity of a countable group action can be tested on exactly invariant events.**

Together with `MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq` this reduces ergodicity of a
countable action to a zero-one law for the σ-algebra of exactly invariant events. -/
theorem ergodicSMul_of_forall_smul_invariant [SMulInvariantMeasure G X μ]
    (h : ∀ t : Set X, MeasurableSet t → (∀ g : G, (fun x => g • x) ⁻¹' t = t) →
      EventuallyConst t (ae μ)) :
    ErgodicSMul G X μ :=
  ⟨fun hs hinv => by
    obtain ⟨t, ht, ht_inv, hts⟩ := exists_smul_invariant_ae_eq hs hinv
    exact (h t ht ht_inv).congr hts⟩

end MeasureTheory

end TauCeti
