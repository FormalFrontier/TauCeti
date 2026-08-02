/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Conjugation-invariance in `Lp`, and the class functions

Conjugation `g ↦ h * g * h⁻¹` on a group is left translation followed by right translation, so a
measure that is invariant under both is invariant under conjugation.  Normalized Haar measure on a
compact group is such a measure, which is what makes "class function" a meaningful condition on an
almost-everywhere equivalence class.

This file records that invariance and feeds it into the two typeclasses Mathlib's machinery
consumes: the conjugation action of `ConjAct G` on `G` is measurable and measure-preserving, so
Mathlib's `DomMulAct` action supplies an isometric action of `(ConjAct G)ᵈᵐᵃ` on `Lp E p μ` by
precomposition, `(c • f) g = f (h * g * h⁻¹)`.  The **class functions** `centralLp` are the vectors
that action fixes: a closed submodule, since each conjugation acts by an isometry.

The condition is on the *class*, not on a representative, and that is the point of packaging it
this way rather than as a pointwise slogan: pointwise conjugation-invariance of a function is not
stable under changing it on a null set, so it does not descend to `Lp` at all.  What descends is
`TauCeti.mem_centralLp_iff_ae`, invariance up to a null set.

## Main definitions

* `TauCeti.centralLp`: the class functions in `Lp E p μ`, a submodule.

## Main statements

* `TauCeti.measurePreserving_conj`: conjugation preserves a two-sided invariant measure.
* `TauCeti.instMeasurableConstSMulConjAct` and `TauCeti.instSMulInvariantMeasureConjAct`: the two
  instances that unlock `DomMulAct`'s action on `Lp`.
* `TauCeti.conjAct_smul_Lp_ae_eq`: the induced action on `Lp` is precomposition with conjugation.
* `TauCeti.mem_centralLp_iff_ae`: membership read on representatives, as invariance almost
  everywhere.
* `TauCeti.isClosed_centralLp`: the class functions are a closed subspace, hence
  (`TauCeti.instCompleteSpaceCentralLp`) complete.
* `TauCeti.mem_centralLp_of_ae_eq`: a pointwise invariant representative makes a class function.

The compact-group specialization -- that the character of a continuous representation is a class
function in `L²(G)` -- is in `TauCeti/RepresentationTheory/Compact/CentralLp.lean`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- **Conjugation preserves a two-sided invariant measure.**  Conjugation by `h` is left
translation by `h` followed by right translation by `h⁻¹`. -/
theorem measurePreserving_conj (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (h : G) : MeasurePreserving (fun g ↦ h * g * h⁻¹) μ μ :=
  (measurePreserving_mul_right μ h⁻¹).comp (measurePreserving_mul_left μ h)

/-- Conjugation by a fixed element is measurable, so the conjugation action of `ConjAct G` on `G`
has measurable orbit maps. -/
instance instMeasurableConstSMulConjAct : MeasurableConstSMul (ConjAct G) G where
  measurable_const_smul c := by
    simp only [ConjAct.smul_def]
    exact (measurable_id.const_mul _).mul_const _

/-- A two-sided invariant measure is invariant under the conjugation action of `ConjAct G`. -/
instance instSMulInvariantMeasureConjAct {μ : Measure G} [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] : SMulInvariantMeasure (ConjAct G) G μ where
  measure_preimage_smul c s hs := by
    simp only [ConjAct.smul_def]
    exact (measurePreserving_conj μ (ConjAct.ofConjAct c)).measure_preimage hs.nullMeasurableSet

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- The action of `(ConjAct G)ᵈᵐᵃ` on `Lp E p μ` is precomposition with conjugation: the class of
`f` is sent to the class of `g ↦ f (h * g * h⁻¹)`. -/
theorem conjAct_smul_Lp_ae_eq (h : G) (f : Lp E p μ) :
    DomMulAct.mk (ConjAct.toConjAct h) • f =ᵐ[μ] fun g ↦ f (h * g * h⁻¹) := by
  simpa only [Equiv.symm_apply_apply, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] using
    DomMulAct.smul_Lp_ae_eq (DomMulAct.mk (ConjAct.toConjAct h)) f

/-- **The class functions in `Lp`.**  The submodule of `Lp E p μ` fixed by every conjugation,
for a two-sided invariant measure `μ` on a group `G`.

Invariance is a condition on the *class*, not on a representative: an element of `Lp` is a class
function exactly when each of its conjugates agrees with it almost everywhere
(`TauCeti.mem_centralLp_iff_ae`).  Asking instead for a pointwise identity would not define a
submodule of `Lp` at all, since it is not stable under changing a representative on a null set. -/
def centralLp (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] : Submodule 𝕜 (Lp E p μ) where
  carrier := {f | ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f}
  add_mem' hf hg c := by rw [DomMulAct.smul_Lp_add, hf c, hg c]
  zero_mem' c := DomMulAct.smul_Lp_zero c
  smul_mem' a _ hf c := by rw [smul_comm, hf c]

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]

@[simp]
theorem mem_centralLp_iff {f : Lp E p μ} :
    f ∈ centralLp 𝕜 E p μ ↔ ∀ c : (ConjAct G)ᵈᵐᵃ, c • f = f :=
  Iff.rfl

/-- **Membership of `centralLp`, read on representatives.**  A class lies in `centralLp` exactly
when each of its conjugates agrees with it almost everywhere. -/
theorem mem_centralLp_iff_ae {f : Lp E p μ} :
    f ∈ centralLp 𝕜 E p μ ↔ ∀ h : G, (fun g ↦ f (h * g * h⁻¹)) =ᵐ[μ] f := by
  constructor
  · intro hf h
    refine ((conjAct_smul_Lp_ae_eq h f).symm.trans ?_)
    rw [hf (DomMulAct.mk (ConjAct.toConjAct h))]
  · intro hf c
    obtain ⟨a, rfl⟩ := DomMulAct.mk.surjective c
    obtain ⟨h, rfl⟩ := ConjAct.toConjAct.surjective a
    exact Lp.ext ((conjAct_smul_Lp_ae_eq h f).trans (hf h))

/-- **The class functions form a closed subspace.**  Each conjugation acts on `Lp` by an isometry,
so the set where it agrees with the identity is closed, and `centralLp` is their intersection. -/
theorem isClosed_centralLp : IsClosed (centralLp 𝕜 E p μ : Set (Lp E p μ)) := by
  have : (centralLp 𝕜 E p μ : Set (Lp E p μ)) =
      ⋂ c : (ConjAct G)ᵈᵐᵃ, {f : Lp E p μ | c • f = f} := by
    ext f
    simp [centralLp]
  rw [this]
  exact isClosed_iInter fun c ↦ isClosed_eq (continuous_const_smul c) continuous_id

/-- **The class functions are complete.**  A closed subspace of the complete space `Lp E p μ`; for
`p = 2` this is the Hilbert space that the characters of a compact group are expected to form an
orthonormal basis of. -/
instance instCompleteSpaceCentralLp [CompleteSpace E] :
    CompleteSpace (centralLp 𝕜 E p μ) :=
  (isClosed_centralLp 𝕜).completeSpace_coe

/-- **A genuinely invariant representative makes a class function.**  If some representative `F` of
`f` is constant on conjugacy classes on the nose, then `f` is central.  Only the representative is
asked to be invariant pointwise: the null set on which `f` and `F` disagree pulls back along
conjugation to a null set, because conjugation preserves `μ`. -/
theorem mem_centralLp_of_ae_eq {f : Lp E p μ} {F : G → E} (hF : ⇑f =ᵐ[μ] F)
    (hFconj : ∀ g h : G, F (h * g * h⁻¹) = F g) : f ∈ centralLp 𝕜 E p μ := by
  rw [mem_centralLp_iff_ae]
  intro h
  have hconj := (measurePreserving_conj μ h).quasiMeasurePreserving.ae_eq hF
  refine hconj.trans (Filter.EventuallyEq.trans ?_ hF.symm)
  exact Filter.Eventually.of_forall fun g ↦ hFconj g h

/-- A constant is a class function. -/
theorem const_mem_centralLp [IsFiniteMeasure μ] (a : E) :
    Lp.const p μ a ∈ centralLp 𝕜 E p μ :=
  fun c ↦ DomMulAct.smul_Lp_const c a

/-- On a commutative group every element of `Lp` is a class function: conjugation is trivial. -/
theorem centralLp_eq_top_of_commGroup {G : Type*} [CommGroup G] [MeasurableSpace G]
    [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] :
    centralLp 𝕜 E p μ = ⊤ := by
  refine eq_top_iff.2 fun f _ ↦ ?_
  rw [mem_centralLp_iff_ae]
  intro h
  refine Filter.Eventually.of_forall fun g ↦ ?_
  simp [mul_comm h g, mul_assoc]

end TauCeti
