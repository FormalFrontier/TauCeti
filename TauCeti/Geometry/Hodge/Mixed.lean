/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.Geometry.Hodge.Graded
public import TauCeti.Geometry.Hodge.Tate

/-!
# Mixed Hodge structures

A mixed Hodge structure on an integral module is an increasing rational weight filtration `W`
together with a decreasing complex Hodge filtration `F` inducing a pure Hodge structure of weight
`k` on every rational graded piece `grᵂ_k = W_k / W_{k-1}`. The graded objects the purity
condition is stated against are built in `TauCeti/Geometry/Hodge/Graded.lean`.

Purity is recorded as the existence of a `TauCeti.Hodge.HodgeStructure` whose filtration *is* the
induced one, rather than as a restatement of the pure axioms or as the bare existence of some
Hodge structure on the graded piece: the former would duplicate the pure object, the latter would
lose the link with `F`. As a consequence every result about pure Hodge structures — Hodge
components, the Hodge decomposition, the Weil operator — applies to the graded pieces of a mixed
Hodge structure through `TauCeti.Hodge.MixedHodgeStructure.gradedHodgeStructure`.

A pure Hodge structure of weight `n` is a mixed Hodge structure whose weight filtration is
concentrated in degree `n`; this is `TauCeti.Hodge.MixedHodgeStructure.ofPure`, and it makes the
Tate structure `ℤ(m)` an explicit rank-one inhabitant.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure`: the mixed Hodge structure itself.
* `TauCeti.Hodge.MixedHodgeStructure.WC`: the complexified weight filtration.
* `TauCeti.Hodge.MixedHodgeStructure.gradedHodgeStructure`: the pure Hodge structure of weight `k`
  carried by the `k`-th graded piece.
* `TauCeti.Hodge.MixedHodgeStructure.ofPure`: a pure Hodge structure viewed as a mixed one.
* `TauCeti.Hodge.tateMixed`: the Tate structure as a mixed Hodge structure.

## References

Deligne, *Théorie de Hodge II*, 1.2.10 and 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*,
Ch. 3. The signature of `MixedHodgeStructure` is adapted from the proposed definitions in
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean),
whose definitive mathematical specification is the accompanying Hodge structures roadmap.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

/-- A mixed Hodge structure on an integral module `Vℤ` with rational and complex base-change
models `Vℚ` and `Vℂ`.

The weight filtration `WQ` is increasing, recorded rationally, and finite in both directions; the
Hodge filtration `F` is decreasing and bounded on the complex model. Purity is imposed on the
rational graded pieces: for every `k`, the filtration `TauCeti.Hodge.gradedF` induced by `F` on
the complexification of `grᵂ_k = W_k / W_{k-1}` is the Hodge filtration of a pure Hodge structure
of weight `k`. -/
@[ext]
structure MixedHodgeStructure (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ) where
  /-- The increasing rational weight filtration. -/
  WQ : ℤ → Submodule ℚ Vℚ
  /-- The weight filtration is increasing. -/
  WQ_monotone : Monotone WQ
  /-- The weight filtration is exhaustive: `W_k` is everything for `k` large. -/
  WQ_top : ∃ k, WQ k = ⊤
  /-- The weight filtration is separated: `W_k` is zero for `k` small. -/
  WQ_bot : ∃ k, WQ k = ⊥
  /-- The decreasing Hodge filtration on the complex model. -/
  F : ℤ → Submodule ℂ Vℂ
  /-- The Hodge filtration is decreasing. -/
  F_antitone : Antitone F
  /-- The Hodge filtration is exhaustive: `F^p` is everything for `p` small. -/
  F_top : ∃ p, F p = ⊤
  /-- The Hodge filtration is separated: `F^p` is zero for `p` large. -/
  F_bot : ∃ p, F p = ⊥
  /-- The `k`-th rational graded piece, complexified, is a pure Hodge structure of weight `k`
  for the induced filtration. -/
  graded_pure : ∀ k, ∃ hs : HodgeStructure
      (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k)) k,
    hs.F = gradedF hℚ hℂ WQ WQ_monotone F k

namespace MixedHodgeStructure

variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ} (mhs : MixedHodgeStructure hℚ hℂ)

/-- The complexified weight filtration of a mixed Hodge structure. -/
noncomputable def WC (k : ℤ) : Submodule ℂ Vℂ :=
  rationalToComplexSubmodule hℚ hℂ (mhs.WQ k)

/-- The complex weight filtration is obtained by complexifying the rational weight filtration. -/
@[simp]
theorem WC_def (k : ℤ) :
    mhs.WC k = rationalToComplexSubmodule hℚ hℂ (mhs.WQ k) :=
  by rw [WC]

/-- The complexified weight filtration is stable under lattice-induced conjugation. -/
theorem WC_conj (k : ℤ) :
    (mhs.WC k).map (latticeConj hℂ) = mhs.WC k := by
  simp [WC]

/-- The complexified weight filtration is increasing. -/
theorem WC_monotone : Monotone mhs.WC := fun _ _ h ↦
  rationalToComplexSubmodule_mono hℚ hℂ (mhs.WQ_monotone h)

/-- The complexified weight filtration is exhaustive. -/
theorem WC_top : ∃ k, mhs.WC k = ⊤ := by
  obtain ⟨k, hk⟩ := mhs.WQ_top
  exact ⟨k, by rw [WC, hk, rationalToComplexSubmodule_top]⟩

/-- The complexified weight filtration is separated. -/
theorem WC_bot : ∃ k, mhs.WC k = ⊥ := by
  obtain ⟨k, hk⟩ := mhs.WQ_bot
  exact ⟨k, by rw [WC, hk, rationalToComplexSubmodule_bot]⟩

/-- The pure Hodge structure of weight `k` carried by the complexification of the `k`-th rational
graded piece. Its filtration is the induced one on the nose, so the whole pure theory applies to
the graded pieces of a mixed Hodge structure. -/
noncomputable def gradedHodgeStructure (k : ℤ) :
    HodgeStructure (isBaseChange_ratTensorMap ℂ (weightGradedRat mhs.WQ k)) k where
  F := gradedF hℚ hℂ mhs.WQ mhs.WQ_monotone mhs.F k
  F_antitone := gradedF_antitone hℚ hℂ mhs.WQ mhs.WQ_monotone mhs.F mhs.F_antitone k
  F_top := by
    obtain ⟨p, hp⟩ := mhs.F_top
    exact ⟨p, gradedF_of_eq_top hℚ hℂ mhs.WQ mhs.WQ_monotone mhs.F hp⟩
  opposed := by
    obtain ⟨hs, hF⟩ := mhs.graded_pure k
    exact hF ▸ hs.opposed

@[simp]
theorem gradedHodgeStructure_F (k : ℤ) :
    (mhs.gradedHodgeStructure k).F = gradedF hℚ hℂ mhs.WQ mhs.WQ_monotone mhs.F k := (rfl)

/-- The Hodge decomposition of each graded piece of a mixed Hodge structure. -/
theorem isInternal_gradedHodgeStructure_piece (k : ℤ) :
    DirectSum.IsInternal (mhs.gradedHodgeStructure k).piece :=
  HodgeStructureOn.isInternal_piece _

end MixedHodgeStructure

section OfPure

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)

variable (Vℚ) in
/-- The weight filtration concentrated in a single degree `n`: everything from degree `n` on,
zero below. It is the weight filtration of a pure Hodge structure of weight `n`. -/
def concentratedWeightFiltration (n : ℤ) : ℤ → Submodule ℚ Vℚ :=
  fun k ↦ if n ≤ k then ⊤ else ⊥

variable {n : ℤ}

@[simp]
theorem concentratedWeightFiltration_of_le {k : ℤ} (h : n ≤ k) :
    concentratedWeightFiltration Vℚ n k = ⊤ := by
  simp [concentratedWeightFiltration, h]

@[simp]
theorem concentratedWeightFiltration_of_lt {k : ℤ} (h : k < n) :
    concentratedWeightFiltration Vℚ n k = ⊥ := by
  simp [concentratedWeightFiltration, Int.not_le.mpr h]

theorem concentratedWeightFiltration_monotone :
    Monotone (concentratedWeightFiltration Vℚ n) := by
  intro j k hjk
  rcases lt_or_ge j n with hj | hj
  · rw [concentratedWeightFiltration_of_lt hj]
    exact bot_le
  · rw [concentratedWeightFiltration_of_le hj, concentratedWeightFiltration_of_le (hj.trans hjk)]

/-- Away from its single jump, the concentrated weight filtration is constant. -/
theorem concentratedWeightFiltration_le_pred {k : ℤ} (hk : k ≠ n) :
    concentratedWeightFiltration Vℚ n k ≤ concentratedWeightFiltration Vℚ n (k - 1) := by
  rcases lt_or_ge k n with hj | hj
  · rw [concentratedWeightFiltration_of_lt hj]
    exact bot_le
  · rw [concentratedWeightFiltration_of_le (by omega : n ≤ k - 1)]
    exact le_top

/-- **A pure Hodge structure is a mixed Hodge structure.** Its weight filtration is concentrated
in the single degree `n`, so the only nonzero graded piece is `grᵂ_n`, which is the whole space
with the given filtration. This exhibits the mixed axioms as satisfiable. -/
noncomputable def MixedHodgeStructure.ofPure (hs : HodgeStructure hℂ n) :
    MixedHodgeStructure hℚ hℂ where
  WQ := concentratedWeightFiltration Vℚ n
  WQ_monotone := concentratedWeightFiltration_monotone
  WQ_top := ⟨n, concentratedWeightFiltration_of_le le_rfl⟩
  WQ_bot := ⟨n - 1, concentratedWeightFiltration_of_lt (by omega)⟩
  F := hs.F
  F_antitone := hs.F_antitone
  F_top := hs.F_top
  F_bot := hs.F_bot
  graded_pure k := by
    rcases eq_or_ne k n with rfl | hk
    · refine ⟨hs.comap (gradedEquivOfEqBotOfEqTop hℚ hℂ _ concentratedWeightFiltration_monotone
        (concentratedWeightFiltration_of_lt (by omega)) (concentratedWeightFiltration_of_le le_rfl))
        (fun x ↦ by simpa using gradedEquivOfEqBotOfEqTop_latticeConj hℚ hℂ _ _ _ _ x), ?_⟩
      funext p
      rw [HodgeStructureOn.comap_F]
      exact (gradedF_eq_comap hℚ hℂ _ _ _ _ hs.F p).symm
    · have : Subsingleton (weightGradedRat (concentratedWeightFiltration Vℚ n) k) :=
        Submodule.Quotient.subsingleton_iff.mpr
          (Submodule.submoduleOf_eq_top.2 (concentratedWeightFiltration_le_pred hk))
      exact ⟨{ F := gradedF hℚ hℂ _ concentratedWeightFiltration_monotone hs.F k
               F_antitone := gradedF_antitone hℚ hℂ _ _ hs.F hs.F_antitone k
               F_top := ⟨0, Subsingleton.elim _ _⟩
               opposed := fun _ ↦ ⟨disjoint_iff.2 (Subsingleton.elim _ _),
                 codisjoint_iff.2 (Subsingleton.elim _ _)⟩ }, rfl⟩

@[simp]
theorem MixedHodgeStructure.ofPure_WQ (hs : HodgeStructure hℂ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WQ = concentratedWeightFiltration Vℚ n :=
  (rfl)

@[simp]
theorem MixedHodgeStructure.ofPure_F (hs : HodgeStructure hℂ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).F = hs.F :=
  (rfl)

/-- The Tate structure `ℤ(m)` as a mixed Hodge structure: a rank-one example whose weight
filtration jumps in degree `-2m`. -/
noncomputable def tateMixed (m : ℤ) :
    MixedHodgeStructure (Vℤ := ℤ) (Vℚ := ℚ) (IsBaseChange.linearMap ℤ ℚ)
      isBaseChange_tateLatticeMap :=
  MixedHodgeStructure.ofPure _ _ (tate m)

end OfPure

end TauCeti.Hodge
