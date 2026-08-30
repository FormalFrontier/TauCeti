/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Hölder spaces

This file records the carrier and canonical norm estimates for the zeroth-order global Hölder
space.  The carrier is a submodule of bounded continuous maps, using Mathlib's existing
`MemHolder` predicate and `nnHolderNorm` seminorm.  The Banach-space completion of this carrier is
the next step in the `C^{k,α}` lane of `TauCetiRoadmap/PDE/README.md`.
-/

public section
noncomputable section

namespace TauCeti

open Set
open scoped NNReal BoundedContinuousFunction ENNReal

universe u v

variable {X : Type u} {Y : Type v} [MetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The supremum-plus-Hölder norm on bounded continuous maps. -/
@[reducible, expose]
def holderNorm (α : ℝ≥0) (f : X →ᵇ Y) : ℝ := ‖f‖ + nnHolderNorm α (f : X → Y)

/-- The additive submodule of bounded continuous `α`-Hölder functions. -/
@[reducible, expose]
def holderSubmodule (α : ℝ≥0) : Submodule ℝ (X →ᵇ Y) where
  carrier := {f | MemHolder α (f : X → Y)}
  zero_mem' := memHolder_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun _ _ hf => hf.smul

namespace holderSubmodule

variable {α : ℝ≥0}

theorem memHolder (f : holderSubmodule (X := X) (Y := Y) α) :
    MemHolder α (f : X → Y) := f.2

theorem holderWith (f : holderSubmodule (X := X) (Y := Y) α) :
    HolderWith (nnHolderNorm α (f : X → Y)) α (f : X → Y) :=
  (holderSubmodule.memHolder f).holderWith

theorem memHolder_sub (f g : holderSubmodule (X := X) (Y := Y) α) :
    MemHolder α (((f : X →ᵇ Y) - g) : X → Y) := by
  convert (holderSubmodule.memHolder f).add
      ((holderSubmodule.memHolder g).smul (c := (-1 : ℝ))) using 1;
    (ext x; simp [sub_eq_add_neg])

omit [NormedSpace ℝ Y] in
theorem holderNorm_nonneg (f : X →ᵇ Y) : 0 ≤ holderNorm α f := by
  exact add_nonneg (norm_nonneg f) NNReal.zero_le_coe

theorem holderNorm_coe_le (f : holderSubmodule (X := X) (Y := Y) α) :
    ‖(f : X →ᵇ Y)‖ ≤ holderNorm α (f : X →ᵇ Y) := by
  exact le_add_of_nonneg_right NNReal.zero_le_coe

theorem nnHolderNorm_le_holderNorm (f : holderSubmodule (X := X) (Y := Y) α) :
    (nnHolderNorm α (f : X → Y) : ℝ) ≤ holderNorm α (f : X →ᵇ Y) := by
  exact le_add_of_nonneg_left (norm_nonneg (f : X →ᵇ Y))

theorem holderNorm_add_le (f g : holderSubmodule (X := X) (Y := Y) α) :
    holderNorm α ((f : X →ᵇ Y) + (g : X →ᵇ Y)) ≤
      holderNorm α (f : X →ᵇ Y) + holderNorm α (g : X →ᵇ Y) := by
  rw [holderNorm, holderNorm, holderNorm]
  calc
    ‖(f : X →ᵇ Y) + (g : X →ᵇ Y)‖ +
          (nnHolderNorm α (((f : X →ᵇ Y) + (g : X →ᵇ Y)) : X → Y) : ℝ) ≤
        (‖(f : X →ᵇ Y)‖ + ‖(g : X →ᵇ Y)‖) +
          (nnHolderNorm α (f : X → Y) + nnHolderNorm α (g : X → Y)) := by
      apply add_le_add (norm_add_le _ _)
      have h := (holderSubmodule.memHolder f).nnHolderNorm_add_le
        (holderSubmodule.memHolder g)
      have heq : ((f : X →ᵇ Y) + (g : X →ᵇ Y) : X → Y) =
          (f : X → Y) + (g : X → Y) := by
        ext x
        rfl
      rw [heq]
      exact_mod_cast h
    _ = (‖(f : X →ᵇ Y)‖ + (nnHolderNorm α (f : X → Y) : ℝ)) +
          (‖(g : X →ᵇ Y)‖ + (nnHolderNorm α (g : X → Y) : ℝ)) := by ring

theorem holderNorm_smul (c : ℝ) (f : holderSubmodule (X := X) (Y := Y) α) :
    holderNorm α (c • (f : X →ᵇ Y)) = ‖c‖ * holderNorm α (f : X →ᵇ Y) := by
  rw [holderNorm, norm_smul, holderNorm]
  have h := (holderSubmodule.memHolder f).nnHolderNorm_smul c
  have heq : ((c • (f : X →ᵇ Y)) : X → Y) = c • (f : X → Y) := by
    ext x
    rfl
  change ‖c‖ * ‖(f : X →ᵇ Y)‖ + (nnHolderNorm α (c • (f : X → Y)) : ℝ) = _
  rw [h]
  simp only [NNReal.coe_mul, coe_nnnorm]
  ring

theorem holderNorm_sub_le (f g h : holderSubmodule (X := X) (Y := Y) α) :
    holderNorm α ((f : X →ᵇ Y) - (h : X →ᵇ Y)) ≤
      holderNorm α ((f : X →ᵇ Y) - (g : X →ᵇ Y)) +
        holderNorm α ((g : X →ᵇ Y) - (h : X →ᵇ Y)) := by
  have hseminorm := (holderSubmodule.memHolder_sub f g).nnHolderNorm_add_le
    (holderSubmodule.memHolder_sub g h)
  have hfun : ((f : X →ᵇ Y) - h : X → Y) =
      (((f : X →ᵇ Y) - g) : X → Y) + (((g : X →ᵇ Y) - h) : X → Y) := by
    ext x
    simp [sub_eq_add_neg, add_assoc]
  rw [holderNorm, holderNorm, holderNorm]
  have hnorm : ‖(f : X →ᵇ Y) - h‖ ≤
      ‖(f : X →ᵇ Y) - g‖ + ‖(g : X →ᵇ Y) - h‖ := by
    rw [show (f : X →ᵇ Y) - h = ((f : X →ᵇ Y) - g) + ((g : X →ᵇ Y) - h) by abel]
    exact norm_add_le _ _
  have hsem : nnHolderNorm α (((f : X →ᵇ Y) - h) : X → Y) ≤
      nnHolderNorm α (((f : X →ᵇ Y) - g) : X → Y) +
        nnHolderNorm α (((g : X →ᵇ Y) - h) : X → Y) := by
    rw [hfun]
    exact hseminorm
  calc
    ‖(f : X →ᵇ Y) - h‖ + (nnHolderNorm α (((f : X →ᵇ Y) - h) : X → Y) : ℝ) ≤
        (‖(f : X →ᵇ Y) - g‖ + ‖(g : X →ᵇ Y) - h‖) +
          (nnHolderNorm α (((f : X →ᵇ Y) - g) : X → Y) +
            nnHolderNorm α (((g : X →ᵇ Y) - h) : X → Y)) := by
      exact add_le_add hnorm hsem
    _ = _ := by
      have hfg : ((((f : X →ᵇ Y) - (g : X →ᵇ Y)) : X →ᵇ Y) : X → Y) =
          (f : X → Y) - (g : X → Y) := by
        ext x
        rfl
      have hgh : ((((g : X →ᵇ Y) - (h : X →ᵇ Y)) : X →ᵇ Y) : X → Y) =
          (g : X → Y) - (h : X → Y) := by
        ext x
        rfl
      have hfg' := congrArg (fun q : X → Y => nnHolderNorm α q) hfg
      have hgh' := congrArg (fun q : X → Y => nnHolderNorm α q) hgh
      rw [hfg', hgh']
      ring

end holderSubmodule

end TauCeti
