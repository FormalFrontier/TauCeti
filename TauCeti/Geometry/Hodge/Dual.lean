/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Hodge.Structure

/-!
# The dual of a pure Hodge structure

The dual `V^*` of a pure Hodge structure of weight `n` is a pure Hodge structure of weight `-n`
on the complex dual space: its filtration step at index `p` is the annihilator of the conjugate
filtration step of index `1 - p` of the original structure, and its conjugation is the twisted
transpose of the original conjugation, sending a functional `φ` to `v ↦ conj (φ (ω v))`.
The dual pairing then respects Hodge components of complementary indices: the `p`-th component
of the dual pairs nontrivially only against components of index at most `n + p`, and has the
same dimension as the `(n + p)`-th component, so dualizing reflects the table of Hodge numbers.

This is one of the companion constructions of Layer L0 of `TauCetiRoadmap/HodgeStructures/README.md`
(the `⊗`/`Hom`/dual companions), following Peters–Steenbrink, *Mixed Hodge Structures*, §2; it is
the base on which the internal hom of Hodge structures is to be built.

## Main declarations

* `TauCeti.Hodge.Conjugation.dual`: the twisted transpose of a conjugation, again a conjugation,
  on the complex dual space, with its pointwise description
  `TauCeti.Hodge.Conjugation.dual_toEquiv_apply`.
* `TauCeti.Hodge.Conjugation.map_dualAnnihilator`: a conjugation carries dual annihilators to
  dual annihilators of conjugated subspaces.
* `TauCeti.Hodge.HodgeStructureOn.dual`: the dual pure Hodge structure, of weight `-n`.
  Finiteness of the ambient complex space is needed for the opposedness of the dual filtration,
  where complements dualize to complements only in finite dimension.
* `TauCeti.Hodge.HodgeStructureOn.dual_F`, `…dual_conjF`: the steps of the dual filtration are
  dual annihilators of conjugate steps.
* `TauCeti.Hodge.HodgeStructureOn.dual_piece` and `…mem_dual_piece_iff`: the components of the
  dual structure are annihilators of unions of complementary filtration steps.
* `TauCeti.Hodge.HodgeStructureOn.finrank_dual_piece`: the dimension of the `p`-th component of
  the dual equals that of the `(n + p)`-th component.
* `TauCeti.Hodge.HodgeStructureOn.apply_eq_zero_of_mem_piece_of_lt`: the dual pairing vanishes
  between components whose indices fail `index ≤ n + p`.
-/

public section

namespace TauCeti.Hodge

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

namespace Conjugation

/-- The twisted transpose of a conjugation: a functional `φ` is sent to the functional
conjugating the values of `φ` along `ω`. -/
def dualMap (ω : Conjugation W) :
    Module.Dual ℂ W →ₛₗ[starRingEnd ℂ] Module.Dual ℂ W :=
  { toFun := fun φ =>
      { toFun := fun v => star (φ (ω.toEquiv v))
        map_add' := by
          intro x y
          simp [map_add, star_add]
        map_smul' := by
          intro c v
          have h1 : ω.toEquiv (c • v) = (starRingEnd ℂ) c • ω.toEquiv v :=
            LinearMap.map_smulₛₗ ω.toEquiv.toLinearMap c v
          have h2 : φ ((starRingEnd ℂ) c • ω.toEquiv v) =
              (starRingEnd ℂ) c * φ (ω.toEquiv v) := by simp
          rw [h1, h2]
          simp [star_mul, mul_comm] }
    map_add' := by
      intro φ ψ
      ext v
      simp
    map_smul' := by
      intro c φ
      ext v
      simp }

/-- Pointwise description of the twisted transpose. -/
@[simp]
theorem dualMap_apply (ω : Conjugation W) (φ : Module.Dual ℂ W) (v : W) :
    dualMap ω φ v = star (φ (ω.toEquiv v)) :=
  (rfl)

/-- The twisted transpose is an involution. -/
private theorem dualMap_involutive (ω : Conjugation W) :
    Function.Involutive (dualMap ω) := by
  intro φ
  ext v
  simp [dualMap_apply, ω.apply_apply]

/-- The twisted transpose of a conjugation `ω`: a functional `φ` acts by conjugating the values
of `φ` along `ω`. It is again an involution, so it packages as a conjugation on the dual space;
see `TauCeti.Hodge.Conjugation.dualMap` for its pointwise description. -/
def dual (ω : Conjugation W) : Conjugation (Module.Dual ℂ W) where
  toEquiv :=
    { toFun := dualMap ω
      invFun := dualMap ω
      left_inv := dualMap_involutive ω
      right_inv := dualMap_involutive ω
      map_add' := by
        intro φ ψ
        ext v
        simp [map_add]
      map_smul' := by
        intro c φ
        ext v
        simp [dualMap_apply] }
  involutive := dualMap_involutive ω

/-- Pointwise description of the dual conjugation. -/
@[simp]
theorem dual_toEquiv_apply (ω : Conjugation W) (φ : Module.Dual ℂ W) (v : W) :
    ω.dual.toEquiv φ v = star (φ (ω.toEquiv v)) :=
  (rfl)

/-- A conjugation carries dual annihilators to dual annihilators of conjugated subspaces. -/
theorem map_dualAnnihilator (ω : Conjugation W) (U : Submodule ℂ W) :
    U.dualAnnihilator.map ω.dual.toEquiv.toLinearMap =
      (U.map ω.toEquiv.toLinearMap).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator, Submodule.mem_map]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
    have hψ' : ∀ w ∈ U, ψ w = 0 := (Submodule.mem_dualAnnihilator ψ).mp hψ
    have h2 : ψ (ω.toEquiv (ω.toEquiv v)) = ψ v := by rw [ω.apply_apply]
    have key : star (ψ (ω.toEquiv (ω.toEquiv v))) = 0 := by
      rw [ω.apply_apply, hψ' v hv]
      simp
    -- the goal is definitionally the preceding statement, by the pointwise description of the
    -- dual conjugation (`Conjugation.dual_toEquiv_apply`)
    exact key
  · intro h
    refine ⟨ω.dual.toEquiv φ,
      (Submodule.mem_dualAnnihilator (ω.dual.toEquiv φ)).mpr fun u hu => ?_, ?_⟩
    · have heq : ω.dual.toEquiv φ u = star (φ (ω.toEquiv u)) := rfl
      have h0 : φ (ω.toEquiv u) = 0 :=
        h (ω.toEquiv u) (Submodule.mem_map.2 ⟨u, hu, rfl⟩)
      rw [heq, h0]
      exact star_zero _
    · ext v
      exact congrArg (fun f => f v) (ω.dual.apply_apply φ)

end Conjugation

namespace HodgeStructureOn

variable {ω : Conjugation W} {n : ℤ}

/-- Opposedness of the dual filtration: the annihilators of a complementary pair are
complementary. This is the step that uses finiteness of the ambient space. -/
private theorem isCompl_dual_annihilator (hs : HodgeStructureOn W ω n) [Module.Finite ℂ W]
    (p : ℤ) :
    IsCompl (hs.conjF (1 - p)).dualAnnihilator
      ((hs.conjF (1 - (-n + 1 - p))).dualAnnihilator.map
        ω.dual.toEquiv.toLinearMap) := by
  have hstep : (hs.conjF (1 - (-n + 1 - p))).dualAnnihilator.map
      ω.dual.toEquiv.toLinearMap = (hs.F (n + p)).dualAnnihilator := by
    rw [Conjugation.map_dualAnnihilator, hs.conjF_def, ω.map_map_eq_self]
    -- the remaining goal is index arithmetic
    exact congrArg _ (by ring)
  have key := hs.isCompl_F_conjF (n + p)
  rw [show n + 1 - (n + p) = 1 - p from by ring] at key
  rw [hstep]
  exact (Subspace.isCompl_dualAnnihilator key).symm

variable (hs : HodgeStructureOn W ω n)

/-- **The dual pure Hodge structure**, of weight `-n`.

Its filtration step at index `p` is the annihilator of the conjugate filtration step of index
`1 - p`; its conjugation is the twisted transpose `TauCeti.Hodge.Conjugation.dual`. Finiteness of
the ambient complex space enters through opposedness: the dual of a complementary pair is a
complementary pair only for finite-dimensional spaces. -/
noncomputable def dual [Module.Finite ℂ W] :
    HodgeStructureOn (Module.Dual ℂ W) ω.dual (-n) where
  F p := (hs.conjF (1 - p)).dualAnnihilator
  F_antitone := fun p q hpq =>
    Submodule.dualAnnihilator_anti (hs.conjF_antitone (by omega))
  F_top := by
    obtain ⟨q, hq⟩ := hs.F_bot
    have hc : hs.conjF (1 - (1 - q)) = ⊥ := by
      have hq' : 1 - (1 - q) = q := by ring
      rw [hq', hs.conjF_def, hq, Submodule.map_bot]
    refine ⟨1 - q, ?_⟩
    rw [hc, Submodule.dualAnnihilator_bot]
  opposed := hs.isCompl_dual_annihilator

/-- The filtration of the dual Hodge structure is made of dual annihilators of conjugate steps. -/
@[simp]
theorem dual_F [Module.Finite ℂ W] (p : ℤ) :
    (hs.dual).F p = (hs.conjF (1 - p)).dualAnnihilator :=
  (rfl)

/-- Membership in a step of the dual filtration: vanishing on the conjugate step of
complementary index. -/
@[simp]
theorem mem_dual_F_iff [Module.Finite ℂ W] (p : ℤ) (φ : Module.Dual ℂ W) :
    φ ∈ (hs.dual).F p ↔ ∀ v ∈ hs.conjF (1 - p), φ v = 0 := by
  rw [hs.dual_F, Submodule.mem_dualAnnihilator]

/-- The conjugate of a step of the dual filtration is the annihilator of a step. -/
theorem dual_conjF [Module.Finite ℂ W] (p : ℤ) :
    (hs.dual).conjF p = (hs.F (1 - p)).dualAnnihilator := by
  rw [(hs.dual).conjF_def, hs.dual_F, Conjugation.map_dualAnnihilator, hs.conjF_def,
    ω.map_map_eq_self]

/-- A component of the dual Hodge structure is the annihilator of the union of the two
filtration steps flanking the component of complementary index. -/
theorem dual_piece [Module.Finite ℂ W] (p : ℤ) :
    (hs.dual).piece p =
      ((hs.conjF (1 - p)) ⊔ (hs.F (n + 1 + p))).dualAnnihilator := by
  rw [piece_def, hs.dual_F, dual_conjF, ← Submodule.dualAnnihilator_sup_eq]
  have hidx : 1 - (-n - p) = n + 1 + p := by omega
  rw [hidx]

/-- Membership in a component of the dual Hodge structure: vanishing on the two filtration steps
of complementary index. -/
@[simp]
theorem mem_dual_piece_iff [Module.Finite ℂ W] (p : ℤ) (φ : Module.Dual ℂ W) :
    φ ∈ (hs.dual).piece p ↔
      (∀ v ∈ hs.conjF (1 - p), φ v = 0) ∧ (∀ v ∈ hs.F (n + 1 + p), φ v = 0) := by
  rw [piece_def, hs.dual_F, dual_conjF,
    show 1 - (-n - p) = n + 1 + p from by omega, Submodule.mem_inf,
    Submodule.mem_dualAnnihilator, Submodule.mem_dualAnnihilator]

section Dimension

/-- If `B` complements a submodule `C ≤ A`, the part of `A` complementary to `B` together with
`C` fills `A`. -/
private theorem finrank_inf_add_finrank_eq_finrank {A B C : Submodule ℂ W}
    (hcompl : IsCompl C B) (hCA : C ≤ A) [Module.Finite ℂ W] :
    Module.finrank ℂ ↥(A ⊓ B) + Module.finrank ℂ ↥C = Module.finrank ℂ ↥A := by
  have hsup : C ⊔ A ⊓ B = A := by
    refine le_antisymm (sup_le hCA inf_le_left) ?_
    intro x hxA
    have hx' : x ∈ (C ⊔ B : Submodule ℂ W) :=
      (le_of_eq hcompl.codisjoint.eq_top.symm) Submodule.mem_top
    obtain ⟨c, hc, b, hb, hx⟩ := Submodule.mem_sup.1 hx'
    have hm : x - c ∈ A := sub_mem hxA (hCA hc)
    have hxcb : x - c = b := by rw [← hx]; abel
    have hbx : x - c ∈ B := by rw [hxcb]; exact hb
    exact Submodule.mem_sup.mpr ⟨c, hc, x - c, ⟨hm, hbx⟩,
      by rw [hxcb]; exact hx⟩
  have hdisj : Disjoint C (A ⊓ B) :=
    hcompl.disjoint.mono_right inf_le_right
  have key := Submodule.finrank_sup_add_finrank_inf_eq C (A ⊓ B)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, hsup] at key
  omega

/-- Complementary submodules partition the dimension. -/
private theorem finrank_add_finrank_of_isCompl {B C : Submodule ℂ W}
    (hcompl : IsCompl C B) [Module.Finite ℂ W] :
    Module.finrank ℂ ↥C + Module.finrank ℂ ↥B = Module.finrank ℂ W := by
  have key := Submodule.finrank_sup_add_finrank_inf_eq C B
  rw [hcompl.disjoint.eq_bot, finrank_bot, add_zero, hcompl.codisjoint.eq_top,
    finrank_top] at key
  exact key.symm

/-- The dimension of the `p`-th component of the dual Hodge structure equals the dimension of
the `(n + p)`-th component: dualizing reflects the table of Hodge numbers. -/
theorem finrank_dual_piece [Module.Finite ℂ W] (p : ℤ) :
    Module.finrank ℂ ((hs.dual).piece p) = Module.finrank ℂ (hs.piece (n + p)) := by
  have hcomp := hs.isCompl_F_conjF (n + p)
  rw [show n + 1 - (n + p) = 1 - p from by ring] at hcomp
  have hd : Disjoint (hs.conjF (1 - p)) (hs.F (n + 1 + p)) :=
    hcomp.disjoint.symm.mono_right
      (hs.F_antitone (show n + p ≤ n + 1 + p from by omega))
  have hL1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    ((hs.conjF (1 - p)) ⊔ (hs.F (n + 1 + p)))
  have hL2 := Submodule.finrank_sup_add_finrank_inf_eq (hs.conjF (1 - p)) (hs.F (n + 1 + p))
  rw [hd.eq_bot, finrank_bot, add_zero] at hL2
  have hL3 := finrank_add_finrank_of_isCompl hcomp
  have hcomp2 := hs.isCompl_F_conjF (n + 1 + p)
  rw [show n + 1 - (n + 1 + p) = -p from by ring] at hcomp2
  have hrhs := finrank_inf_add_finrank_eq_finrank hcomp2
    (hs.F_antitone (show n + p ≤ n + 1 + p from by omega))
  rw [dual_piece, piece_def]
  have hidx : n - (n + p) = -p := by ring
  rw [hidx]
  omega

end Dimension

/-- A functional in the `p`-th component of the dual vanishes on every component of index above
`n + p`: the dual pairing pairs the `p`-th component of the dual against components of index at
most `n + p`. -/
theorem apply_eq_zero_of_mem_piece_of_lt [Module.Finite ℂ W] {a p : ℤ}
    {u : W} {φ : Module.Dual ℂ W} (hu : u ∈ hs.piece a) (hφ : φ ∈ (hs.dual).piece p)
    (hlt : n + p < a) :
    φ u = 0 := by
  rw [mem_dual_piece_iff] at hφ
  have hpair := (mem_piece_iff hs a u).mp hu
  have hlt' : n + 1 + p ≤ a := by omega
  have hu'' : u ∈ hs.F (n + 1 + p) :=
    hs.F_antitone hlt' (by exact hpair.1)
  exact hφ.2 u hu''

end HodgeStructureOn

end TauCeti.Hodge
