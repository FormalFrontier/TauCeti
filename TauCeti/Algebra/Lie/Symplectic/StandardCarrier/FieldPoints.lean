/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# Field-valued points of the type-C full-weight carrier

Over a field, the standard positive and negative simple-root subgroups generate the full
symplectic group.  The ring-general identification of these subgroups with the numbered root
subgroups of the full-weight type `C_(n+1)` carrier is proved in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation`.  Since the carrier already preserves
the standard alternating form, its matrix points are therefore exactly
`TauCeti.GLSymplecticFin (n + 1) K`.

## Main results

* `TauCeti.SpStd.points_eq_GLSymplecticFin`: over a field, the carrier points are the full
  symplectic group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §5.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

The organization follows the type-`A` carrier field-points file
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FieldPoints`.
-/

public section

namespace TauCeti.SpStd

universe u

variable (n : ℕ)

/-- **Over a field, the matrix points of the full-weight type `C_(n+1)` carrier are exactly the
standard symplectic group.** -/
theorem points_eq_GLSymplecticFin {K : Type u} [Field K] :
    points n K = GLSymplecticFin (n + 1) K := by
  apply le_antisymm
  · intro g hg
    exact mem_GLSymplecticFin_of_mem_points n hg
  · let H : Subgroup (GLSymplecticFin (n + 1) K) :=
      (points n K).comap (GLSymplecticFin (n + 1) K).subtype
    have hH : H = ⊤ := by
      apply GLSymplecticFin.eq_top_of_adjacent_of_long H (Fin.last n)
      · intro i j hij c hadjacent
        rcases hadjacent with hijSucc | hjiSucc
        · have hi : i ≠ Fin.last n := by
            intro hi
            subst i
            have hjlt := j.isLt
            simp only [Fin.val_last] at hijSucc
            omega
          have hj : next n i hi = j := Fin.ext (by simpa only [val_next] using hijSucc)
          subst j
          rw [Subgroup.mem_comap]
          have hroot := (rootSubgroupPoints n (.inl i) K (Multiplicative.ofAdd c)).property
          rw [coe_rootSubgroupPoints_inl_of_ne_last n i hi c] at hroot
          exact hroot
        · have hj : j ≠ Fin.last n := by
            intro hj
            subst j
            have hilt := i.isLt
            simp only [Fin.val_last] at hjiSucc
            omega
          have hi : next n j hj = i := Fin.ext (by simpa only [val_next] using hjiSucc)
          subst i
          rw [Subgroup.mem_comap]
          have hroot := (rootSubgroupPoints n (.inr j) K (Multiplicative.ofAdd c)).property
          rw [coe_rootSubgroupPoints_inr_of_ne_last n j hj c] at hroot
          exact hroot
      · intro c
        rw [Subgroup.mem_comap]
        have hroot :=
          (rootSubgroupPoints n (.inl (Fin.last n)) K (Multiplicative.ofAdd c)).property
        rw [coe_rootSubgroupPoints_inl_last n c] at hroot
        exact hroot
      · intro c
        rw [Subgroup.mem_comap]
        have hroot :=
          (rootSubgroupPoints n (.inr (Fin.last n)) K (Multiplicative.ofAdd c)).property
        rw [coe_rootSubgroupPoints_inr_last n c] at hroot
        exact hroot
    intro g hg
    have : (⟨g, hg⟩ : GLSymplecticFin (n + 1) K) ∈ H := by
      rw [hH]
      exact Subgroup.mem_top _
    change (GLSymplecticFin (n + 1) K).subtype ⟨g, hg⟩ ∈ points n K at this
    simpa only [Subgroup.subtype_apply] using this

end TauCeti.SpStd
