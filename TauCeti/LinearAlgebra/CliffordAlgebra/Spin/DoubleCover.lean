/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Surjectivity
public import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The Spin double cover as a group extension

For a positive-dimensional finite nondegenerate quadratic space, the kernel of the Spin action
is canonically identified with the multiplicative group underlying `ZMod 2`. Over a separably
closed field, surjectivity of the action then packages the Spin double cover as a
`GroupExtension`.

## Main definitions

* `TauCeti.CliffordAlgebra.spinKernelEquivZModTwo` identifies the kernel with
  `Multiplicative (ZMod 2)`.
* `TauCeti.CliffordAlgebra.spinDoubleCover` packages
  `1 → ZMod 2 → Spin(Q) → SO(Q) → 1` as a group extension.

## References

This completes the short-exact-sequence part of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra

namespace TauCeti.CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- The kernel of the Spin action on a positive-dimensional nondegenerate quadratic space is
canonically the cyclic group of order two, with its generator sent to the scalar `-1`. -/
noncomputable def spinKernelEquivZModTwo
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Multiplicative (ZMod 2) ≃* MonoidHom.ker (spinToSpecialOrthogonal Q) := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  let z : MonoidHom.ker (spinToSpecialOrthogonal Q) :=
    ⟨spinGroup.negOne Q hQ.ne_zero,
      spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ.ne_zero⟩
  apply zmodMulEquivOfGenerator (g := z)
  · intro x
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).mp x.2 with hx | hx
    · have hx' : x = 1 := Subtype.ext hx
      rw [hx']
      exact Subgroup.one_mem _
    · have hx' : x = z := Subtype.ext hx
      rw [hx']
      exact Subgroup.mem_zpowers z
  · exact card_ker_spinToSpecialOrthogonal hV Q hQ

/-- The chosen generator of `Multiplicative (ZMod 2)` maps to the scalar `-1` in the Spin
kernel. -/
@[simp]
theorem spinKernelEquivZModTwo_apply_ofAdd_one
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinKernelEquivZModTwo hV Q hQ (Multiplicative.ofAdd 1) =
      ⟨spinGroup.negOne Q (by
          let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
          exact hQ.ne_zero),
        spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q
          (by
            let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
            exact hQ.ne_zero)⟩ := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  rw [spinKernelEquivZModTwo, zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- Over a separably closed field, the Spin action is the group extension
`1 → ZMod 2 → Spin(Q) → SO(Q) → 1`. -/
noncomputable def spinDoubleCover [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (QuadraticMap.specialOrthogonalGroup Q) where
  inl := (MonoidHom.ker (spinToSpecialOrthogonal Q)).subtype.comp
    (spinKernelEquivZModTwo hV Q hQ).toMonoidHom
  rightHom := spinToSpecialOrthogonal Q
  inl_injective := fun x y h =>
    (spinKernelEquivZModTwo hV Q hQ).injective (Subtype.ext h)
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp]
    have hrange : (spinKernelEquivZModTwo hV Q hQ).toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (spinKernelEquivZModTwo hV Q hQ).surjective
    rw [hrange, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rightHom_surjective := spinToSpecialOrthogonal_surjective Q hQ

/-- The inclusion in the Spin double cover sends the generator to the scalar `-1`. -/
@[simp]
theorem spinDoubleCover_inl_ofAdd_one [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover hV Q hQ).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q (by
        let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
        exact hQ.ne_zero) := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  -- Expose the kernel subtype beneath the bundled extension inclusion.
  change ((spinKernelEquivZModTwo hV Q hQ (Multiplicative.ofAdd 1) :
    MonoidHom.ker (spinToSpecialOrthogonal Q)) : spinGroup Q) = _
  rw [spinKernelEquivZModTwo_apply_ofAdd_one]

/-- The projection in the Spin double cover is the Spin action. -/
@[simp]
theorem spinDoubleCover_rightHom [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover hV Q hQ).rightHom = spinToSpecialOrthogonal Q := by
  rfl

end TauCeti.CliffordAlgebra
