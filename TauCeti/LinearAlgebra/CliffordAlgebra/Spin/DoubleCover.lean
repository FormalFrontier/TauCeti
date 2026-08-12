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

For a positive-dimensional finite nondegenerate quadratic space over a field in which `2` is
invertible, the kernel of the Spin action is canonically identified with the multiplicative group
underlying `ZMod 2`. Any proof that the action is surjective then packages the Spin double cover as
a `GroupExtension`; in particular, the action is surjective over a separably closed field.

## Main definitions

* `TauCeti.CliffordAlgebra.zmodTwoMulEquivSpinKernel` identifies the kernel with
  `Multiplicative (ZMod 2)`.
* `TauCeti.CliffordAlgebra.spinDoubleCoverOfSurjective` packages any surjective Spin action as a
  group extension.
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

/-- The kernel of the Spin action on a positive-dimensional nondegenerate quadratic space over a
field in which `2` is invertible is canonically the cyclic group of order two, with its generator
sent to the scalar `-1`. -/
noncomputable def zmodTwoMulEquivSpinKernel
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
theorem zmodTwoMulEquivSpinKernel_apply_ofAdd_one
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    zmodTwoMulEquivSpinKernel hV Q hQ (Multiplicative.ofAdd 1) =
      ⟨spinGroup.negOne Q (by
          let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
          exact hQ.ne_zero),
        spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q
          (by
            let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
            exact hQ.ne_zero)⟩ := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  rw [zmodTwoMulEquivSpinKernel, zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- The inverse kernel equivalence sends the scalar `-1` to the chosen generator of
`Multiplicative (ZMod 2)`. -/
@[simp]
theorem zmodTwoMulEquivSpinKernel_symm_apply_negOne
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (zmodTwoMulEquivSpinKernel hV Q hQ).symm
        ⟨spinGroup.negOne Q (by
            let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
            exact hQ.ne_zero),
          spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q
            (by
              let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
              exact hQ.ne_zero)⟩ =
      Multiplicative.ofAdd 1 := by
  rw [MulEquiv.symm_apply_eq, zmodTwoMulEquivSpinKernel_apply_ofAdd_one]

/-- A surjective Spin action on a positive-dimensional nondegenerate quadratic space over a field
in which `2` is invertible is the group extension `1 → ZMod 2 → Spin(Q) → SO(Q) → 1`. -/
noncomputable def spinDoubleCoverOfSurjective
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (QuadraticMap.specialOrthogonalGroup Q) where
  inl := (MonoidHom.ker (spinToSpecialOrthogonal Q)).subtype.comp
    (zmodTwoMulEquivSpinKernel hV Q hQ).toMonoidHom
  rightHom := spinToSpecialOrthogonal Q
  inl_injective := fun x y h =>
    (zmodTwoMulEquivSpinKernel hV Q hQ).injective (Subtype.ext h)
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp]
    have hrange : (zmodTwoMulEquivSpinKernel hV Q hQ).toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (zmodTwoMulEquivSpinKernel hV Q hQ).surjective
    rw [hrange, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rightHom_surjective := hsurj

/-- The inclusion in a Spin double cover built from a surjectivity proof sends the generator to
the scalar `-1`. -/
@[simp]
theorem spinDoubleCoverOfSurjective_inl_ofAdd_one
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    (spinDoubleCoverOfSurjective hV Q hQ hsurj).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q (by
        let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
        exact hQ.ne_zero) := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  -- Expose the kernel subtype beneath the bundled extension inclusion.
  change ((zmodTwoMulEquivSpinKernel hV Q hQ (Multiplicative.ofAdd 1) :
    MonoidHom.ker (spinToSpecialOrthogonal Q)) : spinGroup Q) = _
  rw [zmodTwoMulEquivSpinKernel_apply_ofAdd_one]

/-- The projection in a Spin double cover built from a surjectivity proof is the Spin action. -/
@[simp]
theorem spinDoubleCoverOfSurjective_rightHom
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    (spinDoubleCoverOfSurjective hV Q hQ hsurj).rightHom = spinToSpecialOrthogonal Q := by
  rfl

/-- Over a separably closed field in which `2` is invertible, the Spin action is the group
extension `1 → ZMod 2 → Spin(Q) → SO(Q) → 1`. -/
noncomputable def spinDoubleCover [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (QuadraticMap.specialOrthogonalGroup Q) :=
  spinDoubleCoverOfSurjective hV Q hQ (spinToSpecialOrthogonal_surjective Q hQ)

/-- The inclusion in the separably closed Spin double cover sends the generator to the scalar
`-1`. -/
@[simp]
theorem spinDoubleCover_inl_ofAdd_one [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover hV Q hQ).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q (by
        let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hV
        exact hQ.ne_zero) := by
  rw [spinDoubleCover, spinDoubleCoverOfSurjective_inl_ofAdd_one]

/-- The projection in the separably closed Spin double cover is the Spin action. -/
@[simp]
theorem spinDoubleCover_rightHom [IsSepClosed K]
    (hV : 0 < Module.finrank K V) (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCover hV Q hQ).rightHom = spinToSpecialOrthogonal Q := by
  rw [spinDoubleCover, spinDoubleCoverOfSurjective_rightHom]

end TauCeti.CliffordAlgebra
