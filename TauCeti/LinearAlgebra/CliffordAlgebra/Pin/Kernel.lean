/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel

/-!
# The kernel of the Pin action

For a positive-dimensional finite nondegenerate quadratic space over a field where `2` is
invertible, the kernel of the Pin action is canonically the cyclic group of order two. The proof
identifies a Pin element acting trivially with an even element, then reuses the Spin-kernel
classification.

## Main results

* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal`: the kernel is canonically
  equivalent to `Multiplicative (ZMod 2)`.
* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one`: the chosen
  generator maps to the scalar `-1` inside the Pin group.
* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal_symm_apply_negOne`: the inverse
  sends the scalar `-1` to the chosen generator.

## References

This completes the Pin-kernel part of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace CliffordAlgebra

universe u v

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

private noncomputable def pinKernelToSpinKernel
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (x : MonoidHom.ker (pinToOrthogonal Q)) :
    MonoidHom.ker (spinToSpecialOrthogonal Q) :=
  let s : spinGroup Q :=
    ⟨x, x.1.2, mem_even_of_det_pinToOrthogonal_eq_one Q x.1 (by
      rw [MonoidHom.mem_ker.mp x.2]
      simp)⟩
  ⟨s, by
    rw [ker_spinToSpecialOrthogonal, MonoidHom.mem_ker, ← pinToOrthogonal_spinToPin]
    have hspinpin : spinToPin Q s = x.1 := Subtype.ext (coe_spinToPin_apply s)
    rw [hspinpin]
    exact MonoidHom.mem_ker.mp x.2⟩

private noncomputable def kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal
    (Q : QuadraticForm K M) [Invertible (2 : K)] :
    MonoidHom.ker (spinToSpecialOrthogonal Q) ≃*
      MonoidHom.ker (pinToOrthogonal Q) where
  toFun x :=
    ⟨spinToPin Q x, by
      rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin]
      exact MonoidHom.mem_ker.mp (ker_spinToSpecialOrthogonal Q ▸ x.2)⟩
  invFun := pinKernelToSpinKernel Q
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only
    exact coe_spinToPin_apply x.1
  right_inv x := by
    apply Subtype.ext
    simp only
    apply Subtype.ext
    exact coe_spinToPin_apply (pinKernelToSpinKernel Q x).1
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (map_mul (spinToPin Q) x.1 y.1)

private theorem kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal_apply
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (x : MonoidHom.ker (spinToSpecialOrthogonal Q)) :
    (kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal Q x).1 =
      spinToPin Q x.1 :=
  rfl

/-- The kernel of the Pin action on a positive-dimensional nondegenerate quadratic space over a
field in which `2` is invertible is canonically the cyclic group of order two, with its generator
sent to the scalar `-1`. -/
noncomputable def zmodTwoMulEquivKerPinToOrthogonal [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    Multiplicative (ZMod 2) ≃* MonoidHom.ker (pinToOrthogonal Q) :=
  (zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).trans
    (kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal Q)

/-- The chosen generator of `Multiplicative (ZMod 2)` maps to the scalar `-1` in the Pin
kernel. -/
@[simp]
theorem zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    zmodTwoMulEquivKerPinToOrthogonal Q hQ (Multiplicative.ofAdd 1) =
      ⟨spinToPin Q (spinGroup.negOne Q hQ.ne_zero), by
        rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin,
          spinGroup.spinToOrthogonal_negOne]⟩ := by
  apply Subtype.ext
  rw [zmodTwoMulEquivKerPinToOrthogonal, MulEquiv.trans_apply,
    kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal_apply]
  exact congrArg (spinToPin Q) <| congrArg Subtype.val
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one Q hQ)

/-- The inverse kernel equivalence sends the scalar `-1` to the chosen generator of
`Multiplicative (ZMod 2)`. -/
@[simp]
theorem zmodTwoMulEquivKerPinToOrthogonal_symm_apply_negOne [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    (zmodTwoMulEquivKerPinToOrthogonal Q hQ).symm
        ⟨spinToPin Q (spinGroup.negOne Q hQ.ne_zero), by
          rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin,
            spinGroup.spinToOrthogonal_negOne]⟩ =
      Multiplicative.ofAdd 1 := by
  rw [MulEquiv.symm_apply_eq]
  exact (zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one Q hQ).symm

end CliffordAlgebra
