/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Reduction of commutative Hopf algebras

Let `H` be a commutative Hopf algebra over a reduced commutative ring. Its nilradical is
automatically stable under the counit and antipode. It is stable under comultiplication provided
the tensor square of the reduced algebra is reduced: the image of a nilpotent element under
comultiplication is nilpotent, hence vanishes in that tensor square. This packages the nilradical
as a Hopf ideal under precisely that hypothesis.

The tensor-square hypothesis is the algebraic condition needed for reduction to commute with a
product. It holds, in particular, for finite-type algebras over a perfect field once the standard
geometric-reducedness theorem is available. Keeping it explicit here separates the Hopf-algebra
argument from that commutative-algebra input.

## Main declarations

* `TauCeti.HopfIdeal.reduction`: the nilradical, packaged as a Hopf ideal.
* `TauCeti.HopfIdeal.reduction_toIdeal`: its underlying ideal is the nilradical.
* `TauCeti.HopfIdeal.mem_reduction`: membership is nilpotence.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), §1.f.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v

variable (R : Type u) [CommRing R] [IsReduced R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

private theorem nilradical_counit_eq_zero {x : H} (hx : x ∈ nilradical H) :
    Coalgebra.counit (R := R) x = 0 := by
  rw [mem_nilradical] at hx
  exact isNilpotent_iff_eq_zero.mp (hx.map (Bialgebra.counitAlgHom R H))

omit [IsReduced R] in
private theorem nilradical_antipode_mem {x : H} (hx : x ∈ nilradical H) :
    HopfAlgebra.antipode R x ∈ nilradical H := by
  rw [mem_nilradical] at hx ⊢
  simpa only [HopfAlgebra.antipodeAlgHom_apply] using
    hx.map (HopfAlgebra.antipodeAlgHom R H)

omit [IsReduced R] in
private theorem nilradical_comul_mem
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {x : H} (hx : x ∈ nilradical H) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := H) (nilradical H) ⊔
        rightTensorIdeal (R := R) (H := H) (nilradical H) := by
  let q : H →ₐ[R] H ⧸ nilradical H := Ideal.Quotient.mkₐ R (nilradical H)
  have hnil : IsNilpotent (Coalgebra.comul (R := R) x) :=
    (mem_nilradical.mp hx).map (Bialgebra.comulAlgHom R H)
  have hzero : Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) x) = 0 :=
    isNilpotent_iff_eq_zero.mp (hnil.map (Algebra.TensorProduct.map q q))
  have hmem : Coalgebra.comul (R := R) x ∈
      RingHom.ker (Algebra.TensorProduct.map q q).toRingHom := by
    rw [RingHom.mem_ker]
    exact hzero
  rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at hmem
  rw [AlgHom.tensor_map_ker_eq_left_sup_right q
    (Ideal.Quotient.mkₐ_surjective R (nilradical H))] at hmem
  rw [← RingHom.ker_coe_toRingHom q, Ideal.Quotient.mkₐ_ker] at hmem
  exact hmem

/-- The nilradical of a commutative Hopf algebra, as a Hopf ideal.

The tensor square of the reduced algebra must be reduced. This is exactly what makes the
comultiplication descend: a nilpotent element maps to a nilpotent element of that tensor square
and therefore to zero. -/
noncomputable def reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] : HopfIdeal R H :=
  ofIdeal (nilradical H)
    (fun {x} hx ↦ nilradical_comul_mem R H (x := x) hx)
    (fun {x} hx ↦ nilradical_counit_eq_zero R H (x := x) hx)
    (fun {x} hx ↦ nilradical_antipode_mem R H (x := x) hx)

/-- The underlying ideal of the reduction Hopf ideal is the nilradical. -/
@[simp]
theorem reduction_toIdeal
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] :
    (reduction R H).toIdeal = nilradical H := by
  rw [reduction, toIdeal_carrier, ofIdeal_carrier]

/-- Membership in the reduction Hopf ideal is nilpotence. -/
@[simp]
theorem mem_reduction
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))] {x : H} :
    x ∈ reduction R H ↔ IsNilpotent x := by
  rw [← mem_toIdeal, reduction_toIdeal, mem_nilradical]

end TauCeti.HopfIdeal
