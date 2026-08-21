/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic

/-!
# The Cartan generators of a Lie algebra basis as a module basis

A `LieAlgebra.Basis ι H` carries a family `h : ι → H` of Cartan generators which is linearly
independent and spans `H`. This file packages that data as a `Module.Basis` of `H` and reads off
the dimension of `H`.

## Main definitions

* `LieAlgebra.Basis.cartanBasis`: the Cartan generators as a module basis of the Cartan
  subalgebra.
-/

public section

namespace LieAlgebra.Basis

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L}

/-- The Cartan generators of a Lie algebra basis form a module basis of its Cartan subalgebra. -/
noncomputable def cartanBasis (b : Basis ι H) : Module.Basis ι R H :=
  (Module.Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm

/-- The vectors of `LieAlgebra.Basis.cartanBasis` are the Cartan generators. -/
@[simp] theorem coe_cartanBasis (b : Basis ι H) (i : ι) :
    (b.cartanBasis i : L) = b.h i := by
  simp only [cartanBasis, Module.Basis.map_apply, Module.Basis.span_apply,
    LinearEquiv.ofEq_symm]
  exact LinearEquiv.coe_ofEq_apply _ _

/-- The Cartan subalgebra has dimension the cardinality of the basis's index type. -/
theorem finrank_cartan [StrongRankCondition R] (b : Basis ι H) :
    Module.finrank R H = Nat.card ι :=
  Module.finrank_eq_nat_card_basis b.cartanBasis

end LieAlgebra.Basis
