/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# Duals of finite-dimensional comodules

This file bundles the linear dual of a finite-dimensional right comodule over a Hopf algebra as
an object of `FGComoduleCat`. The underlying coaction is the basis-free dual coaction constructed
in `TauCeti.Algebra.Coalgebra.Comodule.Dual`.

## Main declaration

* `TauCeti.FGComoduleCat.dual`: the finite-dimensional dual comodule.

## References

This is the finite-dimensional specialization of the standard dual-comodule construction; see
Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open CategoryTheory

namespace TauCeti.FGComoduleCat

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [Semiring H] [HopfAlgebra k H]

attribute [local instance] Comodule.dual

/-- The linear dual of a finite-dimensional right comodule, with the coaction induced by the
antipode. -/
noncomputable abbrev dual (M : FGComoduleCat.{u, v, u} k H) :
    FGComoduleCat.{u, v, u} k H :=
  of (R := k) (C := H) (Module.Dual k M)

/-- The ambient comodule underlying the finite dual is the linear dual equipped with
`Comodule.dual`. -/
@[simp]
theorem dual_obj (M : FGComoduleCat.{u, v, u} k H) :
    (dual k H M).obj = ComoduleCat.of k H (Module.Dual k M) :=
  rfl

/-- The carrier of the finite dual is the ordinary linear dual. -/
@[simp]
theorem dual_coe (M : FGComoduleCat.{u, v, u} k H) :
    (dual k H M : Type u) = Module.Dual k M :=
  rfl

/-- The coaction on the finite dual is the basis-free dual coaction. -/
theorem dual_coact (M : FGComoduleCat.{u, v, u} k H) :
    Comodule.coact (R := k) (C := H) (M := dual k H M) =
      Comodule.dualCoact (R := k) (H := H) (M := M) :=
  Comodule.dual_coact (R := k) (H := H) (M := M)

/-- The inclusion into all comodules sends the finite dual to the ambient dual comodule. -/
@[simp]
theorem incl_dual (M : FGComoduleCat.{u, v, u} k H) :
    (incl (R := k) (C := H)).obj (dual k H M) =
      ComoduleCat.of k H (Module.Dual k M) :=
  rfl

/-- Forgetting the finite dual to semimodules gives the ordinary linear-dual module. -/
@[simp]
theorem forget₂_semimoduleCat_dual_obj (M : FGComoduleCat.{u, v, u} k H) :
    (forget₂ (FGComoduleCat.{u, v, u} k H) (SemimoduleCat.{u} k)).obj (dual k H M) =
      SemimoduleCat.of k (Module.Dual k M) :=
  rfl

end TauCeti.FGComoduleCat
