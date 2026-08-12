/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Unit
public import TauCeti.Algebra.Coalgebra.Subcomodule.DirectedUnion

/-!
# Global functionals from tensor automorphisms

Let `H` be a Hopf algebra over a field `k`, and let `A` be a commutative `k`-algebra. A tensor
automorphism of scalar extension on the finite-dimensional `H`-comodules determines a compatible
linear functional on every finite subcomodule of the regular comodule. Since these subcomodules
cover `H`, the local functionals glue uniquely to a linear map

```text
g_η : H → A.
```

This file performs that gluing, proves that `g_η` preserves one, and proves that a tensor
automorphism arising from an `A`-valued point recovers the underlying linear map of that point.
Tensor compatibility will next show that `g_η` preserves multiplication, upgrading it to an
algebra-valued point.

## Main declarations

* `TauCeti.Tannaka.globalFunctional`: the linear map obtained by gluing the local functionals.
* `TauCeti.Tannaka.globalFunctional_comp_subtype`: its restriction to a finite regular
  subcomodule is the prescribed local functional.
* `TauCeti.Tannaka.globalFunctional_unique`: the restriction property uniquely characterizes
  the global functional.
* `TauCeti.Tannaka.globalFunctional_one`: the global functional preserves the unit.
* `TauCeti.Tannaka.globalFunctional_fgPointTensorIso`: a point-induced tensor automorphism
  recovers the point's underlying linear map.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- The global linear functional obtained by gluing the functionals extracted from a tensor
automorphism on all finite subcomodules of the regular comodule. -/
noncomputable def globalFunctional
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    H →ₗ[k] A :=
  Subcomodule.finiteSubcomoduleLift
    (fun N ↦ localFunctional k H A η N)
    (localFunctional_eq_comp_inclusion k H A η)

/-- The global functional agrees with the extracted local functional on every finite regular
subcomodule. -/
@[simp]
theorem globalFunctional_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    globalFunctional k H A η n = localFunctional k H A η N n :=
  Subcomodule.finiteSubcomoduleLift_apply
    (fun Q ↦ localFunctional k H A η Q)
    (localFunctional_eq_comp_inclusion k H A η) N n

/-- Restricting the global functional to a finite regular subcomodule gives its local
functional. -/
@[simp]
theorem globalFunctional_comp_subtype
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    (globalFunctional k H A η).comp N.1.toSubmodule.subtype =
      localFunctional k H A η N :=
  Subcomodule.finiteSubcomoduleLift_comp_subtype
    (fun Q ↦ localFunctional k H A η Q)
    (localFunctional_eq_comp_inclusion k H A η) N

/-- The restrictions to finite regular subcomodules uniquely determine the global functional. -/
theorem globalFunctional_unique
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (g : H →ₗ[k] A)
    (hg : ∀ (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
      (n : N.1), g n = localFunctional k H A η N n) :
    g = globalFunctional k H A η :=
  Subcomodule.finiteSubcomoduleLift_unique
    (fun N ↦ localFunctional k H A η N)
    (localFunctional_eq_comp_inclusion k H A η) g hg

/-- The global functional extracted from a tensor automorphism sends the unit of the coordinate
Hopf algebra to the unit of the value algebra. -/
@[simp high]
theorem globalFunctional_one
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    globalFunctional k H A η 1 = 1 := by
  obtain ⟨N, hNfinite, hOne⟩ :=
    Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) (1 : H)
  let N' : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H) :=
    ⟨N, Subcomodule.mem_finiteSubcomodules.mpr hNfinite⟩
  calc
    globalFunctional k H A η 1 =
        globalFunctional k H A η (⟨1, hOne⟩ : N'.1) :=
      congrArg (globalFunctional k H A η) (Subtype.coe_mk 1 hOne).symm
    _ = localFunctional k H A η N' ⟨1, hOne⟩ :=
      globalFunctional_apply k H A η N' ⟨1, hOne⟩
    _ = 1 := localFunctional_one k H A η N' hOne

/-- The global functional associated to the tensor automorphism induced by an algebra-valued
point is the underlying linear map of that point. -/
@[simp]
theorem globalFunctional_fgPointTensorIso (g : WithConv (H →ₐ[k] A)) :
    globalFunctional k H A (fgPointTensorIso k H A g) = g.ofConv.toLinearMap := by
  symm
  apply globalFunctional_unique
  intro N n
  exact (localFunctional_fgPointTensorIso k H A g N n).symm

end TauCeti.Tannaka
