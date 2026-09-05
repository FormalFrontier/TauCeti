/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.LinearAlgebra.JordanChevalley.Commuting

/-!
# Jordan decomposition of commuting algebraic-group points

The Jordan decomposition of algebraic-group points respects commuting products. If two points
commute, then all of their reconstructed Jordan factors commute across the two decompositions,
and the semisimple and unipotent parts of their product are the corresponding products.

The proof checks the linear result in every finite-dimensional comodule and then uses Tannakian
reconstruction to separate points. This compatibility completes a standard structural property
of the pointwise Jordan decomposition constructed in Layer 4 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.HopfAlgebra.Point.commute_semisimplePart_left_of_commute` and
  `TauCeti.HopfAlgebra.Point.commute_unipotentPart_left_of_commute`: each Jordan factor commutes
  with every point commuting with the original point.
* `TauCeti.HopfAlgebra.Point.commute_semisimplePart_semisimplePart_of_commute`: semisimple parts
  of commuting points commute.
* `TauCeti.HopfAlgebra.Point.commute_semisimplePart_unipotentPart_of_commute` and
  `TauCeti.HopfAlgebra.Point.commute_unipotentPart_semisimplePart_of_commute`: the two
  cross-commutation statements.
* `TauCeti.HopfAlgebra.Point.commute_unipotentPart_unipotentPart_of_commute`: unipotent parts of
  commuting points commute.
* `TauCeti.HopfAlgebra.Point.jordanDecomposition_mul_of_commute`: the ordered decomposition of a
  commuting product is the componentwise product.
* `TauCeti.HopfAlgebra.Point.semisimplePart_mul_of_commute` and
  `TauCeti.HopfAlgebra.Point.unipotentPart_mul_of_commute`: the two factor formulas.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open LinearMap WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra
namespace Point

universe u

variable (k H K : Type u) [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- The semisimple factor of a point commutes with every point that commutes with the original
point. -/
theorem commute_semisimplePart_left_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (semisimplePart k H K g) h := by
  apply (Tannaka.commute_iff_forall_ofLinearEquiv_pointsAction k H K).2
  intro M
  rw [ofLinearEquiv_pointsAction_semisimplePart]
  exact GeneralLinearGroup.commute_semisimplePart_left_of_commute
    ((GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
      (hgh.map (Comodule.pointsAction M)))

/-- The unipotent factor of a point commutes with every point that commutes with the original
point. -/
theorem commute_unipotentPart_left_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (unipotentPart k H K g) h := by
  apply (Tannaka.commute_iff_forall_ofLinearEquiv_pointsAction k H K).2
  intro M
  rw [ofLinearEquiv_pointsAction_unipotentPart]
  exact GeneralLinearGroup.commute_unipotentPart_left_of_commute
    ((GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
      (hgh.map (Comodule.pointsAction M)))

/-- The semisimple parts of two commuting algebraic-group points commute. -/
theorem commute_semisimplePart_semisimplePart_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (semisimplePart k H K g) (semisimplePart k H K h) :=
  commute_semisimplePart_left_of_commute k H K
    (commute_semisimplePart_left_of_commute k H K hgh.symm).symm

/-- The semisimple part of the first of two commuting points commutes with the unipotent part of
the second. -/
theorem commute_semisimplePart_unipotentPart_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (semisimplePart k H K g) (unipotentPart k H K h) :=
  commute_semisimplePart_left_of_commute k H K
    (commute_unipotentPart_left_of_commute k H K hgh.symm).symm

/-- The unipotent part of the first of two commuting points commutes with the semisimple part of
the second. -/
theorem commute_unipotentPart_semisimplePart_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (unipotentPart k H K g) (semisimplePart k H K h) :=
  commute_unipotentPart_left_of_commute k H K
    (commute_semisimplePart_left_of_commute k H K hgh.symm).symm

/-- The unipotent parts of two commuting algebraic-group points commute. -/
theorem commute_unipotentPart_unipotentPart_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    Commute (unipotentPart k H K g) (unipotentPart k H K h) :=
  commute_unipotentPart_left_of_commute k H K
    (commute_unipotentPart_left_of_commute k H K hgh.symm).symm

/-- The semisimple part of a product of commuting algebraic-group points is the product of their
semisimple parts. -/
theorem semisimplePart_mul_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    semisimplePart k H K (g * h) =
      semisimplePart k H K g * semisimplePart k H K h := by
  apply Tannaka.fgPoint_ext_of_forall_ofLinearEquiv_pointsAction k H K
  intro M
  simp only [ofLinearEquiv_pointsAction_semisimplePart, map_mul,
    GeneralLinearGroup.ofLinearEquiv_mul]
  exact GeneralLinearGroup.semisimplePart_mul_of_commute
    ((GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
      (hgh.map (Comodule.pointsAction M)))

/-- The unipotent part of a product of commuting algebraic-group points is the product of their
unipotent parts. -/
theorem unipotentPart_mul_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    unipotentPart k H K (g * h) =
      unipotentPart k H K g * unipotentPart k H K h := by
  apply Tannaka.fgPoint_ext_of_forall_ofLinearEquiv_pointsAction k H K
  intro M
  simp only [ofLinearEquiv_pointsAction_unipotentPart, map_mul,
    GeneralLinearGroup.ofLinearEquiv_mul]
  exact GeneralLinearGroup.unipotentPart_mul_of_commute
    ((GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
      (hgh.map (Comodule.pointsAction M)))

/-- The Jordan decomposition of a product of commuting algebraic-group points is the
componentwise product of their Jordan decompositions. -/
theorem jordanDecomposition_mul_of_commute
    {g h : WithConv (H →ₐ[k] K)} (hgh : Commute g h) :
    jordanDecomposition k H K (g * h) =
      (semisimplePart k H K g * semisimplePart k H K h,
        unipotentPart k H K g * unipotentPart k H K h) := by
  apply Prod.ext
  · simpa only [jordanDecomposition_fst] using
      semisimplePart_mul_of_commute k H K hgh
  · simpa only [jordanDecomposition_snd] using
      unipotentPart_mul_of_commute k H K hgh

end Point
end TauCeti.HopfAlgebra
