/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The special linear group is reductive

The coordinate Hopf algebra of `SL_n` is reductive over every field and in every natural rank.
The proof uses the geometric definition, so it works in arbitrary characteristic.

Smoothness and geometric connectedness are established directly for the special-linear
coordinate algebra. Over an algebraically closed field, smoothness makes a subgroup coordinate
ring reduced, while geometric unipotence says that all of its points act unipotently. The general
normal-invariants theorem then makes the subgroup act trivially on every completely reducible
ambient representation. The standard representation of `SL_n` is simple in positive rank, hence
completely reducible, and it is faithful in every rank. Faithfulness therefore identifies the
subgroup's defining ideal with the augmentation ideal. The zero-rank case is handled directly
using the zero-dimensional standard representation.

The final theorem transports the normal-subgroup argument across the canonical identification

`AlgebraicClosure k ⊗[k] O(SL_n) ≃ O(SL_n, AlgebraicClosure k)`.

Its final reductivity assembly is adapted from
`TauCeti.GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`, with the
common geometric-fibre transport factored through the generic reductivity API.

## Main declaration

* `TauCeti.SpecialLinear.eq_augmentation_of_isNormal_of_smoothUnipotent`: a normal smooth
  unipotent closed subgroup of `SL_n` over an algebraically closed field is the identity subgroup.
* `TauCeti.SpecialLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`SL_n` is reductive.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 5, 19.b, and Chapter 14.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.

This completes the `SL_n` worked example in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u

noncomputable section

open HopfIdeal

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (n : Nat) :
    coordinateHopfAlgebra R n ≅ (finiteTypeCoordinateHopfAlgebra R n).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n).symm

/-- A normal smooth unipotent closed subgroup of `SL_n` over an algebraically closed field is
trivial. No positivity hypothesis on `n` is needed. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    (k : Type u) [Field k] [IsAlgClosed k] (n : Nat)
    (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)) :
    I = HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k n) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  let f : coordinateHopfAlgebra k n →ₐc[k] (finiteTypeCoordinateHopfAlgebra k n) :=
    CommHopfAlgCat.ofIso e
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.hom
  let J : HopfIdeal k (coordinateHopfAlgebra k n) := I.comapOfSurjective f hf.2
  have hJnormal : J.IsNormal := hI.comapOfSurjective_of_bijective f hf.1 hf.2
  let qIso : CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J ≅
      CommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n).obj I :=
    CommHopfAlgCat.quotientIsoOfIso e I
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)).mp hU
  let _ : Algebra.Smooth k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso qIso.symm
        ((smoothCommHopfAlgProperty_iff _).mpr hU'.1)
  have hJunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (geometricallyUnipotentPointsCommHopfAlgProperty k).prop_of_iso qIso.symm
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU'.2)
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    isReduced_of_smooth_of_field k _
  let _ : IsReduced (coordinateHopfAlgebra k n) := isReduced_of_smooth_of_field k _
  let _ : Comodule k (coordinateHopfAlgebra k n) (Fin n → k) := standardComodule k n
  have hu :=
    geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint hJunipotent
  have hcr : Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k n) (Fin n → k) := by
    cases n with
    | zero => exact Comodule.isCompletelyReducible_of_subsingleton
    | succ n =>
        let _ : NeZero n.succ := ⟨Nat.succ_ne_zero n⟩
        exact Comodule.isCompletelyReducible_of_isSimpleOrder
  have htrivial :=
    mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
      hJnormal hu hcr
  have hJ : J = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) :=
    Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one J
      (isFaithful_standardComodule k n) htrivial
  rw [← HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff f hf.2,
    HopfIdeal.comapOfSurjective_augmentation]
  exact hJ

/-- **The special linear group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  let e₀ := coordinateHopfAlgebraFiniteTypeObjIso k n
  apply reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
    (finiteTypeCoordinateHopfAlgebra (AlgebraicClosure k) n)
    ((smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e₀
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e₀
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n))
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) n)
  intro I hI hU
  exact eq_augmentation_of_isNormal_of_smoothUnipotent
    (AlgebraicClosure k) n I hI hU

end

end TauCeti.SpecialLinear
