/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful

/-!
# The general linear group is reductive

The coordinate Hopf algebra of `GL_n` is reductive over every field and in every natural rank.
The proof uses the geometric definition, so it works in arbitrary characteristic.

First, the determinant localization defining `O(GL_n)` is smooth and geometrically connected.
For the normal-subgroup condition, work over an algebraically closed field and let `I` cut out a
normal smooth unipotent closed subgroup. The simple standard `GL_n`-comodule is completely
reducible, so the general normal-unipotent elimination theorem makes the subgroup act trivially.
Faithfulness of the standard representation then identifies `I` with the augmentation ideal.

The final theorem transports this argument across the canonical identification

`AlgebraicClosure k ⊗[k] O(GL_n) ≃ O(GL_n, AlgebraicClosure k)`.

## Main declarations

* `TauCeti.GeneralLinear.eq_augmentation_of_isNormal_of_smoothUnipotent`: a normal smooth
  unipotent closed subgroup of `GL_n` over an algebraically closed field is trivial.
* `TauCeti.GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`GL_n` is reductive.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 5, 19.b, and Chapter 14.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.

This gives the reductivity half of the `GL_n` worked example requested alongside Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. The characteristic-zero
complete-reducibility route remains open.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

open HopfIdeal

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (n : Nat) :
    coordinateHopfAlgebra R n ≅ (finiteTypeCoordinateHopfAlgebra R n).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n).symm

/-- A normal smooth unipotent closed subgroup of `GL_n` over an algebraically closed field is
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
  let H : FiniteTypeCommHopfAlgCat k :=
    ⟨coordinateHopfAlgebra k n, by
      rw [← finiteTypeCoordinateHopfAlgebra_obj]
      exact (finiteTypeCoordinateHopfAlgebra k n).property⟩
  let qIso' : FiniteTypeCommHopfAlgCat.quotient H J ≅
      FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I :=
    ObjectProperty.isoMk _ qIso
  have hUJ : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H J) :=
    (smoothUnipotentCommHopfAlgProperty k).prop_of_iso qIso'.symm hU
  let _ : IsReduced H := by
    change IsReduced (coordinateHopfAlgebra k n)
    exact isReduced_of_smooth_of_field k _
  let _ : Comodule k (coordinateHopfAlgebra k n) (Fin n → k) := standardComodule k n
  have hcr : Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k n) (Fin n → k) := by
    cases n with
    | zero => exact Comodule.isCompletelyReducible_of_subsingleton
    | succ n =>
        let _ : NeZero n.succ := ⟨Nat.succ_ne_zero n⟩
        exact Comodule.isCompletelyReducible_of_isSimpleOrder
  have hJ : J = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) :=
    HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful k H (Fin n → k)
      hcr (isFaithful_standardComodule k n) J hJnormal hUJ
  rw [← HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff f hf.2,
    HopfIdeal.comapOfSurjective_augmentation]
  exact hJ

/-- **The general linear group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  apply reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
    (finiteTypeCoordinateHopfAlgebra (AlgebraicClosure k) n)
    ((smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n))
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) n)
  intro I hI hU
  exact eq_augmentation_of_isNormal_of_smoothUnipotent
    (AlgebraicClosure k) n I hI hU

end

end TauCeti.GeneralLinear
