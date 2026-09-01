/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Maximal tori in Hopf coordinates

A closed subgroup of an affine group is encoded contravariantly by a Hopf ideal in its
coordinate algebra. This file defines a maximal torus to be a torus closed subgroup which is
not properly contained in another torus. Thus, if `I` is maximal and `J ≤ I` defines a torus,
then `I = J`.

The file also records that the coordinate Hopf algebra of a torus is cocommutative. Although
this is implicit in the definition by geometric splitting, making it available explicitly is
what lets existing results about commutative closed subgroup schemes consume a torus hypothesis.

## Main declarations

* `TauCeti.torusCommHopfAlgProperty.isCocomm`: the coordinate Hopf algebra of a torus is
  cocommutative.
* `TauCeti.HopfIdeal.IsMaximalTorus`: maximality among torus Hopf ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 17.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.

This supplies the Hopf-coordinate maximal-torus predicate required by Layer 7, "Borel subgroups,
maximal tori, and their conjugacy", of the ReductiveGroups roadmap. Existence and conjugacy of
maximal tori remain to be proved.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti

universe u

namespace Coalgebra.IsCocomm

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [_root_.Bialgebra R A] [_root_.Bialgebra R B]

/-- Cocommutativity transfers across a bialgebra equivalence. -/
private theorem of_bialgEquiv (e : A ≃ₐc[R] B) (_hA : _root_.Coalgebra.IsCocomm R A) :
    _root_.Coalgebra.IsCocomm R B where
  comm_comp_comul := by
    ext b
    apply (TensorProduct.map_bijective e.symm.bijective e.symm.bijective).injective
    simp only [LinearMap.comp_apply]
    change TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (TensorProduct.comm R B B (Coalgebra.comul (R := R) b)) = _
    rw [TensorProduct.map_comm]
    have hm :
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
            (Coalgebra.comul (R := R) b) =
          Coalgebra.comul (R := R) (e.symm b) :=
      CoalgHomClass.map_comp_comul_apply e.symm b
    rw [hm, Coalgebra.comm_comul]

end Coalgebra.IsCocomm

namespace Coalgebra.IsCocomm

variable {k K H : Type u} [Field k] [Field K] [Algebra k K]
  [CommRing H] [_root_.Bialgebra k H]

/-- Cocommutativity descends from a field extension. -/
private theorem of_baseChange (_h : _root_.Coalgebra.IsCocomm K (K ⊗[k] H)) :
    _root_.Coalgebra.IsCocomm k H where
  comm_comp_comul := by
    ext h
    apply Algebra.TensorProduct.includeRight_injective (B := H ⊗[k] H)
      (algebraMap k K).injective
    apply (Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H).injective
    have hc := Coalgebra.comm_comul K (1 ⊗ₜ[k] h : K ⊗[k] H)
    let e := Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
    have he_comm (x : H ⊗[k] H) :
        e (1 ⊗ₜ[k] TensorProduct.comm k H H x) =
          TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H) (e (1 ⊗ₜ[k] x)) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [map_add, LinearMap.map_add, TensorProduct.tmul_add] using
            congrArg₂ (· + ·) hx hy
      | tmul x y => simp [e]
    have he (x : H ⊗[k] H) :
        e (1 ⊗ₜ[k] x) =
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            k K k K K K H H ((1 ⊗ₜ[K] 1) ⊗ₜ[k] x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [map_add, LinearMap.map_add, TensorProduct.tmul_add] using
            congrArg₂ (· + ·) hx hy
      | tmul x y => simp [e]
    have he_comul :
        e (1 ⊗ₜ[k] Coalgebra.comul (R := k) h) =
          Coalgebra.comul (R := K) (1 ⊗ₜ[k] h : K ⊗[k] H) := by
      rw [he]
      rfl
    change e (1 ⊗ₜ[k]
        TensorProduct.comm k H H (Coalgebra.comul (R := k) h)) =
      e (1 ⊗ₜ[k] Coalgebra.comul (R := k) h)
    calc
      _ = TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
          (e (1 ⊗ₜ[k] Coalgebra.comul (R := k) h)) :=
        he_comm (Coalgebra.comul (R := k) h)
      _ = TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
          (Coalgebra.comul (R := K) (1 ⊗ₜ[k] h : K ⊗[k] H)) :=
        congrArg (TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)) he_comul
      _ = Coalgebra.comul (R := K) (1 ⊗ₜ[k] h : K ⊗[k] H) := hc
      _ = e (1 ⊗ₜ[k] Coalgebra.comul (R := k) h) := he_comul.symm

end Coalgebra.IsCocomm

/-- The coordinate Hopf algebra of a torus is cocommutative. -/
theorem torusCommHopfAlgProperty.isCocomm
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    _root_.Coalgebra.IsCocomm k H.obj := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  let hsplit : _root_.Coalgebra.IsCocomm (AlgebraicClosure k)
      (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
        (SplitTorus.characterGroup (ULift.{u} (Fin n)))).obj := inferInstance
  let hbase : _root_.Coalgebra.IsCocomm (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj :=
    Coalgebra.IsCocomm.of_bialgEquiv
      (_root_.CommHopfAlgCat.ofIso <|
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
          (_root_.CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i) hsplit
  exact Coalgebra.IsCocomm.of_baseChange hbase

namespace HopfIdeal

/-- A Hopf ideal defines a maximal torus when its quotient coordinate Hopf algebra is a torus
and every torus closed subgroup containing it is equal to it.

Because coordinate rings reverse arrows, `J ≤ I` says that the subgroup cut out by `I` is
contained in the subgroup cut out by `J`. -/
def IsMaximalTorus (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I) ∧
    ∀ J : HopfIdeal k H,
      torusCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J) →
      J ≤ I → I ≤ J

/-- The Hopf-ideal criterion for a maximal torus: the quotient is a torus and no strictly larger
torus closed subgroup contains it. -/
@[simp]
theorem isMaximalTorus_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    IsMaximalTorus k H I ↔
      torusCommHopfAlgProperty k
          (FiniteTypeCommHopfAlgCat.quotient
            ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I) ∧
        ∀ J : HopfIdeal k H,
          torusCommHopfAlgProperty k
              (FiniteTypeCommHopfAlgCat.quotient
                ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J) →
            J ≤ I → I ≤ J :=
  Iff.rfl

/-- A maximal torus is a torus. -/
theorem IsMaximalTorus.torus {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {I : HopfIdeal k H}
    (hI : IsMaximalTorus k H I) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ I) :=
  hI.1

/-- A torus containing a maximal torus contains no additional closed subgroup directions. -/
theorem IsMaximalTorus.le_of_torus_of_le {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {I J : HopfIdeal k H}
    (hI : IsMaximalTorus k H I)
    (hJ : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J))
    (hJI : J ≤ I) : I ≤ J :=
  hI.2 J hJ hJI

/-- Any torus containing a maximal torus has the same defining Hopf ideal. -/
theorem IsMaximalTorus.eq_of_torus_of_le {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {I J : HopfIdeal k H}
    (hI : IsMaximalTorus k H I)
    (hJ : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩ J))
    (hJI : J ≤ I) : J = I :=
  le_antisymm hJI (hI.le_of_torus_of_le hJ hJI)

end HopfIdeal

end TauCeti
