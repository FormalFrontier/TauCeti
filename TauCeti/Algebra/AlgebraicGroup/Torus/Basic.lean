/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# Tori over a field

A finite-type affine group over a field is a torus when it becomes a finite-rank split torus
after extending scalars to an algebraic closure. On coordinate Hopf algebras, the rank-`n` split
torus has coordinate ring

```text
k[Multiplicative (Fin n →₀ ℤ)].
```

This file records both the split and geometric forms of that definition as object properties on
finite-type commutative Hopf algebras. Keeping them as properties, rather than building them into
the ambient category, leaves finite, non-smooth groups such as `μ_p` in the general theory.

Every split torus is a torus: after base change, the standard coordinate-ring comparison
identifies `K ⊗[k] k[ℤⁿ]` with `K[ℤⁿ]`. Every torus is of multiplicative type, since its
base change is a diagonalizable coordinate Hopf algebra. Thus this definition extends the
existing multiplicative-type theory while imposing the free finite-rank character lattice that
distinguishes tori from general groups of multiplicative type.

## Main declarations

* `TauCeti.splitTorusCommHopfAlgProperty`: finite-type coordinate Hopf algebras isomorphic over
  the base ring to the coordinate ring of a finite-rank split torus.
* `TauCeti.torusCommHopfAlgProperty`: finite-type coordinate Hopf algebras that become a
  finite-rank split torus over `AlgebraicClosure k`.
* `TauCeti.splitTorusCommHopfAlgProperty.torus`: every split torus is a torus.
* `TauCeti.torusCommHopfAlgProperty.multiplicativeType`: every torus is of multiplicative type.
* `TauCeti.torusCommHopfAlgProperty.isCocomm`: the coordinate Hopf algebra of a torus is
  cocommutative.
* `TauCeti.SplitTorus.splitTorus_coordinateRing`: the standard finite-rank split tori satisfy the
  split predicate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This is the coordinate-algebra definition required by Layer 4, "Tori: split and non-split", of
the ReductiveGroups roadmap. Smoothness and geometric connectedness are proved in
`TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected`; the next step is the character lattice
with its Galois action.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti

universe u

/-- The object property selecting finite-type commutative Hopf algebras that are coordinate
rings of split tori of finite rank.

The witness `n` is the rank. The finite index type is universe-lifted so that its character group
lives in the same universe as `k`; this does not change the represented rank-`n` torus. -/
def splitTorusCommHopfAlgProperty (k : Type u) [CommRing k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ ∃ n : ℕ, Nonempty
    (DiagonalizableGroup.coordinateRing k
        (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅ H)

/-- Membership in the split-torus property means being isomorphic to the coordinate Hopf algebra
of a finite-rank split torus. -/
@[simp]
theorem splitTorusCommHopfAlgProperty_iff
    (k : Type u) [CommRing k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    splitTorusCommHopfAlgProperty k H ↔
      ∃ n : ℕ, Nonempty
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅ H) :=
  Iff.rfl

/-- Being a split torus is invariant under isomorphisms of finite-type commutative Hopf
algebras. -/
instance (k : Type u) [CommRing k] :
    (splitTorusCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨n, ⟨i⟩⟩
    exact ⟨n, ⟨i ≪≫ e⟩⟩

/-- The category of finite-type split-torus coordinate Hopf algebras over a commutative ring. -/
abbrev SplitTorusCommHopfAlgCat (k : Type u) [CommRing k] :=
  (splitTorusCommHopfAlgProperty k).FullSubcategory

/-- The object property selecting finite-type commutative Hopf algebras that become coordinate
rings of split tori of finite rank after base change to an algebraic closure.

This is the coordinate-Hopf-algebra definition of a not-necessarily-split torus over `k`. -/
def torusCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  (splitTorusCommHopfAlgProperty (AlgebraicClosure k)).inverseImage
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k))

/-- Membership in the torus property means becoming a finite-rank split torus after base change
to an algebraic closure. -/
@[simp]
theorem torusCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k H ↔
      ∃ n : ℕ, Nonempty
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
            (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅
          FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

/-- Being a torus is invariant under isomorphisms of finite-type commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (torusCommHopfAlgProperty k).IsClosedUnderIsomorphisms := by
  unfold torusCommHopfAlgProperty
  infer_instance

namespace Coalgebra.IsCocomm

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [_root_.Bialgebra R A] [_root_.Bialgebra R B]

/-- Cocommutativity transfers across a bialgebra equivalence. -/
theorem of_bialgEquiv (e : A ≃ₐc[R] B) [hA : _root_.Coalgebra.IsCocomm R A] :
    _root_.Coalgebra.IsCocomm R B := by
  constructor
  ext b
  apply (TensorProduct.map_bijective e.symm.bijective e.symm.bijective).injective
  simp only [LinearMap.comp_apply]
  -- Applying the tensor map to the composite with `TensorProduct.comm` unfolds to this
  -- expression. There is no propositional compatibility lemma for that coercion-level step;
  -- the subsequent `TensorProduct.map_comm` is the structural identity used by the proof.
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

private theorem baseChangeTensorBialgEquiv_includeRight (y : H ⊗[k] H) :
    Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
        (Algebra.TensorProduct.includeRight y) =
      TensorProduct.AlgebraTensorModule.distribBaseChange k K H H
        (Algebra.TensorProduct.includeRight y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [Algebra.TensorProduct.includeRight_apply,
        Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

private theorem baseChangeTensorBialgEquiv_includeRight_comm (y : H ⊗[k] H) :
    Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
        (Algebra.TensorProduct.includeRight (TensorProduct.comm k H H y)) =
      TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
        (Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
          (Algebra.TensorProduct.includeRight y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, LinearMap.map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      simp only [TensorProduct.comm_tmul, Algebra.TensorProduct.includeRight_apply,
        Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul]

/-- Cocommutativity descends from a field extension. -/
theorem of_baseChange [h : _root_.Coalgebra.IsCocomm K (K ⊗[k] H)] :
    _root_.Coalgebra.IsCocomm k H := by
  constructor
  ext x
  apply Algebra.TensorProduct.includeRight_injective (B := H ⊗[k] H)
    (algebraMap k K).injective
  let e := Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
  apply e.injective
  have he_comul :
      e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x)) =
        Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x) := by
    rw [baseChangeTensorBialgEquiv_includeRight]
    simp only [Algebra.TensorProduct.includeRight_apply]
    rw [TauCeti.Coalgebra.baseChange_comul_tmul]
  calc
    e (Algebra.TensorProduct.includeRight
        (TensorProduct.comm k H H (Coalgebra.comul (R := k) x))) =
        TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
          (e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x))) :=
      baseChangeTensorBialgEquiv_includeRight_comm (Coalgebra.comul (R := k) x)
    _ = TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
        (Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x)) :=
      congrArg (TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)) he_comul
    _ = Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x) :=
      Coalgebra.comm_comul K (Algebra.TensorProduct.includeRight x)
    _ = e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x)) := he_comul.symm

end Coalgebra.IsCocomm

/-- The coordinate Hopf algebra of a torus is cocommutative. -/
@[grind →]
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
          (_root_.CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i) (hA := hsplit)
  exact Coalgebra.IsCocomm.of_baseChange (h := hbase)

/-- The category of finite-type torus coordinate Hopf algebras over a field.

Objects need not be split over the base field; they become split after extension to an algebraic
closure. -/
abbrev TorusCommHopfAlgCat (k : Type u) [Field k] : Type _ :=
  (torusCommHopfAlgProperty k).FullSubcategory

/-- Every split torus is a torus. -/
@[grind →]
theorem splitTorusCommHopfAlgProperty.torus
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : splitTorusCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty k H := by
  rw [splitTorusCommHopfAlgProperty_iff] at hH
  rw [torusCommHopfAlgProperty_iff]
  obtain ⟨n, ⟨i⟩⟩ := hH
  exact ⟨n, ⟨
    (DiagonalizableGroup.baseChangeCoordinateRingIso k (AlgebraicClosure k)
      (SplitTorus.characterGroup (ULift.{u} (Fin n)))).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).mapIso i⟩⟩

/-- Every torus is a group of multiplicative type. -/
@[grind →]
theorem torusCommHopfAlgProperty.multiplicativeType
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    multiplicativeTypeCommHopfAlgProperty k H := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing]
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, hn⟩ := hH
  exact ⟨SplitTorus.characterGroup (ULift.{u} (Fin n)), hn⟩

namespace SplitTorus

/-- The coordinate Hopf algebra of a finite-rank split torus satisfies the split-torus property. -/
@[grind =>]
theorem splitTorus_coordinateRing (k : Type u) [CommRing k] (σ : Type u) [Finite σ] :
    splitTorusCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let eσ : σ ≃ ULift.{u} (Fin (Nat.card σ)) :=
    (Finite.equivFin σ).trans Equiv.ulift.symm
  let e : Multiplicative (σ →₀ ℤ) ≃*
      Multiplicative (ULift.{u} (Fin (Nat.card σ)) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr eσ)
  let i : DiagonalizableGroup.coordinateRing k (characterGroup σ) ≅
      DiagonalizableGroup.coordinateRing k
        (characterGroup (ULift.{u} (Fin (Nat.card σ)))) :=
    ObjectProperty.isoMk _ <|
      _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k e)
  exact ⟨Nat.card σ, ⟨i.symm⟩⟩

end SplitTorus

end TauCeti
