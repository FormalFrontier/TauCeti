/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalPath
import Mathlib.RingTheory.FiniteStability
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Geometric connectedness of the special linear group

The coordinate Hopf algebra of `SLₙ` is geometrically connected over every field. The proof
uses idempotents and algebraically closed points, so it does not depend on an irreducibility
theorem for the generic determinant polynomial.

Over an algebraically closed extension, a finite-type coordinate algebra has no nontrivial
idempotent once every idempotent has the same value at all rational points. Right translation
reduces that constancy to generators of the ordinary special linear group. Mathlib's
`Matrix.SpecialLinearGroup.diagonal_transvection_induction'` gives elementary transvections and
two-coordinate diagonal matrices as generators. Their one-parameter families are defined over
`K[X]` and `K[T,T⁻¹]`; these rings are domains, so an idempotent function on either family is
constant. The argument includes ranks zero and one, where the special linear group is trivial.

## Main declaration

* `TauCeti.SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  `SLₙ` is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.a and 21.a.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance : IsScalarTower k K (Polynomial K) :=
  IsScalarTower.of_algebraMap_eq (by simp)

local instance : IsScalarTower k K (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq (by simp)

/-- Base-changed special-linear points identified with determinant-one matrices. -/
private def baseChangeSpecialLinearPointsMulEquiv
    (n : ℕ) (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] :
    WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] A) ≃*
      Matrix.SpecialLinearGroup (Fin n) A :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
    (A := coordinateHopfAlgebra k n) (R := A)).symm.trans
      (pointsMulEquiv (R := k) (A := A) n)

private theorem baseChangeSpecialLinearPointsMulEquiv_mapValue
    (n : ℕ) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (f : WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] A))
    (phi : A →ₐ[K] B) :
    baseChangeSpecialLinearPointsMulEquiv n B
        (AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n) phi f) =
      Matrix.SpecialLinearGroup.map phi.toRingHom
        (baseChangeSpecialLinearPointsMulEquiv n A f) := by
  rw [baseChangeSpecialLinearPointsMulEquiv, MulEquiv.trans_apply,
    AlgHom.baseChangePointsMulEquiv_symm_mapValue,
    baseChangeSpecialLinearPointsMulEquiv, MulEquiv.trans_apply]
  exact pointsMulEquiv_mapValue (R := k) (A := A) (B := B) n
    (phi.restrictScalars k) _

private theorem rightTranslationAlgHom_eq_self_of_transvection
    (n : ℕ) (e : K ⊗[k] coordinateHopfAlgebra k n)
    [IsAlgClosed K] (he : IsIdempotentElem e) {i j : Fin n} (hij : i ≠ j) (a : K) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.transvection hij a)) e = e := by
  let xX : WithConv
      (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] Polynomial K) :=
    (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n (Polynomial K)).symm
      (Matrix.SpecialLinearGroup.transvection hij Polynomial.X)
  let eval (c : K) : Polynomial K →ₐ[K] K :=
    Polynomial.aevalTower (AlgHom.id K K) c
  have hx (c : K) :
      AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n) (eval c) xX =
        (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.transvection hij c) := by
    apply (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).injective
    rw [baseChangeSpecialLinearPointsMulEquiv_mapValue (k := k) (K := K)]
    simp [xX, eval]
  let ga := (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
    (Matrix.SpecialLinearGroup.transvection hij a)
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he ga xX (eval a) (eval 0)
  · simpa [ga] using hx a
  · simpa using hx 0

/-- The generic two-coordinate diagonal point over the Laurent-polynomial ring. -/
private noncomputable def diag2nLaurentPath
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    WithConv
      (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] LaurentPolynomial K) :=
  (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n
    (LaurentPolynomial K)).symm
      (Matrix.SpecialLinearGroup.diag2nUnit hij (MultiplicativeGroup.genericUnit K))

private theorem mapValue_diag2nLaurentPath
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) (b : Kˣ) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
        (MultiplicativeGroup.point b) (diag2nLaurentPath (k := k) n hij) =
      (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
        (Matrix.SpecialLinearGroup.diag2n hij b (Units.ne_zero b)) := by
  apply (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).injective
  rw [baseChangeSpecialLinearPointsMulEquiv_mapValue (k := k) (K := K)]
  dsimp only [diag2nLaurentPath]
  simp only [MulEquiv.apply_symm_apply]
  exact map_diag2nUnit_genericUnit hij b

private theorem mapValue_diag2nLaurentPath_one
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
        (MultiplicativeGroup.point (1 : Kˣ))
        (diag2nLaurentPath (k := k) n hij) = 1 := by
  have hdiag : Matrix.SpecialLinearGroup.diag2n hij
      (1 : K) (Units.ne_zero (1 : Kˣ)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.diag2nUnit_mk0]
    simp
  calc
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
        (MultiplicativeGroup.point (1 : Kˣ))
        (diag2nLaurentPath (k := k) n hij) =
      (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
        (Matrix.SpecialLinearGroup.diag2n hij
          (1 : K) (Units.ne_zero (1 : Kˣ))) :=
      mapValue_diag2nLaurentPath (k := k) (K := K) n hij 1
    _ = (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm 1 :=
      congrArg _ hdiag
    _ = 1 := map_one _

private theorem rightTranslationAlgHom_eq_self_of_diag2n
    (n : ℕ) (e : K ⊗[k] coordinateHopfAlgebra k n)
    [IsAlgClosed K] (he : IsIdempotentElem e) {i j : Fin n}
    (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.diag2n hij a ha)) e = e := by
  let xT := diag2nLaurentPath (k := k) (K := K) n hij
  let eval (b : Kˣ) : LaurentPolynomial K →ₐ[K] K :=
    MultiplicativeGroup.point b
  have hx (b : Kˣ) := mapValue_diag2nLaurentPath (k := k) (K := K) n hij b
  let au : Kˣ := Units.mk0 a ha
  let ga := (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
    (Matrix.SpecialLinearGroup.diag2n hij a ha)
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he ga xT (eval au) (eval 1)
  · simpa only [ga, au, Units.val_mk0] using hx au
  · simpa only [xT, eval] using
      mapValue_diag2nLaurentPath_one (k := k) (K := K) n hij

private theorem rightTranslationAlgHom_eq_self
    (n : ℕ) [IsAlgClosed K] (e : K ⊗[k] coordinateHopfAlgebra k n)
    (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  let E := baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K
  by_cases h : Nontrivial (Fin n)
  · let _ := h
    let P : Matrix.SpecialLinearGroup (Fin n) K → Prop := fun M ↦
      HopfAlgebra.rightTranslationAlgHom (E.symm M) e = e
    have hp : P (E g) := by
      apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P (E g)
      · intro i j hij a ha
        exact rightTranslationAlgHom_eq_self_of_diag2n n e he hij a ha
      · intro i j hij a
        exact rightTranslationAlgHom_eq_self_of_transvection n e he hij a
      · intro A B hA hB
        calc
          HopfAlgebra.rightTranslationAlgHom (E.symm (A * B)) e =
              HopfAlgebra.rightTranslationAlgHom (E.symm A * E.symm B) e := by
            rw [map_mul]
          _ = HopfAlgebra.rightTranslationAlgHom (E.symm A)
              (HopfAlgebra.rightTranslationAlgHom (E.symm B) e) :=
            DFunLike.congr_fun (HopfAlgebra.rightTranslationAlgHom_mul _ _) e
          _ = e := by rw [hB, hA]
    simpa [P] using hp
  · let _ : Subsingleton (Fin n) := not_nontrivial_iff_subsingleton.mp h
    have hmatrix : E g = 1 := Subsingleton.elim _ _
    have hg : g = 1 := E.injective (by simpa using hmatrix)
    rw [hg, HopfAlgebra.rightTranslationAlgHom_one, AlgHom.id_apply]

/-- The coordinate Hopf algebra of `SLₙ` is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let H := coordinateHopfAlgebra k n
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) k
  let _ : Nontrivial (K ⊗[k] H) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K H
      (RingHom.injective (algebraMap k H))
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) :=
    HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      (fun e he g ↦ rightTranslationAlgHom_eq_self n e he g)
  let e : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr hconnected

end

end TauCeti.SpecialLinear
