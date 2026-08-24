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
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalPath
import TauCeti.RingTheory.FiniteType.PointSeparation
import Mathlib.Algebra.GroupWithZero.Idempotent
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

private noncomputable instance instFiniteTypeCoordinateHopfAlgebra (n : ℕ) :
    Algebra.FiniteType k (coordinateHopfAlgebra k n) := by
  exact Algebra.FiniteType.quotient k (definingHopfIdeal k n).toIdeal

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

private theorem point_comp_rightTranslationAlgHom
    {H : Type u} [CommRing H] [_root_.HopfAlgebra K H]
    (f g : WithConv (H →ₐ[K] K)) :
    toConv (f.ofConv.comp (HopfAlgebra.rightTranslationAlgHom g)) = f * g := by
  apply WithConv.ofConv_injective
  ext x
  change f.ofConv (HopfAlgebra.rightTranslationAlgHom g x) = (f * g).ofConv x
  rw [HopfAlgebra.rightTranslationAlgHom_apply, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := K) x using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp [hy, hz]
  | tmul y z => simp [Algebra.smul_def, mul_comm]

private theorem mapValue_apply_eq_of_isIdempotentElem
    {H A : Type u} [CommRing H] [_root_.HopfAlgebra K H]
    [CommRing A] [Algebra K A] [IsDomain A]
    (e : H) (he : IsIdempotentElem e) (q : WithConv (H →ₐ[K] A))
    (phi psi : A →ₐ[K] K) :
    (AlgHom.mapValue (H := H) phi q).ofConv e =
      (AlgHom.mapValue (H := H) psi q).ofConv e := by
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map q.ofConv) with h | h <;>
    simp [AlgHom.mapValue_apply, h]

private theorem rightTranslationAlgHom_eq_self_of_transvection
    (n : ℕ) (e : K ⊗[k] coordinateHopfAlgebra k n)
    [IsAlgClosed K] (he : IsIdempotentElem e) {i j : Fin n} (hij : i ≠ j) (a : K) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.transvection hij a)) e = e := by
  apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
    (k := K) (A := K ⊗[k] coordinateHopfAlgebra k n) (K := K) (he.map _) he
  intro f
  let _ : Algebra k (Polynomial K) := Algebra.compHom (Polynomial K) (algebraMap k K)
  let _ : IsScalarTower k K (Polynomial K) := IsScalarTower.of_algebraMap_eq' rfl
  let fX : WithConv
      (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] Polynomial K) :=
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
      (IsScalarTower.toAlgHom K K (Polynomial K)) (toConv f)
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
  have hf (c : K) :
      AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n) (eval c) fX = toConv f := by
    apply WithConv.ofConv_injective
    ext z
    simp [fX, eval, AlgHom.mapValue_apply]
  have hpath := mapValue_apply_eq_of_isIdempotentElem
    (K := K) e he (fX * xX) (eval a) (eval 0)
  rw [map_mul, hf a, hx a] at hpath
  rw [map_mul, hf 0, hx 0] at hpath
  rw [Matrix.SpecialLinearGroup.transvection_coeff_zero] at hpath
  let ga := (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
    (Matrix.SpecialLinearGroup.transvection hij a)
  calc
    f (HopfAlgebra.rightTranslationAlgHom ga e) = (toConv f * ga).ofConv e :=
      congrArg (fun q : WithConv
        (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K) ↦ q.ofConv e)
        (point_comp_rightTranslationAlgHom (toConv f) ga)
    _ = f e := by simpa [ga] using hpath

/-- The generic two-coordinate diagonal point over the Laurent-polynomial ring. -/
private noncomputable def diag2nLaurentPath
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    WithConv
      (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] LaurentPolynomial K) := by
  let _ : Algebra k (LaurentPolynomial K) :=
    Algebra.compHom (LaurentPolynomial K) (algebraMap k K)
  let _ : IsScalarTower k K (LaurentPolynomial K) := IsScalarTower.of_algebraMap_eq' rfl
  exact (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n
    (LaurentPolynomial K)).symm
      (diag2nUnit hij (laurentVariableUnit (K := K)))

private theorem mapValue_diag2nLaurentPath
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) (b : Kˣ) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
        (MultiplicativeGroup.point b) (diag2nLaurentPath (k := k) n hij) =
      (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
        (Matrix.SpecialLinearGroup.diag2n hij b (Units.ne_zero b)) := by
  let _ : Algebra k (LaurentPolynomial K) :=
    Algebra.compHom (LaurentPolynomial K) (algebraMap k K)
  let _ : IsScalarTower k K (LaurentPolynomial K) := IsScalarTower.of_algebraMap_eq' rfl
  apply (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).injective
  rw [baseChangeSpecialLinearPointsMulEquiv_mapValue (k := k) (K := K)]
  dsimp only [diag2nLaurentPath]
  simp only [MulEquiv.apply_symm_apply]
  exact map_diag2nUnit_laurent hij b

/-- A rational point extended to a constant Laurent-polynomial-valued point. -/
private noncomputable def constantLaurentPath
    (n : ℕ) (f : K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K) :
    WithConv
      (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] LaurentPolynomial K) :=
  AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
    (IsScalarTower.toAlgHom K K (LaurentPolynomial K)) (toConv f)

private theorem mapValue_constantLaurentPath
    (n : ℕ) (f : K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K) (b : Kˣ) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n)
        (MultiplicativeGroup.point b) (constantLaurentPath n f) = toConv f := by
  apply WithConv.ofConv_injective
  ext z
  simp [constantLaurentPath, AlgHom.mapValue_apply]

private theorem algHom_apply_rightTranslationAlgHom_diag2n
    (n : ℕ) (e : K ⊗[k] coordinateHopfAlgebra k n)
    (he : IsIdempotentElem e) {i j : Fin n}
    (hij : i ≠ j) (a : K) (ha : a ≠ 0)
    (f : K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K) :
    f (HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.diag2n hij a ha)) e) = f e := by
  let _ : Algebra k (LaurentPolynomial K) :=
    Algebra.compHom (LaurentPolynomial K) (algebraMap k K)
  let _ : IsScalarTower k K (LaurentPolynomial K) := IsScalarTower.of_algebraMap_eq' rfl
  let fT := constantLaurentPath n f
  let xT := diag2nLaurentPath (k := k) (K := K) n hij
  let eval (b : Kˣ) : LaurentPolynomial K →ₐ[K] K :=
    MultiplicativeGroup.point b
  have hx (b : Kˣ) := mapValue_diag2nLaurentPath (k := k) (K := K) n hij b
  have hf (b : Kˣ) := mapValue_constantLaurentPath (k := k) n f b
  let au : Kˣ := Units.mk0 a ha
  have hpath := mapValue_apply_eq_of_isIdempotentElem
    (K := K) e he (fT * xT) (eval au) (eval 1)
  rw [map_mul, hf au, hx au] at hpath
  rw [map_mul, hf 1, hx 1] at hpath
  have hdiagone : Matrix.SpecialLinearGroup.diag2n hij
      ((1 : Kˣ) : K) (Units.ne_zero (1 : Kˣ)) = 1 := by
    ext r s
    simp [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply,
      Matrix.one_apply]
  have hEone :
      (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm 1 = 1 :=
    map_one _
  rw [hdiagone, hEone] at hpath
  have hdiagau : Matrix.SpecialLinearGroup.diag2n hij
      ((au : Kˣ) : K) (Units.ne_zero au) =
        Matrix.SpecialLinearGroup.diag2n hij a ha := by
    rfl
  let ga := (baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
    (Matrix.SpecialLinearGroup.diag2n hij a ha)
  calc
    f (HopfAlgebra.rightTranslationAlgHom ga e) = (toConv f * ga).ofConv e :=
      congrArg (fun q : WithConv
        (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K) ↦ q.ofConv e)
        (point_comp_rightTranslationAlgHom (toConv f) ga)
    _ = f e := by simpa [ga, hdiagau] using hpath

private theorem rightTranslationAlgHom_eq_self_of_diag2n
    (n : ℕ) (e : K ⊗[k] coordinateHopfAlgebra k n)
    [IsAlgClosed K] (he : IsIdempotentElem e) {i j : Fin n}
    (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSpecialLinearPointsMulEquiv (k := k) (K := K) n K).symm
          (Matrix.SpecialLinearGroup.diag2n hij a ha)) e = e := by
  apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
    (k := K) (A := K ⊗[k] coordinateHopfAlgebra k n) (K := K) (he.map _) he
  intro f
  exact algHom_apply_rightTranslationAlgHom_diag2n n e he hij a ha f

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
        have hequiv (q : WithConv
            (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K)) :
            HopfAlgebra.rightTranslationAlgEquiv q e =
              HopfAlgebra.rightTranslationAlgHom q e :=
          DFunLike.congr_fun (HopfAlgebra.rightTranslationAlgEquiv_toAlgHom q) e
        calc
          HopfAlgebra.rightTranslationAlgHom (E.symm (A * B)) e =
              HopfAlgebra.rightTranslationAlgEquiv (E.symm (A * B)) e :=
            (hequiv _).symm
          _ = HopfAlgebra.rightTranslationAlgEquiv (E.symm A)
              (HopfAlgebra.rightTranslationAlgEquiv (E.symm B) e) := by
            rw [map_mul, HopfAlgebra.rightTranslationAlgEquiv_mul,
              AlgEquiv.mul_apply]
          _ = HopfAlgebra.rightTranslationAlgEquiv (E.symm A) e := by
            rw [hequiv, hB]
          _ = e := by rw [hequiv, hA]
    simpa [P] using hp
  · let _ : Subsingleton (Fin n) := not_nontrivial_iff_subsingleton.mp h
    have hmatrix : E g = 1 := Subsingleton.elim _ _
    have hg : g = 1 := E.injective (by simpa using hmatrix)
    rw [hg]
    calc
      HopfAlgebra.rightTranslationAlgHom 1 e =
          HopfAlgebra.rightTranslationAlgEquiv 1 e :=
        (DFunLike.congr_fun
          (HopfAlgebra.rightTranslationAlgEquiv_toAlgHom
            (1 : WithConv
              (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K))) e).symm
      _ = e := by rw [HopfAlgebra.rightTranslationAlgEquiv_one]; rfl

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
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) := by
    apply connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr
    intro e he
    have heval (g : WithConv (K ⊗[k] H →ₐ[K] K)) :
        g.ofConv e = Coalgebra.counit (R := K) e := by
      have htranslate := rightTranslationAlgHom_eq_self n e he g
      have h := DFunLike.congr_fun
        (HopfAlgebra.counitAlgHom_comp_rightTranslationAlgHom g) e
      rw [AlgHom.comp_apply, htranslate] at h
      exact h.symm
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp
      (he.map (_root_.Bialgebra.counitAlgHom K (K ⊗[k] H))) with hzero | hone
    · left
      change Coalgebra.counit (R := K) e = 0 at hzero
      apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
        (k := K) (A := K ⊗[k] H) (K := K) he IsIdempotentElem.zero
      intro f
      simpa using (heval (toConv f)).trans hzero
    · right
      change Coalgebra.counit (R := K) e = 1 at hone
      apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
        (k := K) (A := K ⊗[k] H) (K := K) he IsIdempotentElem.one
      intro f
      simpa using (heval (toConv f)).trans hone
  let e : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr hconnected

end

end TauCeti.SpecialLinear
