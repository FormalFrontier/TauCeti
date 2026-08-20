/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Unipotence of the dynamic unipotent subgroup

For a cocharacter `l : 𝔾ₘ → G`, the dynamic subgroup `U(l)` consists of the points whose
conjugates by `l(t)` extend to `t = 0` with limit one. This file proves that these points are
unipotent in the representation-theoretic sense: they act unipotently in every finite-dimensional
comodule.

The proof applies a representation to the extending polynomial family. Over the Laurent
polynomials the family is conjugate to the original action, so its characteristic polynomial is
constant. At the origin the family is the identity, hence that constant is `(X - 1) ^ n`.

## Main declaration

* `TauCeti.Cocharacter.isUnipotentPoint_of_mem_unipotent`: every point of the dynamic unipotent
  subgroup is a unipotent point.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.

This completes the pointwise unipotence assertion implicit in the dynamic route to parabolic and
Levi subgroups in Layer 7 of the ReductiveGroups roadmap, using the representation-theoretic
definition from Layer 5.
-/

public section

open Module Polynomial WithConv
open scoped TensorProduct

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

variable {R : Type u} {H : Type v} {A : Type w}
variable [Field R] [Semiring H] [_root_.HopfAlgebra R H]
variable [Field A] [Algebra R A]

private theorem charpoly_conjugate {B : Type w} [CommRing B] [Algebra R B]
    (M : FGComoduleCat.{u, v, u} R H) (x y : WithConv (H →ₐ[R] B)) :
    (Comodule.endOfPoint M (x * y * x⁻¹).ofConv).charpoly =
      (Comodule.endOfPoint M y.ofConv).charpoly := by
  have hEnd : Comodule.endOfPoint M (x * y * x⁻¹).ofConv =
      (Comodule.pointsAction M x).conj (Comodule.endOfPoint M y.ofConv) := by
    rw [← Comodule.pointsAction_toLinearMap M]
    ext z
    simp [LinearEquiv.conj_apply, Comodule.pointsAction_toLinearMap]
  rw [hEnd, LinearEquiv.charpoly_conj]

/-- Every point of the dynamic unipotent subgroup attached to a cocharacter is unipotent in
every finite-dimensional representation. -/
theorem isUnipotentPoint_of_mem_unipotent
    (l : H →ₐc[R] LaurentPolynomial R) {g : WithConv (H →ₐ[R] A)}
    (hg : g ∈ unipotent A l) : HopfAlgebra.IsUnipotentPoint g := by
  rw [HopfAlgebra.isUnipotentPoint_def]
  intro M
  obtain ⟨hgP, hlimit⟩ := mem_unipotent_iff.mp hg
  let E := extend A l ⟨g, hgP⟩
  let b := Module.Free.chooseBasis R M
  let C := Comodule.coefficientMatrix (C := H) b
  let P : Matrix (Module.Free.ChooseBasisIndex R M) (Module.Free.ChooseBasisIndex R M)
      (Polynomial A) := C.map E.ofConv
  let G : Matrix (Module.Free.ChooseBasisIndex R M) (Module.Free.ChooseBasisIndex R M) A :=
    C.map g.ofConv
  have hzeroPoint : evalZeroPoint A E = 1 := by
    simpa only [E, limit_apply] using hlimit
  have hzeroMatrix : P.map (Polynomial.evalRingHom (0 : A)) = 1 := by
    calc
      P.map (Polynomial.evalRingHom (0 : A)) =
          C.map (evalZeroPoint A E).ofConv := by
        ext i j
        simp [P, C, evalZeroPoint_apply, Matrix.map_apply]
      _ = C.map (1 : WithConv (H →ₐ[R] A)).ofConv := by rw [hzeroPoint]
      _ = 1 := by
        rw [← Comodule.toMatrix_endOfPoint b]
        simp
  have hLaurentMatrix :
      P.map Polynomial.toLaurent =
        C.map (conjugate A l g).ofConv := by
    calc
      P.map Polynomial.toLaurent = C.map (ofPolyPoint A E).ofConv := by
        ext i j
        simp [P, C, ofPolyPoint_apply, Matrix.map_apply]
      _ = C.map (conjugate A l g).ofConv := by rw [ofPolyPoint_extend]
  have hLaurentCharpoly :
      (P.map Polynomial.toLaurent).charpoly =
        (G.map LaurentPolynomial.C).charpoly := by
    rw [hLaurentMatrix]
    rw [← Comodule.toMatrix_endOfPoint b]
    rw [LinearMap.charpoly_toMatrix]
    rw [conjugate_apply, charpoly_conjugate]
    rw [constPoint_apply]
    rw [← LinearMap.charpoly_toMatrix
      (Comodule.endOfPoint M
        (toConv ((IsScalarTower.toAlgHom R A (LaurentPolynomial A)).comp g.ofConv)).ofConv)
      (b.baseChange (LaurentPolynomial A))]
    simp only [Comodule.toMatrix_endOfPoint, G, C, Matrix.map_map]
    congr 2
  have hpolyCharpoly : P.charpoly = G.charpoly.map Polynomial.C := by
    apply Polynomial.map_injective _ Polynomial.toLaurent_injective
    calc
      P.charpoly.map Polynomial.toLaurent =
          G.charpoly.map LaurentPolynomial.C := by
        simpa only [Matrix.charpoly_map] using hLaurentCharpoly
      _ = (G.charpoly.map Polynomial.C).map Polynomial.toLaurent := by
        ext n
        simp
  have hGCharpoly : G.charpoly =
      (1 : Matrix (Module.Free.ChooseBasisIndex R M)
        (Module.Free.ChooseBasisIndex R M) A).charpoly := by
    have hzeroCharpoly := congrArg Matrix.charpoly hzeroMatrix
    rw [Matrix.charpoly_map, hpolyCharpoly, Polynomial.map_map] at hzeroCharpoly
    calc
      G.charpoly = G.charpoly.map
          ((Polynomial.evalRingHom (0 : A)).comp Polynomial.C) := by
        ext n
        simp
      _ = (1 : Matrix (Module.Free.ChooseBasisIndex R M)
          (Module.Free.ChooseBasisIndex R M) A).charpoly := hzeroCharpoly
  apply (LinearMap.GeneralLinearGroup.isUnipotent_iff_charpoly_eq _).2
  have hcoe :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
          LinearMap.GeneralLinearGroup A (A ⊗[R] M)) : Module.End A (A ⊗[R] M)) =
        Comodule.endOfPoint M g.ofConv := by
    exact Comodule.pointsAction_toLinearMap M g
  rw [hcoe, ← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M g.ofConv) (b.baseChange A),
    Comodule.toMatrix_endOfPoint, hGCharpoly, Matrix.charpoly_one,
    ← Module.finrank_eq_card_basis (b.baseChange A)]

end

end TauCeti.Cocharacter
