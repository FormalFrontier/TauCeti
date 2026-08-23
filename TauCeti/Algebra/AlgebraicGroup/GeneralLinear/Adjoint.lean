/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The tangent matrix of a counit-valued derivation of `O(GLₙ)` is the object being conjugated.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
-- `Derivation.adDerivation` is the convolution conjugation being computed.
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
-- Points valued in the counit algebra, where the conjugating point lives, are the `B`-points.
public import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints
-- The diagonal torus supplies the points whose adjoint action is diagonalized.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus
-- Non-public: the diagonal-matrix-unit product law is used only in a proof below.
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The adjoint representation of the general linear group is matrix conjugation

The tangent space at the identity of `GLₙ` is the full matrix algebra
(`TauCeti.GeneralLinear.tangentLinearEquivMatrix`), and a point of `GLₙ` acts on it by the
convolution conjugation `Ad g d = g ⋆ d ⋆ g⁻¹` (`Derivation.adDerivation`). This file computes
that action: it is conjugation of the tangent matrix by the invertible matrix of the point,

```text
Ad(g) X = g X g⁻¹.
```

The proof is the two-fold comultiplication of a generic matrix entry. Evaluating the convolution
product `g ⋆ d ⋆ g⁻¹` on `Xᵢⱼ` runs over `comul Xᵢⱼ = ∑ₖ Xᵢₖ ⊗ Xₖⱼ` twice, so the `(i, j)` entry
of the conjugated tangent matrix is the double sum `∑ₖ ∑ₗ gᵢₗ dₗₖ (g⁻¹)ₖⱼ`, which is the
`(i, j)` entry of the matrix product.

Specializing to the diagonal torus computes the expected eigenvalues of the adjoint
representation: conjugation by `diag(t)` multiplies the `(i, j)` entry by `tᵢ tⱼ⁻¹`. Thus the
matrix units have the eigenvalue formulas needed for a future formal weight decomposition, and
the diagonal matrices — the tangent space of the torus itself — are fixed.

## Main declarations

* `TauCeti.GeneralLinear.counitPointsMulEquiv`: the invertible matrix of a point of `GLₙ` valued
  in the counit algebra of the coordinate ring, where the tangent vectors live.
* `TauCeti.GeneralLinear.tangentMatrix_adDerivation`: **the adjoint action of `GLₙ` on its
  tangent space is conjugation of matrices.**
* `TauCeti.GeneralLinear.tangentMatrix_adDerivation_apply_of_diagGL` and
  `TauCeti.GeneralLinear.tangentMatrix_adDerivation_apply_symm_diagGL`: conjugation by a diagonal
  point scales the `(i, j)` entry by `tᵢ tⱼ⁻¹`.
* `TauCeti.GeneralLinear.tangentMatrix_adDerivation_single`: the corresponding eigenvalue
  computation for a matrix unit `Eᵢⱼ`.
* `TauCeti.GeneralLinear.tangentMatrix_adDerivation_diagonal`: the tangent space of the diagonal
  torus is fixed by the adjoint action of the torus.
* `TauCeti.GeneralLinear.tangentMatrix_adDerivation_apply_diagonalTorusPoints`: the same
  computation for a point of the diagonal torus of `GLₙ`, indexed by its split-torus coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.24 and 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.18.

Layer 2 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the adjoint action
`Ad : G → GL(Lie G)`, and Layer 7 asks for the root datum of a split pair `(G, T)`, read off the
weight decomposition of `Lie G` under `T`. This file supplies the eigenvalue computations needed
for that future decomposition in the worked example `GLₙ` with its diagonal torus, the roadmap's
prescribed check that the definitions are honest.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
variable (n : ℕ)

/-- The invertible matrix of a point of `GLₙ` valued in the counit algebra of `O(GLₙ)`.

Tangent vectors at the identity are derivations valued in that counit algebra, so this is the
form in which a point conjugating a tangent vector presents itself. -/
def counitPointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R]
        Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃*
      Matrix.GeneralLinearGroup (Fin n) B :=
  (Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).trans
    (pointsMulEquiv (R := R) (A := B) n)

variable
  (g : WithConv (coordinateHopfAlgebra R n →ₐ[R]
    Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B))
  (d : Derivation R (coordinateHopfAlgebra R n)
    (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B))

/-- The transported points equivalence is the points equivalence of the transported point. -/
theorem counitPointsMulEquiv_eq_pointsMulEquiv :
    counitPointsMulEquiv n g =
      pointsMulEquiv n (AlgHom.mapValue (H := coordinateHopfAlgebra R n)
        (Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R n) B).toAlgHom g) := by
  rw [← Bialgebra.CounitAlgebra.pointsMulEquiv_eq_mapValue]
  exact MulEquiv.trans_apply _ _ _

/-- The matrix of a counit-algebra-valued point evaluates it on the generic matrix entries. -/
@[simp]
theorem counitPointsMulEquiv_apply (i j : Fin n) :
    counitPointsMulEquiv n g i j =
      Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R n) B
        (g.ofConv (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j))))) := by
  rw [counitPointsMulEquiv_eq_pointsMulEquiv, pointsMulEquiv_apply, pointToGeneralLinear_apply,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

/-- The matrix of the inverse of a counit-algebra-valued point evaluates the inverse point on
the generic matrix entries. -/
@[simp]
theorem counitPointsMulEquiv_inv_apply (i j : Fin n) :
    ((counitPointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) B) i j =
      Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R n) B
        ((g⁻¹).ofConv (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j))))) := by
  rw [← map_inv (counitPointsMulEquiv n) g, counitPointsMulEquiv_apply]

/-- A convolution product of counit-valued linear maps, evaluated on a generic matrix entry, is
the matrix product of their values: the comultiplication of `Xᵢⱼ` is `∑ₖ Xᵢₖ ⊗ Xₖⱼ`. -/
private theorem ofConv_convMul_apply_X
    (f h : WithConv (coordinateHopfAlgebra R n →ₗ[R]
      Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B))
    (i j : Fin n) :
    (f * h).ofConv (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      ∑ k : Fin n,
        f.ofConv (coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (i, k)))) *
          h.ofConv (coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (k, j)))) := by
  simp

/-- **The adjoint action of `GLₙ` on its tangent space is conjugation of matrices.**

The tangent vector `Ad g d = g ⋆ d ⋆ g⁻¹` has tangent matrix `g X g⁻¹`, where `X` is the tangent
matrix of `d` and `g` is read as an invertible matrix through
`TauCeti.GeneralLinear.counitPointsMulEquiv`. -/
@[simp]
theorem tangentMatrix_adDerivation :
    tangentMatrix n (Derivation.adDerivation B g d) =
      (counitPointsMulEquiv n g : Matrix (Fin n) (Fin n) B) * tangentMatrix n d *
        ((counitPointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) B) := by
  ext i j
  rw [tangentMatrix_apply, Derivation.adDerivation_apply, ofConv_convMul_apply_X, map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ofConv_convMul_apply_X, map_sum, Matrix.mul_apply, counitPointsMulEquiv_inv_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, counitPointsMulEquiv_apply, tangentMatrix_apply]
  rfl

/-- The adjoint action of `GLₙ`, entrywise: conjugation by `g` sends the tangent matrix `X` to
`g X g⁻¹`. -/
theorem tangentMatrix_adDerivation_apply (i j : Fin n) :
    tangentMatrix n (Derivation.adDerivation B g d) i j =
      ∑ k : Fin n, ∑ l : Fin n,
        (counitPointsMulEquiv n g : Matrix (Fin n) (Fin n) B) i l * tangentMatrix n d l k *
          ((counitPointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) B) k j := by
  rw [tangentMatrix_adDerivation, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]

variable {n g d}
variable {t : Fin n → Bˣ}

/-- Conjugation by a diagonal point of `GLₙ` scales the `(i, j)` entry of a tangent matrix by
the character `tᵢ tⱼ⁻¹` of the diagonal torus. -/
theorem tangentMatrix_adDerivation_apply_of_diagGL (hg : counitPointsMulEquiv n g = diagGL t)
    (i j : Fin n) :
    tangentMatrix n (Derivation.adDerivation B g d) i j =
      (t i : B) * tangentMatrix n d i j * ((t j)⁻¹ : Bˣ) := by
  rw [tangentMatrix_adDerivation, hg, ← map_inv diagGL t, diagGL_coe, diagGL_coe,
    Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (mul_assoc _ _ _).symm

/-- Conjugation by the diagonal point with coordinates `t`, with no hypothesis to discharge:
every invertible matrix, in particular every diagonal one, is the matrix of a unique point. -/
theorem tangentMatrix_adDerivation_apply_symm_diagGL (i j : Fin n) :
    tangentMatrix n
        (Derivation.adDerivation B
          ((counitPointsMulEquiv (R := R) (B := B) n).symm (diagGL t)) d) i j =
      (t i : B) * tangentMatrix n d i j * ((t j)⁻¹ : Bˣ) :=
  tangentMatrix_adDerivation_apply_of_diagGL
    ((counitPointsMulEquiv (R := R) (B := B) n).apply_symm_apply _) i j

/-- The matrix-unit eigenvalue computation for the adjoint action: conjugation by `diag(t)`
rescales `Eᵢⱼ` by `tᵢ tⱼ⁻¹`. -/
theorem tangentMatrix_adDerivation_single (hg : counitPointsMulEquiv n g = diagGL t)
    {i j : Fin n} {c : B} (hd : tangentMatrix n d = Matrix.single i j c) :
    tangentMatrix n (Derivation.adDerivation B g d) =
      Matrix.single i j ((t i : B) * c * ((t j)⁻¹ : Bˣ)) := by
  rw [tangentMatrix_adDerivation, hg, hd, ← map_inv diagGL t, diagGL_coe, diagGL_coe,
    diagonal_mul_single_mul_diagonal, Pi.inv_apply]

/-- The tangent space of the diagonal torus is fixed by the adjoint action of the torus: a
diagonal tangent matrix is unchanged by conjugation by a diagonal point. This is the fixed-vector
computation needed to identify the zero-weight space in a future formal decomposition. -/
theorem tangentMatrix_adDerivation_diagonal (hg : counitPointsMulEquiv n g = diagGL t)
    {x : Fin n → B} (hd : tangentMatrix n d = Matrix.diagonal x) :
    tangentMatrix n (Derivation.adDerivation B g d) = Matrix.diagonal x := by
  ext a b
  rw [tangentMatrix_adDerivation_apply_of_diagGL hg, hd]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, mul_comm ((t a : B)) (x a), mul_assoc, Units.mul_inv, mul_one]
  · rw [Matrix.diagonal_apply_ne _ hab, mul_zero, zero_mul]

/-- The adjoint action of a point of the diagonal torus of `GLₙ`: it multiplies the `(i, j)`
entry of a tangent matrix by the character `tᵢ tⱼ⁻¹` read off the split-torus coordinates of
the point. -/
theorem tangentMatrix_adDerivation_apply_diagonalTorusPoints
    (s : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[R] B))
    (i j : Fin n) :
    tangentMatrix n (Derivation.adDerivation B
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).symm
          (diagonalTorusPoints s)) d) i j =
      (SplitTorus.pointsMulEquiv s (ULift.up i) : B) * tangentMatrix n d i j *
        (((SplitTorus.pointsMulEquiv s (ULift.up j))⁻¹ : Bˣ) : B) := by
  have hg : counitPointsMulEquiv n
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R n) B).symm
          (diagonalTorusPoints s)) =
      diagGL fun a => SplitTorus.pointsMulEquiv s (ULift.up a) := by
    rw [counitPointsMulEquiv_eq_pointsMulEquiv,
      ← Bialgebra.CounitAlgebra.pointsMulEquiv_eq_mapValue, MulEquiv.apply_symm_apply,
      pointsMulEquiv_diagonalTorusPoints]
    congr 1
    funext a
    exact diagonalTorusCoordinates_apply _ a
  exact tangentMatrix_adDerivation_apply_of_diagGL hg i j

end

end TauCeti.GeneralLinear
