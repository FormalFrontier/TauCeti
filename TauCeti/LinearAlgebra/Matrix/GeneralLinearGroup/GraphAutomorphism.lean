/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The pinned type-A graph automorphism on matrices

For a commutative ring `A`, inverse transpose is an automorphism of `GL_n(A)`. In type `A_r`,
conjugating it by the signed reversal matrix gives the pinned graph automorphism

```text
g ↦ Q (g⁻¹)ᵀ Q⁻¹,
```

where `Q` reverses the standard basis and alternates its signs. The sign correction is essential:
it makes the automorphism carry each positive simple-root transvection to the positive
simple-root transvection at the reversed Dynkin node, with the parameter unchanged. Without it,
inverse transpose would introduce a minus sign.

The construction is over an arbitrary commutative ring and is natural under ring homomorphisms.
It is the matrix-points input for the graph automorphism of the full-weight type-`A` Chevalley
carrier.

## Main definitions

* `Matrix.GeneralLinearGroup.inverseTranspose`: the automorphism `g ↦ (g⁻¹)ᵀ`.
* `TauCeti.typeAGraphConjugator`: the signed reversal matrix `Q`.
* `TauCeti.typeAGraphAutomorphism`: the pinned graph automorphism `g ↦ Q (g⁻¹)ᵀ Q⁻¹`.

## Main results

* `TauCeti.typeAGraphAutomorphism_transvectionUnit`: the sign-free equation on every positive
  simple-root subgroup.
* `TauCeti.typeAGraphAutomorphism_mul_self`: the automorphism has order dividing two.
* `TauCeti.map_typeAGraphAutomorphism`: the construction is natural in the coefficient ring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.

This supplies the matrix-points prerequisite for the pinned type-`A` graph automorphism in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md` for the Steinberg map defining `²A_r(q)`.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {A : Type v} [CommRing A]

/-- Transpose an invertible matrix, retaining its transposed inverse as inverse data. This is
anti-multiplicative; composing it with inversion below gives a group automorphism. -/
private def transposeUnit (g : GL n A) : GL n A where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]

/-- **Inverse transpose on the general linear group.** This is the group automorphism
`g ↦ (g⁻¹)ᵀ`. -/
def inverseTranspose : GL n A ≃* GL n A where
  toFun g := transposeUnit g⁻¹
  invFun g := transposeUnit g⁻¹
  left_inv g := by
    apply Units.ext
    simp [transposeUnit, Matrix.transpose_transpose]
  right_inv g := by
    apply Units.ext
    simp [transposeUnit, Matrix.transpose_transpose]
  map_mul' g h := by
    apply Units.ext
    simp [transposeUnit, Matrix.transpose_mul]

/-- The matrix underlying inverse transpose is `(g⁻¹)ᵀ`. -/
@[simp]
theorem coe_inverseTranspose (g : GL n A) :
    (inverseTranspose g : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A).transpose :=
  (rfl)

/-- Inverse transpose is an involution. -/
@[simp]
theorem inverseTranspose_inverseTranspose (g : GL n A) :
    inverseTranspose (inverseTranspose g) = g :=
  (inverseTranspose : GL n A ≃* GL n A).left_inv g

/-- Inverse transpose commutes with entrywise application of a ring homomorphism. -/
@[simp]
theorem map_inverseTranspose {B : Type*} [CommRing B] (f : A →+* B) (g : GL n A) :
    map f (inverseTranspose g) = inverseTranspose (map f g) := by
  apply Units.ext
  ext i j
  rfl

end Matrix.GeneralLinearGroup

namespace TauCeti

universe u

variable {A : Type u} [CommRing A]

/-- The alternating diagonal signs used to pin the type-`A_r` graph automorphism. -/
private def typeAGraphSign (i : Fin (r + 1)) : Aˣ := (-1 : Aˣ) ^ (i : ℕ)

/-- The signed reversal matrix `Q` used in the pinned type-`A_r` graph automorphism. It first
reverses the standard basis and then applies alternating signs. -/
def typeAGraphConjugator (r : ℕ) (A : Type u) [CommRing A] : GL (Fin (r + 1)) A :=
  diagGL (typeAGraphSign (A := A)) * permutationGL (k := A) Fin.revPerm

/-- **The pinned graph automorphism of the type-`A_r` matrix group.** It is signed reverse
inverse transpose, `g ↦ Q (g⁻¹)ᵀ Q⁻¹`. -/
def typeAGraphAutomorphism (r : ℕ) (A : Type u) [CommRing A] :
    GL (Fin (r + 1)) A ≃* GL (Fin (r + 1)) A :=
  Matrix.GeneralLinearGroup.inverseTranspose.trans (MulAut.conj (typeAGraphConjugator r A))

/-- The type-`A` graph automorphism is conjugated inverse transpose. -/
theorem typeAGraphAutomorphism_apply (r : ℕ) (g : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A g =
      typeAGraphConjugator r A * Matrix.GeneralLinearGroup.inverseTranspose g *
        (typeAGraphConjugator r A)⁻¹ :=
  (rfl)

private theorem inverseTranspose_diagGL_typeAGraphSign (r : ℕ) :
    Matrix.GeneralLinearGroup.inverseTranspose
        (diagGL (typeAGraphSign (A := A) : Fin (r + 1) → Aˣ)) =
      diagGL (typeAGraphSign (A := A)) := by
  have hInv :
      (diagGL (typeAGraphSign (A := A) : Fin (r + 1) → Aˣ))⁻¹ =
        diagGL (fun i => (typeAGraphSign (A := A) i)⁻¹) := by
    rw [← map_inv]
    rfl
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, hInv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [typeAGraphSign, Matrix.transpose_apply]
  · have hji : j ≠ i := Ne.symm hij
    simp [typeAGraphSign, Matrix.transpose_apply, hij, hji]

private theorem permutationGL_rev_inv (r : ℕ) :
    (permutationGL (k := A) (Fin.revPerm : Equiv.Perm (Fin (r + 1))))⁻¹ =
      permutationGL (k := A) Fin.revPerm := by
  rw [← map_inv]
  congr 1

private theorem inverseTranspose_permutationGL_rev (r : ℕ) :
    Matrix.GeneralLinearGroup.inverseTranspose
        (permutationGL (k := A) (Fin.revPerm : Equiv.Perm (Fin (r + 1)))) =
      permutationGL (k := A) Fin.revPerm := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, permutationGL_rev_inv]
  simp only [permutationGL_coe, Matrix.transpose_permMatrix, inv_inv]
  exact congrArg (fun σ : Equiv.Perm (Fin (r + 1)) => σ.permMatrix A)
    Fin.revPerm_symm.symm

private theorem inverseTranspose_typeAGraphConjugator (r : ℕ) :
    Matrix.GeneralLinearGroup.inverseTranspose (typeAGraphConjugator r A) =
      typeAGraphConjugator r A := by
  rw [typeAGraphConjugator, map_mul, inverseTranspose_diagGL_typeAGraphSign,
    inverseTranspose_permutationGL_rev]

/-- The square of the signed reversal matrix is the scalar matrix `(-1)^r I`. -/
theorem typeAGraphConjugator_mul_self (r : ℕ) :
    typeAGraphConjugator r A * typeAGraphConjugator r A =
      Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) := by
  let d : GL (Fin (r + 1)) A := diagGL (typeAGraphSign (A := A))
  let p : GL (Fin (r + 1)) A := permutationGL (k := A) Fin.revPerm
  have hp : p * p = 1 :=
    inv_eq_iff_mul_eq_one.mp (permutationGL_rev_inv (A := A) r)
  have hpd : p * d * p⁻¹ = diagGL (fun i => typeAGraphSign (A := A) i.rev) := by
    simpa only [p, d, Equiv.Perm.inv_def, Fin.revPerm_symm, Fin.revPerm_apply] using
      permutationGL_mul_diagGL_mul_inv (k := A)
        (Fin.revPerm : Equiv.Perm (Fin (r + 1))) (typeAGraphSign (A := A))
  -- Normalize the public conjugator definition to the local names used in the calculation.
  change (d * p) * (d * p) = _
  calc
    _ = d * (p * d * p⁻¹) * (p * p) := by group
    _ = d * diagGL (fun i => typeAGraphSign (A := A) i.rev) * 1 := by rw [hpd, hp]
    _ = diagGL (fun i =>
        typeAGraphSign (A := A) i * typeAGraphSign (A := A) i.rev) := by
      rw [mul_one, ← map_mul]
      rfl
    _ = diagGL (fun _ : Fin (r + 1) => (-1 : Aˣ) ^ r) := by
      congr 1
      funext i
      simp only [typeAGraphSign, ← pow_add]
      congr 1
      simp [Fin.val_rev]
      omega
    _ = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) := by
      apply Units.ext
      rw [diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar]
      rw [Matrix.scalar_apply]

/-- Applying the pinned type-`A` graph automorphism twice is the identity. -/
@[simp]
theorem typeAGraphAutomorphism_typeAGraphAutomorphism (r : ℕ)
    (g : GL (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A (typeAGraphAutomorphism r A g) = g := by
  rw [typeAGraphAutomorphism_apply, typeAGraphAutomorphism_apply, map_mul, map_mul,
    inverseTranspose_typeAGraphConjugator,
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose, map_inv,
    inverseTranspose_typeAGraphConjugator]
  calc
    typeAGraphConjugator r A *
          (typeAGraphConjugator r A * g * (typeAGraphConjugator r A)⁻¹) *
        (typeAGraphConjugator r A)⁻¹ =
        (typeAGraphConjugator r A * typeAGraphConjugator r A) * g *
          (typeAGraphConjugator r A * typeAGraphConjugator r A)⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r) * g *
          (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ((-1 : Aˣ) ^ r))⁻¹ := by
      rw [typeAGraphConjugator_mul_self]
    _ = g := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      group

/-- The pinned type-`A` graph automorphism has order dividing two. -/
@[simp]
theorem typeAGraphAutomorphism_mul_self (r : ℕ) :
    typeAGraphAutomorphism r A * typeAGraphAutomorphism r A = 1 := by
  apply DFunLike.ext _ _
  intro g
  exact typeAGraphAutomorphism_typeAGraphAutomorphism r g

private theorem permutationGL_conj_transvectionUnit {i j : Fin (r + 1)}
    (hij : i ≠ j) (c : A) :
    permutationGL (k := A) Fin.revPerm * transvectionUnit hij c *
        (permutationGL (k := A) Fin.revPerm)⁻¹ =
      transvectionUnit (Fin.rev_injective.ne hij) c := by
  rw [permutationGL_rev_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, permutationGL_coe]
  simp only [coe_transvectionUnit, Equiv.Perm.inv_def]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp [Matrix.transvection, Matrix.submatrix_apply, Matrix.one_apply,
    Matrix.single_apply, Fin.revPerm_apply, Fin.rev_eq_iff, Fin.rev_injective.eq_iff]

/-- Inverse transpose swaps the indices of a transvection and negates its parameter. -/
@[simp]
theorem inverseTranspose_transvectionUnit {n : Type*} [Fintype n] [DecidableEq n] {i j : n}
    (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.inverseTranspose (transvectionUnit hij c) =
      transvectionUnit hij.symm (-c) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, transvectionUnit_inv,
    coe_transvectionUnit, coe_transvectionUnit]
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]

private theorem typeAGraphSign_castSucc_mul_neg_mul_inv_succ (i : Fin r) (c : A) :
    ((typeAGraphSign (A := A) i.castSucc : A) * (-c) *
      ((typeAGraphSign (A := A) i.succ)⁻¹ : Aˣ)) = c := by
  let s : Aˣ := typeAGraphSign (A := A) i.castSucc
  have hs_sq : s * s = 1 := by
    dsimp only [s, typeAGraphSign, Fin.val_castSucc]
    rw [← pow_add, ← two_mul (i : ℕ), pow_mul]
    simp
  have hs_inv : s⁻¹ = s := inv_eq_iff_mul_eq_one.mpr hs_sq
  have hsucc : typeAGraphSign (A := A) i.succ = -s := by
    dsimp only [s, typeAGraphSign, Fin.val_succ]
    rw [pow_succ]
    simp
  rw [hsucc, inv_neg, hs_inv]
  simp only [Units.val_neg]
  have hcast : typeAGraphSign (A := A) i.castSucc = s := rfl
  rw [hcast]
  -- Expose the values of the units so the remaining equality is an identity in `A`.
  change (s : A) * (-c) * (-(s : A)) = c
  have hneg : (s : A) * (-c) * (-(s : A)) = (s : A) * c * (s : A) := by ring
  rw [hneg]
  calc
    (s : A) * c * (s : A) = c * ((s : A) * (s : A)) := by ac_rfl
    _ = c := by rw [show (s : A) * (s : A) = 1 from congrArg Units.val hs_sq, mul_one]

/-- **The pinned graph automorphism reverses the positive simple-root subgroups without changing
their parameters.** In Bourbaki numbering, the node `i` is carried to `i.rev`. -/
@[simp]
theorem typeAGraphAutomorphism_transvectionUnit (r : ℕ) (i : Fin r) (c : A) :
    typeAGraphAutomorphism r A
        (transvectionUnit (Fin.castSucc_lt_succ (i := i)).ne c) =
      transvectionUnit (Fin.castSucc_lt_succ (i := i.rev)).ne c := by
  rw [typeAGraphAutomorphism_apply, inverseTranspose_transvectionUnit]
  let d : GL (Fin (r + 1)) A := diagGL (typeAGraphSign (A := A))
  let p : GL (Fin (r + 1)) A := permutationGL (k := A) Fin.revPerm
  let hneg : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ (i := i)).ne'
  let hpos : i.rev.castSucc ≠ i.rev.succ := (Fin.castSucc_lt_succ (i := i.rev)).ne
  -- Normalize the conjugator and the two index inequalities to their local names.
  change (d * p) * transvectionUnit hneg (-c) * (d * p)⁻¹ = _
  calc
    _ = d * (p * transvectionUnit hneg (-c) * p⁻¹) * d⁻¹ := by group
    _ = d * transvectionUnit (Fin.rev_injective.ne hneg) (-c) * d⁻¹ := by
      rw [permutationGL_conj_transvectionUnit]
    _ = d * transvectionUnit hpos (-c) * d⁻¹ := by
      congr 3 <;> simp only [Fin.rev_succ, Fin.rev_castSucc]
    _ = transvectionUnit hpos
          (((typeAGraphSign (A := A)) i.rev.castSucc : A) * (-c) *
            (((typeAGraphSign (A := A)) i.rev.succ)⁻¹ : Aˣ)) := by
      rw [diagGL_mul_transvectionUnit_mul_inv]
    _ = transvectionUnit hpos c := by
      rw [typeAGraphSign_castSucc_mul_neg_mul_inv_succ]

/-- Entrywise base change carries the signed reversal matrix to the signed reversal matrix. -/
@[simp]
theorem map_typeAGraphConjugator {B : Type*} [CommRing B] (f : A →+* B) (r : ℕ) :
    Matrix.GeneralLinearGroup.map f (typeAGraphConjugator r A) =
      typeAGraphConjugator r B := by
  apply Units.ext
  ext i j
  simp [typeAGraphConjugator, typeAGraphSign]

/-- The pinned type-`A` graph automorphism is natural in the coefficient ring. -/
@[simp]
theorem map_typeAGraphAutomorphism {B : Type*} [CommRing B] (f : A →+* B) (r : ℕ)
    (g : GL (Fin (r + 1)) A) :
    Matrix.GeneralLinearGroup.map f (typeAGraphAutomorphism r A g) =
      typeAGraphAutomorphism r B (Matrix.GeneralLinearGroup.map f g) := by
  rw [typeAGraphAutomorphism_apply, typeAGraphAutomorphism_apply, map_mul, map_mul,
    Matrix.GeneralLinearGroup.map_inverseTranspose, map_inv, map_typeAGraphConjugator]

end TauCeti
