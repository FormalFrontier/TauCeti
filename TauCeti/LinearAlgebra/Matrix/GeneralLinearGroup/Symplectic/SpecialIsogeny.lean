/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The special isogeny of `Sp₄` in characteristic two

Over a field of characteristic two the pinned group of type `B₂ = C₂` admits an endomorphism `τ`
that exchanges the two root lengths, raising the parameter of a short simple root subgroup to the
defining characteristic and leaving that of a long one alone. It is the *special isogeny*, and the
finite Suzuki groups are cut out by the fixed points of its odd powers. This file constructs `τ`
on `TauCeti.GLSymplecticFin 2 R` for every commutative ring `R` of characteristic two, and proves
its action on the two simple root subgroups.

## The construction

`Sp₄` acts on `Λ² R⁴`, which is free of rank six. The alternating form gives a linear functional
`φ` on that module, and the form read as a bivector gives an invariant element `ω`. In
characteristic two, and only there, `φ ω = 2 = 0`, so `ω` lies in the rank-five kernel `W = ker φ`
and the quotient `W ⧸ ⟨ω⟩` is free of rank four, carries the induced alternating form, and is
acted on by `Sp₄`. Composing gives `Sp₄ → Sp₄`, and that composite is the special isogeny.

The four bivectors `e₀∧e₁`, `e₀∧e₃`, `e₂∧e₃`, `e₁∧e₂` are a basis of a complement of `⟨ω⟩` in `W`,
because they are exactly the coordinate bivectors on which the form vanishes, `ω` being supported
on the other two. So no correction term is needed when passing to the quotient, and the matrix of
the composite in that basis is simply the matrix of `2 × 2` minors of `g` on those four index
pairs. That matrix is `TauCeti.specialIsogenyMatrix`, and everything below is proved from the
minor formula rather than from the exterior square, which is why no exterior power appears.

The order of the four pairs is chosen so that the induced form is again the standard one: the
first pairs with the third and the second with the fourth, matching
`TauCeti.JFin 2 R`.

## Where characteristic two enters

Multiplicativity is Cauchy--Binet, `TauCeti.pairMinor_mul`, which expands a minor of a product
over all six index pairs. Four of the six terms assemble the product of the two minor matrices;
the other two involve the pairs `(0,2)` and `(1,3)` carrying the form. The symplectic condition
makes those two minors cancel in pairs, once along rows and once along columns
(`TauCeti.pairMinor_row_eq_zero` and `TauCeti.pairMinor_column_eq_zero`), and what is left of the
two extra terms is `2` times a product of minors. That is the only place the hypothesis is used,
and it is why the construction has no counterpart in odd characteristic.

That `τ g` is again symplectic is deduced rather than computed: `τ` commutes with the symplectic
adjoint `M ↦ -(J Mᵀ J)` in characteristic two, and for a symplectic `g` that adjoint is the
inverse, so `τ g` has `-(J (τ g)ᵀ J)` as an inverse, which is the symplectic condition.

## What is not proved here

The relation `τ ^ 2 = Frob₂` is not established below, and neither is any statement about fixed
points, finiteness or simplicity. What identifies `τ` here is its action on the numbered simple
root subgroups, which is the pinning the CFSG roadmap fixes.

## Main definitions

* `TauCeti.pairMinor`: the `2 × 2` minor of a matrix on an ordered row pair and column pair.
* `TauCeti.specialIsogenyMatrix`: the matrix of `2 × 2` minors on the four form-free index pairs.
* `TauCeti.specialIsogeny`: the resulting endomorphism of `TauCeti.GLSymplecticFin 2 R` in
  characteristic two.

## Main results

* `TauCeti.pairMinor_mul`: Cauchy--Binet for `2 × 2` minors of a `4 × 4` product.
* `TauCeti.specialIsogenyMatrix_mul`: multiplicativity on symplectic matrices in characteristic
  two.
* `TauCeti.specialIsogenyMatrix_mul_jFin_mul_transpose`: the image of a symplectic matrix is
  symplectic.
* `TauCeti.specialIsogeny_differenceShortRootUnit` and
  `TauCeti.specialIsogeny_positiveLongRootTransvectionUnit`: the pinning equations
  `τ (x_{e₀-e₁}(t)) = x_{2e₁}(t²)` and `τ (x_{2e₁}(t)) = x_{e₀-e₁}(t)`, which exchange the two
  root lengths with exponent two on the short root and one on the long root.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.3 and §13.4, for the exceptional isogenies and
  the groups their odd powers cut out.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ² = Frob_p`.

## Roadmap

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`, which lists "the special isogenies in characteristics
two and three" among its targets and says of them that they are statements about the pinned groups
and belong there rather than in any consumer. Its consumer is milestone `L2` of
`TauCetiRoadmap/CFSGStatement/README.md`, which owns everything between such an isogeny and a
finite group: `L2` fixes the exponent convention followed here, attaching `1` to a long simple root
and the defining characteristic to a short one, and the two pinning equations proved below are that
convention on the `B₂` diagram. The odd powers `τ ^ (2m+1)` that `L2` takes, and the ambient
carrier they are taken on, are not part of this file.
-/
public section

open Matrix

namespace TauCeti

universe u

variable {n : Type*} {R : Type u} [CommRing R]

/-- The `2 × 2` minor of a square matrix on the ordered row pair `p` and the ordered column
pair `q`. -/
def pairMinor (g : Matrix n n R) (p q : n × n) : R :=
  (g.submatrix ![p.1, p.2] ![q.1, q.2]).det

/-- The `2 × 2` minor written out. -/
theorem pairMinor_eq (g : Matrix n n R) (p q : n × n) :
    pairMinor g p q = g p.1 q.1 * g p.2 q.2 - g p.1 q.2 * g p.2 q.1 := by
  rw [pairMinor, Matrix.det_fin_two]
  simp

/-- **Cauchy--Binet for `2 × 2` minors of a `4 × 4` product.** -/
theorem pairMinor_mul (g h : Matrix (Fin 4) (Fin 4) R) (p q : Fin 4 × Fin 4) :
    pairMinor (g * h) p q =
      pairMinor g p (0, 1) * pairMinor h (0, 1) q +
        pairMinor g p (0, 2) * pairMinor h (0, 2) q +
        pairMinor g p (0, 3) * pairMinor h (0, 3) q +
        pairMinor g p (1, 2) * pairMinor h (1, 2) q +
        pairMinor g p (1, 3) * pairMinor h (1, 3) q +
        pairMinor g p (2, 3) * pairMinor h (2, 3) q := by
  simp only [pairMinor_eq, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-! ### The standard alternating form in rank two -/

/-- The transported alternating form of `Sp₄`, written out. -/
theorem jFin_two_eq : JFin 2 R = !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  have hJ : JFin 2 R =
      (Matrix.J (Fin 2) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← JFin_submatrix 2 (R := R), Matrix.submatrix_submatrix]
    simp
  have e0 : finSumFinEquiv.symm (0 : Fin (2 + 2)) = Sum.inl 0 := by rw [Equiv.symm_apply_eq]; rfl
  have e1 : finSumFinEquiv.symm (1 : Fin (2 + 2)) = Sum.inl 1 := by rw [Equiv.symm_apply_eq]; rfl
  have e2 : finSumFinEquiv.symm (2 : Fin (2 + 2)) = Sum.inr 0 := by rw [Equiv.symm_apply_eq]; rfl
  have e3 : finSumFinEquiv.symm (3 : Fin (2 + 2)) = Sum.inr 1 := by rw [Equiv.symm_apply_eq]; rfl
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, e2, e3, Matrix.J, Matrix.fromBlocks]

/-- The transported alternating form squares to `-1`. -/
theorem jFin_two_mul_self : JFin 2 R * JFin 2 R = -1 := by
  rw [jFin_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

variable {g : Matrix (Fin 4) (Fin 4) R}

/-- The column form of the symplectic condition. -/
theorem transpose_mul_jFin_mul_self (hg : g * JFin 2 R * gᵀ = JFin 2 R) :
    gᵀ * JFin 2 R * g = JFin 2 R := by
  have hsq : JFin 2 R * JFin 2 R = -1 := jFin_two_mul_self
  have hright : g * (-(JFin 2 R * gᵀ * JFin 2 R)) = 1 := by
    rw [mul_neg, ← mul_assoc, ← mul_assoc, hg, hsq, neg_neg]
  have hleft := mul_eq_one_comm.mp hright
  calc gᵀ * JFin 2 R * g
      = -(JFin 2 R * JFin 2 R) * (gᵀ * JFin 2 R * g) := by rw [hsq]; simp
    _ = JFin 2 R * (-(JFin 2 R * gᵀ * JFin 2 R) * g) := by noncomm_ring
    _ = JFin 2 R := by rw [hleft, mul_one]

/-- The row identity: the two `J`-supported minors on a fixed row pair cancel. -/
theorem pairMinor_row_eq_zero (hg : g * JFin 2 R * gᵀ = JFin 2 R)
    (p : Fin 4 × Fin 4) (hp : JFin 2 R p.1 p.2 = 0) :
    pairMinor g p (0, 2) + pairMinor g p (1, 3) = 0 := by
  have h := congrFun (congrFun hg p.1) p.2
  rw [hp] at h
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, jFin_two_eq] at h
  simp only [pairMinor_eq]
  linear_combination -h

/-- The column identity: the two `J`-supported minors on a fixed column pair cancel. -/
theorem pairMinor_column_eq_zero (hg : g * JFin 2 R * gᵀ = JFin 2 R)
    (q : Fin 4 × Fin 4) (hq : JFin 2 R q.1 q.2 = 0) :
    pairMinor g (0, 2) q + pairMinor g (1, 3) q = 0 := by
  have h := congrFun (congrFun (transpose_mul_jFin_mul_self hg) q.1) q.2
  rw [hq] at h
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, jFin_two_eq] at h
  simp only [pairMinor_eq]
  linear_combination -h

/-! ### The special isogeny on matrices -/

/-- The four coordinate pairs whose `2 × 2` minors carry the special isogeny. -/
def specialIsogenyPair : Fin 4 → Fin 4 × Fin 4 := ![(0, 1), (0, 3), (2, 3), (1, 2)]

@[simp] theorem specialIsogenyPair_zero : specialIsogenyPair 0 = (0, 1) := by
  rw [specialIsogenyPair]; rfl

@[simp] theorem specialIsogenyPair_one : specialIsogenyPair 1 = (0, 3) := by
  rw [specialIsogenyPair]; rfl

@[simp] theorem specialIsogenyPair_two : specialIsogenyPair 2 = (2, 3) := by
  rw [specialIsogenyPair]; rfl

@[simp] theorem specialIsogenyPair_three : specialIsogenyPair 3 = (1, 2) := by
  rw [specialIsogenyPair]; rfl

/-- The `J`-supported pairs are exactly the two omitted ones. -/
theorem jFin_specialIsogenyPair (i : Fin 4) :
    JFin 2 R (specialIsogenyPair i).1 (specialIsogenyPair i).2 = 0 := by
  fin_cases i <;> simp [specialIsogenyPair, jFin_two_eq]

/-- The matrix of `2 × 2` minors on the four pairs. -/
def specialIsogenyMatrix (g : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => pairMinor g (specialIsogenyPair i) (specialIsogenyPair j)

@[simp]
theorem specialIsogenyMatrix_apply (g : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    specialIsogenyMatrix g i j = pairMinor g (specialIsogenyPair i) (specialIsogenyPair j) := by
  rw [specialIsogenyMatrix]
  rfl

/-- The special isogeny is multiplicative on symplectic matrices in characteristic two. -/
theorem specialIsogenyMatrix_mul [CharP R 2] {g h : Matrix (Fin 4) (Fin 4) R}
    (hg : g * JFin 2 R * gᵀ = JFin 2 R) (hh : h * JFin 2 R * hᵀ = JFin 2 R) :
    specialIsogenyMatrix (g * h) = specialIsogenyMatrix g * specialIsogenyMatrix h := by
  have h2 : (2 : R) = 0 := by
    have := CharP.cast_eq_zero R 2
    simpa using this
  ext i j
  have hgp := pairMinor_row_eq_zero hg (specialIsogenyPair i) (jFin_specialIsogenyPair i)
  have hhq := pairMinor_column_eq_zero hh (specialIsogenyPair j) (jFin_specialIsogenyPair j)
  rw [specialIsogenyMatrix_apply, pairMinor_mul, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [specialIsogenyMatrix_apply, specialIsogenyPair_zero, specialIsogenyPair_one,
    specialIsogenyPair_two, specialIsogenyPair_three]
  linear_combination pairMinor g (specialIsogenyPair i) (0, 2) * hhq -
    pairMinor h (1, 3) (specialIsogenyPair j) * hgp +
    (pairMinor g (specialIsogenyPair i) (1, 3) *
      pairMinor h (1, 3) (specialIsogenyPair j)) * h2

/-- A matrix preserving the transported alternating form has determinant one. -/
theorem det_eq_one_of_mul_jFin (hg : g * JFin 2 R * gᵀ = JFin 2 R) : g.det = 1 := by
  have hmem : g.submatrix finSumFinEquiv finSumFinEquiv ∈
      Matrix.symplecticGroup (Fin 2) R := by
    rw [SymplecticGroup.mem_iff, ← JFin_submatrix 2 (R := R), Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]
  have hdet := SymplecticGroup.det_eq_one hmem
  rwa [Matrix.det_submatrix_equiv_self] at hdet

/-! ### Compatibility with inversion -/

/-- For a symplectic matrix, `-(J gᵀ J)` is a two-sided inverse. -/
theorem mul_neg_jFin_mul_transpose_mul_jFin (hg : g * JFin 2 R * gᵀ = JFin 2 R) :
    g * -(JFin 2 R * gᵀ * JFin 2 R) = 1 := by
  rw [mul_neg, ← mul_assoc, ← mul_assoc, hg, jFin_two_mul_self, neg_neg]

/-- The inverse of a symplectic matrix is symplectic. -/
theorem neg_jFin_mul_transpose_mul_jFin_symplectic (hg : g * JFin 2 R * gᵀ = JFin 2 R) :
    -(JFin 2 R * gᵀ * JFin 2 R) * JFin 2 R * (-(JFin 2 R * gᵀ * JFin 2 R))ᵀ = JFin 2 R := by
  set h : Matrix (Fin 4) (Fin 4) R := -(JFin 2 R * gᵀ * JFin 2 R) with hdef
  have hgh : g * h = 1 := mul_neg_jFin_mul_transpose_mul_jFin hg
  have hhg : h * g = 1 := mul_eq_one_comm.mp hgh
  calc h * JFin 2 R * hᵀ
      = h * (g * JFin 2 R * gᵀ) * hᵀ := by rw [hg]
    _ = h * g * JFin 2 R * (h * g)ᵀ := by rw [Matrix.transpose_mul]; noncomm_ring
    _ = JFin 2 R := by rw [hhg]; simp

/-- The special isogeny fixes the identity. -/
@[simp]
theorem specialIsogenyMatrix_one :
    specialIsogenyMatrix (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairMinor_eq]

/-- The symplectic adjoint `-(J Mᵀ J)`, written out. -/
theorem neg_jFin_mul_transpose_mul_jFin_eq (M : Matrix (Fin 4) (Fin 4) R) :
    -(JFin 2 R * Mᵀ * JFin 2 R) =
      !![M 2 2, M 3 2, -M 0 2, -M 1 2;
        M 2 3, M 3 3, -M 0 3, -M 1 3;
        -M 2 0, -M 3 0, M 0 0, M 1 0;
        -M 2 1, -M 3 1, M 0 1, M 1 1] := by
  rw [jFin_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, -Matrix.cons_mul]

/-- In characteristic two the special isogeny commutes with the symplectic adjoint. -/
theorem specialIsogenyMatrix_neg_jFin_mul_transpose_mul_jFin [CharP R 2]
    (g : Matrix (Fin 4) (Fin 4) R) :
    specialIsogenyMatrix (-(JFin 2 R * gᵀ * JFin 2 R)) =
      -(JFin 2 R * (specialIsogenyMatrix g)ᵀ * JFin 2 R) := by
  rw [neg_jFin_mul_transpose_mul_jFin_eq, neg_jFin_mul_transpose_mul_jFin_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      specialIsogenyMatrix_apply, specialIsogenyPair_zero, specialIsogenyPair_one,
      specialIsogenyPair_two, specialIsogenyPair_three, pairMinor_eq, of_apply, cons_val',
      cons_val, cons_val_zero, cons_val_one, cons_val_fin_one] <;>
    (try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;> ring

/-- The special isogeny of a symplectic matrix is symplectic. -/
theorem specialIsogenyMatrix_mul_jFin_mul_transpose [CharP R 2]
    (hg : g * JFin 2 R * gᵀ = JFin 2 R) :
    specialIsogenyMatrix g * JFin 2 R * (specialIsogenyMatrix g)ᵀ = JFin 2 R := by
  have hh := neg_jFin_mul_transpose_mul_jFin_symplectic hg
  have hgh := mul_neg_jFin_mul_transpose_mul_jFin hg
  have hmul : specialIsogenyMatrix g *
      specialIsogenyMatrix (-(JFin 2 R * gᵀ * JFin 2 R)) = 1 := by
    rw [← specialIsogenyMatrix_mul hg hh, hgh, specialIsogenyMatrix_one]
  rw [specialIsogenyMatrix_neg_jFin_mul_transpose_mul_jFin, Matrix.mul_neg] at hmul
  have h1 : specialIsogenyMatrix g *
      (JFin 2 R * (specialIsogenyMatrix g)ᵀ * JFin 2 R) = -1 := neg_eq_iff_eq_neg.mp hmul
  have key : specialIsogenyMatrix g * JFin 2 R * (specialIsogenyMatrix g)ᵀ * JFin 2 R =
      JFin 2 R * JFin 2 R := by
    rw [jFin_two_mul_self, ← h1]
    noncomm_ring
  have hJinv : JFin 2 R * -JFin 2 R = 1 := by
    rw [Matrix.mul_neg, jFin_two_mul_self, neg_neg]
  calc specialIsogenyMatrix g * JFin 2 R * (specialIsogenyMatrix g)ᵀ
      = specialIsogenyMatrix g * JFin 2 R * (specialIsogenyMatrix g)ᵀ *
          (JFin 2 R * -JFin 2 R) := by rw [hJinv, Matrix.mul_one]
    _ = specialIsogenyMatrix g * JFin 2 R * (specialIsogenyMatrix g)ᵀ * JFin 2 R *
          -JFin 2 R := by noncomm_ring
    _ = JFin 2 R * JFin 2 R * -JFin 2 R := by rw [key]
    _ = JFin 2 R := by rw [jFin_two_mul_self]; simp

/-! ### The special isogeny as an endomorphism of `Sp₄` -/

section CharTwo

variable [CharP R 2]

/-- The special isogeny of `Sp₄`, as a monoid homomorphism into the matrix monoid. -/
def specialIsogenyToMatrix :
    GLSymplecticFin 2 R →* Matrix (Fin (2 + 2)) (Fin (2 + 2)) R where
  toFun M := specialIsogenyMatrix ((M : GL (Fin (2 + 2)) R) :
    Matrix (Fin (2 + 2)) (Fin (2 + 2)) R)
  map_one' := by simp
  map_mul' M N := by
    simpa using specialIsogenyMatrix_mul (GLSymplecticFin.mem_iff.mp M.2)
      (GLSymplecticFin.mem_iff.mp N.2)

@[simp]
theorem specialIsogenyToMatrix_apply (M : GLSymplecticFin 2 R) :
    specialIsogenyToMatrix M =
      specialIsogenyMatrix ((M : GL (Fin (2 + 2)) R) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  rw [specialIsogenyToMatrix]
  rfl

/-- **The special isogeny of `Sp₄` in characteristic two.** -/
def specialIsogeny : GLSymplecticFin 2 R →* GLSymplecticFin 2 R :=
  MonoidHom.codRestrict (specialIsogenyToMatrix (R := R)).toHomUnits (GLSymplecticFin 2 R)
    fun M => by
      rw [GLSymplecticFin.mem_iff]
      simpa using specialIsogenyMatrix_mul_jFin_mul_transpose
        (GLSymplecticFin.mem_iff.mp M.2)

/-- The matrix underlying the special isogeny is the matrix of `2 × 2` minors. -/
@[simp]
theorem coe_specialIsogeny (M : GLSymplecticFin 2 R) :
    (((specialIsogeny M : GLSymplecticFin 2 R) : GL (Fin (2 + 2)) R) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      specialIsogenyMatrix ((M : GL (Fin (2 + 2)) R) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  rw [specialIsogeny]
  simp

end CharTwo

/-! ### The action on the simple root subgroups -/

private theorem fse_inl_zero : finSumFinEquiv (Sum.inl (0 : Fin 2)) = (0 : Fin (2 + 2)) := rfl
private theorem fse_inl_one : finSumFinEquiv (Sum.inl (1 : Fin 2)) = (1 : Fin (2 + 2)) := rfl
private theorem fse_inr_zero : finSumFinEquiv (Sum.inr (0 : Fin 2)) = (2 : Fin (2 + 2)) := rfl
private theorem fse_inr_one : finSumFinEquiv (Sum.inr (1 : Fin 2)) = (3 : Fin (2 + 2)) := rfl

/-- The short simple root element `x_{e₀-e₁}(t)` of `Sp₄`, written out. -/
theorem coe_differenceShortRootUnit_zero_one (t : R) :
    (((GLSymplecticFin.differenceShortRootUnit (show (0 : Fin 2) ≠ 1 by decide) t :
          GLSymplecticFin 2 R) : GL (Fin (2 + 2)) R) :
        Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      !![1, t, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -t, 1] := by
  rw [GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul, coe_transvectionUnit,
    coe_transvectionUnit]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_four, fse_inl_zero, fse_inl_one, fse_inr_zero, fse_inr_one]

/-- The long simple root element `x_{2e₁}(t)` of `Sp₄`, written out. -/
theorem coe_positiveLongRootTransvectionUnit_one (t : R) :
    (((GLSymplecticFin.positiveLongRootTransvectionUnit (1 : Fin 2) t : GLSymplecticFin 2 R) :
        GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      !![1, 0, 0, 0; 0, 1, 0, t; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [GLSymplecticFin.coe_positiveLongRootTransvectionUnit, coe_transvectionUnit]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.single, fse_inl_one, fse_inr_one]

/-- The special isogeny carries the short simple root subgroup to the long one and squares the
parameter: `τ (x_{e₀-e₁}(t)) = x_{2e₁}(t²)`. -/
theorem specialIsogeny_differenceShortRootUnit [CharP R 2] (t : R) :
    specialIsogeny
        (GLSymplecticFin.differenceShortRootUnit (show (0 : Fin 2) ≠ 1 by decide) t) =
      GLSymplecticFin.positiveLongRootTransvectionUnit 1 (t ^ 2) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny, coe_differenceShortRootUnit_zero_one,
    coe_positiveLongRootTransvectionUnit_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [specialIsogenyMatrix_apply, specialIsogenyPair_zero, specialIsogenyPair_one,
      specialIsogenyPair_two, specialIsogenyPair_three, pairMinor_eq, of_apply, cons_val',
      cons_val, cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk] <;>
    (first | ring1 | (rw [CharTwo.neg_eq]; ring1))

/-- The special isogeny carries the long simple root subgroup to the short one and keeps the
parameter: `τ (x_{2e₁}(t)) = x_{e₀-e₁}(t)`. -/
theorem specialIsogeny_positiveLongRootTransvectionUnit [CharP R 2] (t : R) :
    specialIsogeny (GLSymplecticFin.positiveLongRootTransvectionUnit 1 t) =
      GLSymplecticFin.differenceShortRootUnit (show (0 : Fin 2) ≠ 1 by decide) t := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny, coe_differenceShortRootUnit_zero_one,
    coe_positiveLongRootTransvectionUnit_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [specialIsogenyMatrix_apply, specialIsogenyPair_zero, specialIsogenyPair_one,
      specialIsogenyPair_two, specialIsogenyPair_three, pairMinor_eq, of_apply, cons_val',
      cons_val, cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk] <;> ring1

end TauCeti
