/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Borel` is the subgroup every statement below is about, and this module re-exports
-- the `GL` notation together with the coercion of an element of `GL n R` to its matrix.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- `TauCeti.GL2WeylElement` occurs in the statement of the inverse of the identification with
-- `OnePoint`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.jordanGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `TauCeti.GL2NonSplitTorusHom` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- `TauCeti.stabilizer_quotientGroup_mk` is the fixed-coset criterion the counts below run on, and
-- this module re-exports the action of a group on the cosets of a subgroup.
public import TauCeti.GroupTheory.QuotientGroup.Basic
-- `OnePoint F` with its `GL (Fin 2) F` action is the model of the projective line used here.
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
-- `Set.ncard` occurs in the statements below.
public import Mathlib.Data.Set.Card

/-!
# The cosets of the Borel subgroup of `GL₂` are the projective line

The coset space `GL₂(F) ⧸ B` of the Borel subgroup of invertible upper-triangular matrices is the
**projective line** over `F`: a coset `g B` remembers exactly the line spanned by the first column
of `g`, because right multiplication by an upper-triangular matrix rescales that column. Mathlib
already models the projective line as `OnePoint F`, with the Möbius action of `GL (Fin 2) F` on it
(`OnePoint.instGLAction`), and this file supplies the missing bridge: the Borel subgroup is the
stabilizer of the point at infinity (`TauCeti.GL2Borel.stabilizer_infty`), and the action is
transitive, so translating `∞` identifies the two
(`TauCeti.GL2Borel.quotientEquivOnePoint`), equivariantly.

The point of the identification is the **fixed-coset count**, which the bridge turns into a
fixed-point count on `OnePoint F`, where Mathlib's `OnePoint.smul_infty_eq_self_iff` and
`Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff` compute it. For an element
`!![a, b; 0, d]` of the Borel subgroup itself, `∞` is fixed and the fixed affine points are the
roots of the linear equation `(d - a) t = b`; so there are two fixed points when `a ≠ d`, and one
when `a = d` and `b ≠ 0`. A scalar matrix is central, so it fixes every coset, and an element with
no upper-triangular conjugate fixes none.

Those four statements are read off for the four families of conjugacy classes of `GL₂(𝔽_q)`: a
scalar matrix fixes all `q + 1` cosets, a diagonal matrix with distinct entries `2`, a Jordan block
`1`, and an element of the non-split torus that does not come from `F` fixes `0`. Those four
numbers, less one, are the character values of the Steinberg representation.

Only the scalar count needs `F` to be finite, and only because it is the one whose value is the
number of points; the other three are the same over any field, and the two general Borel counts
hold there too.

## Main definitions

* `TauCeti.GL2Borel.quotientEquivOnePoint`: the identification `GL₂(F) ⧸ B ≃ OnePoint F` of the
  coset space with Mathlib's model of the projective line, by translating the point at infinity.

## Main results

* `TauCeti.GL2Borel.stabilizer_infty`: the Borel subgroup is the stabilizer of `∞` for the Möbius
  action of `GL₂(F)` on `OnePoint F`.
* `TauCeti.GL2Borel.quotientEquivOnePoint_smul`: that identification is equivariant, whence
  `TauCeti.GL2Borel.natCard_fixedCosets_eq_ncard`, the fixed cosets of `g` are counted by its fixed
  points on `OnePoint F`.
* `TauCeti.GL2Borel.natCard_fixedCosets_of_mem_of_diagonal_ne` and
  `TauCeti.GL2Borel.natCard_fixedCosets_of_mem_of_diagonal_eq_of_upperRight_ne_zero`: an
  upper-triangular element fixes exactly `2` cosets when its diagonal entries differ, and exactly
  `1` when they agree and it is not diagonal.
* `TauCeti.GL2Borel.scalar_smul_quotient_eq_self` and
  `TauCeti.GL2Borel.natCard_fixedCosets_eq_zero`: a scalar matrix fixes every coset, and an element
  with no upper-triangular conjugate fixes none.
* `TauCeti.GL2Borel.natCard_fixedCosets_scalar`, `TauCeti.GL2Borel.natCard_fixedCosets_diagGL`,
  `TauCeti.GL2Borel.natCard_fixedCosets_jordanGL` and
  `TauCeti.GL2Borel.natCard_fixedCosets_gl2NonSplitTorusHom`: the counts `q + 1`, `2`, `1` and `0`
  for the four families of conjugacy classes of `GL₂(𝔽_q)`.

## References

This supplies the fixed-point counts on the projective line that the character-value formulas of
Layer 9 ("the representation theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` need. See also W. Fulton and
J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2, and C. Bonnafé,
*Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

namespace TauCeti

open _root_.Matrix OnePoint
open scoped Pointwise

universe u

namespace GL2Borel

section CommRing

variable {R : Type u} [CommRing R]

/-- **A scalar matrix fixes every coset** of the Borel subgroup: scalar matrices are central, so a
conjugate of one is itself, and they are upper triangular. -/
@[simp]
theorem scalar_smul_quotient_eq_self (u : Rˣ) (c : GL (Fin 2) R ⧸ GL2Borel R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u • c = c := by
  induction c using QuotientGroup.induction_on with
  | H y =>
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, Matrix.GeneralLinearGroup.scalar_commute]
    exact QuotientGroup.mk_mul_of_mem y (scalar_mem R u)

/-- **An element with no upper-triangular conjugate fixes no coset at all.** A fixed coset would
exhibit such a conjugate. Over a field this is the elliptic case: the matrix has no eigenline. -/
theorem natCard_fixedCosets_eq_zero {g : GL (Fin 2) R}
    (h : ∀ y : GL (Fin 2) R, y * g * y⁻¹ ∉ GL2Borel R) :
    Nat.card {c : GL (Fin 2) R ⧸ GL2Borel R // g • c = c} = 0 := by
  have hnone : ∀ c : GL (Fin 2) R ⧸ GL2Borel R, ¬ g • c = c := by
    refine QuotientGroup.mk_surjective.forall.2 fun y hy => ?_
    -- the stabilizer of the coset `yB` is the conjugate `yBy⁻¹`, so a fixed coset exhibits `y⁻¹gy`
    -- in `B`
    have hmem : g ∈ MulAut.conj y • GL2Borel R := by
      rw [← stabilizer_quotientGroup_mk]
      exact MulAction.mem_stabilizer_iff.2 hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply] at hmem
    exact h y⁻¹ hmem
  have : IsEmpty {c : GL (Fin 2) R ⧸ GL2Borel R // g • c = c} := ⟨fun c => hnone c.1 c.2⟩
  exact Nat.card_of_isEmpty

end CommRing

section OnePointModel

variable (F : Type u) [Field F] [DecidableEq F]

/-- **The Borel subgroup is the stabilizer of the point at infinity** for the Möbius action of
`GL₂(F)` on Mathlib's model `OnePoint F` of the projective line: the coset `B` is the line spanned
by the first basis vector. -/
theorem stabilizer_infty :
    MulAction.stabilizer (GL (Fin 2) F) (∞ : OnePoint F) = GL2Borel F :=
  Subgroup.ext fun _ =>
    MulAction.mem_stabilizer_iff.trans (OnePoint.smul_infty_eq_self_iff.trans mem_iff.symm)

/-- The matrix `!![t, 1; 1, 0]` carries `∞` to the affine point `t`. -/
private theorem upperRightHom_mul_gl2WeylElement_smul_infty (t : F) :
    (Matrix.GeneralLinearGroup.upperRightHom t * GL2WeylElement F) • (∞ : OnePoint F) =
      (t : OnePoint F) := by
  rw [OnePoint.smul_infty_eq_ite]
  simp [Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The cosets of the Borel subgroup are the points of the projective line**: translating the
point at infinity identifies `GL₂(F) ⧸ B` with Mathlib's model `OnePoint F`. It is a bijection
because `TauCeti.GL2Borel.stabilizer_infty` identifies the stabilizer of `∞` with `B`, and because
the action is transitive. -/
noncomputable def quotientEquivOnePoint : GL (Fin 2) F ⧸ GL2Borel F ≃ OnePoint F :=
  (Subgroup.quotientEquivOfEq (stabilizer_infty F).symm).trans <|
    Equiv.ofBijective (MulAction.ofQuotientStabilizer (GL (Fin 2) F) (∞ : OnePoint F))
      ⟨MulAction.injective_ofQuotientStabilizer _ _, fun x => by
        cases x with
        | infty => exact ⟨QuotientGroup.mk 1, one_smul _ _⟩
        | coe t =>
          exact ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.upperRightHom t * GL2WeylElement F),
            upperRightHom_mul_gl2WeylElement_smul_infty F t⟩⟩

/-- The point of the projective line attached to the coset of `g` is `g • ∞`, the line spanned by
the first column of `g`. -/
@[simp]
theorem quotientEquivOnePoint_mk (g : GL (Fin 2) F) :
    quotientEquivOnePoint F (QuotientGroup.mk g) = g • (∞ : OnePoint F) :=
  (rfl)

/-- **The identification is equivariant**, so it matches fixed cosets with fixed points. -/
@[simp]
theorem quotientEquivOnePoint_smul (g : GL (Fin 2) F) (c : GL (Fin 2) F ⧸ GL2Borel F) :
    quotientEquivOnePoint F (g • c) = g • quotientEquivOnePoint F c := by
  induction c using QuotientGroup.induction_on with
  | H y => rw [MulAction.Quotient.smul_mk, quotientEquivOnePoint_mk, quotientEquivOnePoint_mk,
      smul_eq_mul, mul_smul]

/-- The coset carried to `∞` is the Borel subgroup itself. -/
@[simp]
theorem quotientEquivOnePoint_symm_infty :
    (quotientEquivOnePoint F).symm ∞ = QuotientGroup.mk 1 := by
  rw [Equiv.symm_apply_eq, quotientEquivOnePoint_mk, one_smul]

/-- The coset carried to the affine point `t` is that of `!![t, 1; 1, 0]`, whose first column spans
the line through `(t, 1)`. -/
@[simp]
theorem quotientEquivOnePoint_symm_coe (t : F) :
    (quotientEquivOnePoint F).symm (t : OnePoint F) =
      QuotientGroup.mk (Matrix.GeneralLinearGroup.upperRightHom t * GL2WeylElement F) := by
  rw [Equiv.symm_apply_eq, quotientEquivOnePoint_mk,
    upperRightHom_mul_gl2WeylElement_smul_infty]

variable {F}

/-- **The fixed-coset count is a fixed-point count on the projective line**, by the equivariant
identification `TauCeti.GL2Borel.quotientEquivOnePoint`. -/
theorem natCard_fixedCosets_eq_ncard (g : GL (Fin 2) F) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // g • c = c} =
      {x : OnePoint F | g • x = x}.ncard :=
  Nat.card_congr <| (quotientEquivOnePoint F).subtypeEquiv fun c => by
    rw [Set.mem_ofPred_eq, ← quotientEquivOnePoint_smul]
    exact (Equiv.apply_eq_iff_eq _).symm

/-- The affine points fixed by an upper-triangular `!![a, b; 0, d]` are the roots of the linear
equation `(d - a) t = b`. This is Mathlib's
`Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff` with the quadratic term struck
out. -/
private theorem smul_coe_eq_self_iff_of_mem {g : GL (Fin 2) F} (hg : g ∈ GL2Borel F) (t : F) :
    g • (t : OnePoint F) = t ↔
      ((g : Matrix (Fin 2) (Fin 2) F) 1 1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0) * t =
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  rw [← Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff]
  simp [Matrix.GeneralLinearGroup.fixpointPolynomial, mem_iff.1 hg, sub_eq_zero]

end OnePointModel

section Field

variable {F : Type u} [Field F]

/-- **An upper-triangular element with distinct diagonal entries fixes exactly two cosets**: the
Borel subgroup itself, and the line spanned by the second eigenvector. -/
theorem natCard_fixedCosets_of_mem_of_diagonal_ne {g : GL (Fin 2) F} (hg : g ∈ GL2Borel F)
    (h : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (g : Matrix (Fin 2) (Fin 2) F) 1 1) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // g • c = c} = 2 := by
  classical
  have hne : (g : Matrix (Fin 2) (Fin 2) F) 1 1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
    sub_ne_zero.2 (Ne.symm h)
  have hset : {x : OnePoint F | g • x = x} =
      {∞, (((g : Matrix (Fin 2) (Fin 2) F) 0 1 /
        ((g : Matrix (Fin 2) (Fin 2) F) 1 1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0) : F) :
          OnePoint F)} := by
    ext x
    cases x with
    | infty => simp [OnePoint.smul_infty_eq_self_iff, mem_iff.1 hg]
    | coe t =>
      rw [Set.mem_ofPred_eq, smul_coe_eq_self_iff_of_mem hg]
      simp [eq_div_iff hne, mul_comm]
  rw [natCard_fixedCosets_eq_ncard, hset, Set.ncard_pair (by simp)]

/-- **An upper-triangular element with equal diagonal entries but a nonzero upper-right entry fixes
exactly one coset**: the Borel subgroup itself, the line of its single eigenvector. -/
theorem natCard_fixedCosets_of_mem_of_diagonal_eq_of_upperRight_ne_zero {g : GL (Fin 2) F}
    (hg : g ∈ GL2Borel F)
    (h : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1)
    (hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // g • c = c} = 1 := by
  classical
  have hset : {x : OnePoint F | g • x = x} = {∞} := by
    ext x
    cases x with
    | infty => simp [OnePoint.smul_infty_eq_self_iff, mem_iff.1 hg]
    | coe t =>
      rw [Set.mem_ofPred_eq, smul_coe_eq_self_iff_of_mem hg]
      simp [← h, Ne.symm hb]
  rw [natCard_fixedCosets_eq_ncard, hset, Set.ncard_singleton]

/-- **A diagonal matrix with distinct entries fixes exactly two cosets**, the two coordinate
axes. -/
@[simp]
theorem natCard_fixedCosets_diagGL {a b : Fˣ} (hab : a ≠ b) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // diagGL ![a, b] • c = c} = 2 :=
  natCard_fixedCosets_of_mem_of_diagonal_ne (mem_iff.2 (by simp))
    (by simpa using fun h => hab (Units.ext h))

/-- **A Jordan block fixes exactly one coset**, the line of its single eigenvector. -/
@[simp]
theorem natCard_fixedCosets_jordanGL (a : Fˣ) {b : F} (hb : b ≠ 0) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // jordanGL a b • c = c} = 1 :=
  natCard_fixedCosets_of_mem_of_diagonal_eq_of_upperRight_ne_zero (jordanGL_mem_gl2Borel a b)
    (by simp) (by simpa using hb)

section NonSplit

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **An element of the non-split torus outside `F` fixes no coset at all.** A fixed coset would
exhibit an upper-triangular conjugate, which is exactly what
`TauCeti.GL2NonSplitTorus.conj_notMem_gl2Borel` forbids. This is the elliptic case: no eigenvalue of
such a matrix lies in `F`, so it has no eigenline over `F`. -/
@[simp]
theorem natCard_fixedCosets_gl2NonSplitTorusHom {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // GL2NonSplitTorusHom F E hE x • c = c} = 0 :=
  natCard_fixedCosets_eq_zero (GL2NonSplitTorus.conj_notMem_gl2Borel hE hx)

end NonSplit

end Field

section FiniteField

variable {F : Type u} [Field F] [Fintype F]

/-- **A scalar matrix fixes every coset**, so it fixes all `q + 1` points of the projective line.

Unlike its three companions this is deliberately not a `simp` lemma: over a finite field the fixed
cosets form a `Fintype`, so `simp` rewrites the left-hand side by `Nat.card_eq_fintype_card` and it
is not in `simp`-normal form. -/
theorem natCard_fixedCosets_scalar (u : Fˣ) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F //
        Matrix.GeneralLinearGroup.scalar (Fin 2) u • c = c} = Fintype.card F + 1 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (scalar_smul_quotient_eq_self u)),
    ← Subgroup.index_eq_card, index_eq]

end FiniteField

end GL2Borel

end TauCeti
