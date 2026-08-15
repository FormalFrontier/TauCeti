/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Subgroup.centralizer` occurs in the statements below, and
-- `TauCeti.mem_centralizer_singleton_iff_commute_val` reads membership in it on matrices.
public import TauCeti.Algebra.Group.Subgroup.Centralizer
-- `TauCeti.commute_fin_two_iff` is the engine of the centralizer computations below.
public import TauCeti.LinearAlgebra.Matrix.Commute
-- `ConjClasses.carrier` occurs in the statements below, `TauCeti.ConjClasses.ncard_carrier_mk`
-- is what turns a centralizer order into a class size, and
-- `TauCeti.ConjClasses.ncard_carrier_mk_of_mem_center` is what does it for a central element.
public import TauCeti.Algebra.Group.Conj
-- `TauCeti.diagGL` and `TauCeti.diagonalTorus` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal
-- `TauCeti.GL2NonSplitTorus` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- `TauCeti.jordanGL` and `TauCeti.GL2ScalarUnipotent` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- Non-public: the order of `GL (Fin 2) F` over a finite field is used only inside the counting
-- proofs, so downstream importers do not pay for it.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Centralizers of the regular elements of `GL₂`

A `2 × 2` matrix over a field is **regular** as soon as it is not scalar: it is then cyclic
(nonderogatory), and the matrices commuting with it are exactly the polynomials in it, the
two-dimensional algebra `F[M]`. That is `TauCeti.commute_fin_two_iff`, from
`TauCeti.LinearAlgebra.Matrix.Commute`, and it is what organizes this file.

Two consequences organize the conjugacy classes of `GL₂(F)`. First, the commutant of a non-scalar
matrix is commutative, so the centralizer of a non-central element of `GL₂(F)` is an **abelian**
subgroup (`TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar`). Second, when a regular
element generates a maximal commutative subalgebra of `Matrix (Fin 2) (Fin 2) F` — a split one,
`F × F`, or a quadratic field extension `E/F` — its centralizer is that subalgebra's unit group:

* the *split* case, an invertible diagonal matrix with distinct diagonal entries: its centralizer
  is the split torus `TauCeti.diagonalTorus F 2` of all invertible diagonal matrices
  (`TauCeti.centralizer_diagGL`), of order `(q - 1)²`, so its conjugacy class has `q (q + 1)`
  elements;
* the *non-split* case, an element of `TauCeti.GL2NonSplitTorus` — the unit group of a quadratic
  field extension `E/F` — that does not come from `F`: its centralizer is that whole group
  (`TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`), of order `q² - 1`, so its
  conjugacy class has `q (q - 1)` elements.

The split computation needs no commutant: a matrix commuting with a diagonal matrix of distinct
entries is diagonal (`TauCeti.isDiag_of_commute_diagonal`), and the torus is commutative. The same
is true of the non-semisimple case below, where two entry equations do the work. It is the
non-split case, and the abelianness of a general non-central centralizer, that consume
`TauCeti.commute_fin_two_iff`.

Over a finite field — more generally whenever `E/F` is separable — both elements are **regular
semisimple** and both centralizers are the **maximal torus** containing the element, split in the
first case and elliptic in the second. Those words are used only under that hypothesis: over an
imperfect field of characteristic two a purely inseparable quadratic extension `E/F` satisfies the
hypotheses of `TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`, and there multiplication
by an element of `E ∖ F` is not semisimple and `Eˣ` is not a torus; the general statement is proved
and read as a centralizer computation for a quadratic extension, with no semisimplicity claimed.
The counting results all assume `F` finite, where the torus language is unconditionally correct.

Both computations are stated for a normal form — a diagonal matrix, and an element of the non-split
torus in the basis `TauCeti.nonSplitTorusBasis` — rather than for an arbitrary regular semisimple
element. Every regular semisimple element of `GL₂(𝔽_q)` is conjugate to one of the two, but that
classification, and the transport of a centralizer along a conjugation, are not proved here.

The third regular family is also here. A **non-semisimple** element is a Jordan block
`TauCeti.jordanGL a b = !![a, b; 0, a]` with `b ≠ 0`; it is again regular
(`TauCeti.notMem_range_scalar_jordanGL`), and its centralizer is
the scalar-unipotent subgroup `TauCeti.GL2ScalarUnipotent F` of all `!![x, y; 0, x]`
(`TauCeti.centralizer_jordanGL`), of order `q (q - 1)`, so its conjugacy class has `q² - 1`
elements. That subgroup is the product `Z U` of the centre with the unipotent radical of the Borel
subgroup, so it is `Gₘ × Gₐ` and not a torus — which is precisely what distinguishes this family
from the two semisimple ones.

The fourth family, the **central** one, is the non-regular case this file's title excludes: a
scalar matrix is central in `GL n R` for any index type and any commutative semiring, so its
centralizer is everything and its class is a single point. The centralizer half is proved at that
generality in `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal`
(`TauCeti.centralizer_scalar`); the class size, `TauCeti.ncard_carrier_mk_scalar`, is here with the
other three.

Together the four families give the class sizes `1`, `q (q + 1)`, `q (q - 1)` and `q² - 1`. These
are the sizes of the individual classes, not the numbers of classes in each family: the
non-semisimple family, for instance, has one class for each of the `q - 1` possible eigenvalues.
That every element of `GL₂(𝔽_q)` is conjugate to one of the four normal forms, and with it any
enumeration of the classes themselves, is not proved here.

The class sizes are read off the centralizer orders by orbit-stabilizer
(`TauCeti.ConjClasses.ncard_carrier_mk`), together with `TauCeti.natCard_GL_fin_two`, which gives
`|GL₂(𝔽_q)| = (q - 1)² q (q + 1)`.

## Main results

* `TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar`: the centralizer of a non-central
  element of `GL (Fin 2) F` is abelian.
* `TauCeti.centralizer_diagGL`, `TauCeti.natCard_centralizer_diagGL`,
  `TauCeti.ncard_carrier_mk_diagGL`: the centralizer of an invertible diagonal matrix with
  distinct entries is the split torus, of order `(q - 1)²`, and its conjugacy class has `q (q + 1)`
  elements.
* `TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`,
  `TauCeti.GL2NonSplitTorus.natCard_centralizer_gl2NonSplitTorusHom`,
  `TauCeti.GL2NonSplitTorus.ncard_carrier_mk_gl2NonSplitTorusHom`: the centralizer of an element of
  the non-split torus not coming from `F` — an elliptic element, over a finite field — is that
  whole torus, of order `q² - 1`, and its conjugacy class has `q (q - 1)` elements.
* `TauCeti.centralizer_jordanGL`, `TauCeti.natCard_centralizer_jordanGL`,
  `TauCeti.ncard_carrier_mk_jordanGL`: the centralizer of a Jordan block `!![a, b; 0, a]` with
  `b ≠ 0` — a non-semisimple element — is the scalar-unipotent subgroup, of order `q (q - 1)`, and
  its conjugacy class has `q² - 1` elements.
* `TauCeti.ncard_carrier_mk_scalar`: the conjugacy class of a scalar matrix is a single point.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)".
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 5.2.
-/

public section

open Matrix

namespace TauCeti

section GeneralLinearGroup

variable {F : Type*} [Field F] {g : GL (Fin 2) F}

/-- A non-central element of `GL (Fin 2) F` is one whose matrix is not scalar; the matrices
commuting with it then form a commutative algebra, so its centralizer is an **abelian** subgroup.
This is the prerequisite for the centralizers computed below being tori: an abelian overgroup of
the torus can be no larger than it. -/
theorem isMulCommutative_centralizer_of_notMem_range_scalar
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) :
    IsMulCommutative ↥(Subgroup.centralizer {g}) :=
  ⟨⟨fun x y => Subtype.ext (Commute.units_val_iff.mp (commute_of_commute_fin_two hg
    (mem_centralizer_singleton_iff_commute_val.mp x.2)
    (mem_centralizer_singleton_iff_commute_val.mp y.2))).eq⟩⟩

end GeneralLinearGroup

section SplitTorus

/-- An invertible diagonal matrix with distinct diagonal entries is not scalar.  Like `diagGL`
itself, this needs only a semiring; specialized to a field it is what supplies the non-scalarity
hypothesis of `TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar`, which is stated over
a field. -/
theorem notMem_range_scalar_diagGL {k : Type*} [Semiring k] {t : Fin 2 → kˣ} (ht : t 0 ≠ t 1) :
    (diagGL t : Matrix (Fin 2) (Fin 2) k) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [mem_range_scalar_fin_two_iff]
  rintro ⟨-, -, h⟩
  exact ht (Units.ext (by simpa using h))

section CommSemiring

variable {k : Type*} [CommSemiring k] [IsCancelMulZero k] {t : Fin 2 → kˣ}

/-- **The centralizer of an invertible diagonal matrix with distinct entries.** Over a commutative
semiring in which every nonzero element cancels, such a matrix has, as its centralizer, exactly the
diagonal torus `TauCeti.diagonalTorus k 2` of all invertible diagonal matrices.

Both inclusions come from the diagonal API: a matrix commuting with a diagonal matrix of distinct
entries is diagonal (`TauCeti.isDiag_of_commute_diagonal`), and conversely the torus is
commutative, so it centralizes each of its own elements. Only the first of these needs anything of
`k`, and only that its two distinct diagonal entries be separated by cancellation, so neither
subtraction nor inverses are used; a field is needed just for the counting below.

Over a field — where `IsCancelMulZero` is automatic — this is **the centralizer of a split regular
semisimple element of `GL₂`**: a diagonal matrix with distinct entries is then regular semisimple,
`TauCeti.diagonalTorus k 2` is the split maximal torus, and the theorem says that the centralizer
of the element is the maximal torus containing it. -/
theorem centralizer_diagGL (ht : t 0 ≠ t 1) :
    Subgroup.centralizer {diagGL t} = diagonalTorus k 2 := by
  have hne : (t 0 : k) ≠ (t 1 : k) := fun h => ht (Units.ext h)
  have hinj : Function.Injective fun i => (t i : k) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine le_antisymm (fun h hh => mem_diagonalTorus_iff.mpr ?_) ?_
  · refine isDiag_of_commute_diagonal hinj ?_
    have hcomm := mem_centralizer_singleton_iff_commute_val.mp hh
    rwa [diagGL_coe] at hcomm
  · exact (Subgroup.le_centralizer (diagonalTorus k 2)).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩)))

end CommSemiring

variable {F : Type*} [Field F] {t : Fin 2 → Fˣ}

/-- **The order of the centralizer of a split regular semisimple element**: over a field with `q`
elements the split torus has `(q - 1)²` elements, one invertible scalar per diagonal entry.  No
finiteness is assumed: over an infinite field both sides vanish. -/
theorem natCard_centralizer_diagGL (ht : t 0 ≠ t 1) :
    Nat.card (Subgroup.centralizer {diagGL t}) = (Nat.card F - 1) ^ 2 := by
  rw [centralizer_diagGL ht, natCard_diagonalTorus]

end SplitTorus

section Counting

variable {F : Type*} [Field F] [Fintype F]

/-- Orbit-stabilizer arithmetic: a subgroup of known nonzero order in a group whose order it
divides in a known way has the complementary factor as its index. -/
private theorem index_eq_of_natCard_eq_mul {G : Type*} [Group G] {H : Subgroup G} {c d : ℕ}
    (hpos : 0 < c) (hH : Nat.card H = c) (hG : Nat.card G = c * d) : H.index = d := by
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc c * H.index = Nat.card H * H.index := by rw [hH]
    _ = Nat.card G := Subgroup.card_mul_index H
    _ = c * d := hG

/-- The factor the split class-size computation cancels by is positive: `(q - 1)² > 0` for a field
with `q > 1` elements. -/
private theorem card_sub_one_sq_pos : 0 < (Fintype.card F - 1) ^ 2 :=
  pow_pos (Nat.sub_pos_of_lt Fintype.one_lt_card) 2

/-- The factor the elliptic class-size computation cancels by is positive: `q² - 1 > 0` for a field
with `q > 1` elements. -/
private theorem card_sq_sub_one_pos : 0 < Fintype.card F ^ 2 - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero Fintype.one_lt_card)

/-- The factor the non-semisimple class-size computation cancels by is positive: `(q - 1) q > 0`
for a field with `q > 1` elements. -/
private theorem card_sub_one_mul_card_pos : 0 < (Fintype.card F - 1) * Fintype.card F :=
  Nat.mul_pos (Nat.sub_pos_of_lt Fintype.one_lt_card) Fintype.card_pos

/-- **The size of a split regular semisimple conjugacy class of `GL₂(𝔽_q)`**: it is
`q (q + 1) = [GL₂(𝔽_q) : T]` for the split torus `T`. -/
theorem ncard_carrier_mk_diagGL {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    (ConjClasses.mk (diagGL t)).carrier.ncard = Fintype.card F * (Fintype.card F + 1) := by
  rw [ConjClasses.ncard_carrier_mk]
  refine index_eq_of_natCard_eq_mul card_sub_one_sq_pos ?_ (natCard_GL_fin_two F)
  rw [natCard_centralizer_diagGL ht, Nat.card_eq_fintype_card]

end Counting

namespace GL2NonSplitTorus

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  (hE : Module.finrank F E = 2) {x : Eˣ}

/-- A scalar matrix over `F` is the image of the algebra map of the matrix algebra, so that the
commutant description of `TauCeti.commute_fin_two_iff` can be compared with `Algebra.leftMulMatrix`
through `AlgHom.commutes`. -/
private theorem scalar_eq_algebraMap (c : F) :
    Matrix.scalar (Fin 2) c = algebraMap F (Matrix (Fin 2) (Fin 2) F) c := by
  ext i j
  rw [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  simp

/-- An element of the non-split torus not coming from `F` is not a scalar matrix: multiplication by
`x` on `E` is multiplication by an element of `F` exactly when `x` lies in `F`. -/
theorem notMem_range_scalar_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) ∉
      Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨c, hc⟩
  refine hx ⟨c, Algebra.leftMulMatrix_injective (nonSplitTorusBasis F E hE) ?_⟩
  rw [(Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes c,
    ← coe_gl2NonSplitTorusHom hE, ← hc, scalar_eq_algebraMap]

/-- **The centralizer of an element of `GL₂` coming from a quadratic field extension.** An element
of `TauCeti.GL2NonSplitTorus F E hE`, the unit group of a quadratic extension `E/F` acting on `E`
by multiplication, that does not come from `F` has that whole group as its centralizer.

When `E/F` is separable — always so over a finite field — such an element is elliptic regular
semisimple and `TauCeti.GL2NonSplitTorus F E hE` is the maximal torus containing it. Together with
`TauCeti.centralizer_diagGL` this computes the centralizer of each of the two standard regular
semisimple normal forms of `GL₂`, split and elliptic; that every regular semisimple element is
conjugate to one of them, and that a centralizer transports along such a conjugation, are not
proved here. Separability is not needed below: for a purely inseparable `E/F` in characteristic
two the statement computes the centralizer of an element that is *not* semisimple, and `Eˣ` is then
not a torus. -/
theorem centralizer_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Subgroup.centralizer {GL2NonSplitTorusHom F E hE x} = GL2NonSplitTorus F E hE := by
  ext h
  rw [mem_centralizer_singleton_iff_commute_val, mem_iff]
  constructor
  · intro hcomm
    obtain ⟨a, b, hab⟩ :=
      (commute_fin_two_iff (notMem_range_scalar_gl2NonSplitTorusHom hE hx)).mp hcomm
    -- The commuting matrix is multiplication by `a + b x`, which is nonzero as it is invertible.
    have hmat : (h : Matrix (Fin 2) (Fin 2) F) = Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)
        (algebraMap F E a + b • (x : E)) := by
      rw [map_add, map_smul, (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes a,
        ← coe_gl2NonSplitTorusHom hE, ← scalar_eq_algebraMap]
      exact hab
    have hy0 : algebraMap F E a + b • (x : E) ≠ 0 := by
      intro h0
      refine (Matrix.GeneralLinearGroup.det h).isUnit.ne_zero ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, hmat, h0, map_zero]
      exact Matrix.det_zero
    exact ⟨Units.mk0 _ hy0, Units.ext (by rw [coe_gl2NonSplitTorusHom, Units.val_mk0, hmat])⟩
  · rintro ⟨z, rfl⟩
    exact Commute.units_val_iff.mpr ((Commute.all x z).map (GL2NonSplitTorusHom F E hE))

/-- **The order of the centralizer of an element of `GL₂` coming from a quadratic extension**: the
centralizer is `TauCeti.GL2NonSplitTorus F E hE`, a copy of `Eˣ`, so over a field with `q` elements
it has `q² - 1` elements.  As for `TauCeti.GL2NonSplitTorus.natCard_eq`, no finiteness is assumed:
over an infinite `F` both sides are `0`.  When `E/F` is separable — always so over a finite field —
this is the order of the elliptic maximal torus containing the element; nothing here needs that
hypothesis. -/
theorem natCard_centralizer_gl2NonSplitTorusHom (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Nat.card (Subgroup.centralizer {GL2NonSplitTorusHom F E hE x}) = Nat.card F ^ 2 - 1 := by
  rw [centralizer_gl2NonSplitTorusHom hE hx, natCard_eq]

/-- **The size of an elliptic conjugacy class of `GL₂(𝔽_q)`**: it is `q (q - 1) = [GL₂(𝔽_q) : T]`
for the non-split torus `T`. -/
theorem ncard_carrier_mk_gl2NonSplitTorusHom [Fintype F]
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    (ConjClasses.mk (GL2NonSplitTorusHom F E hE x)).carrier.ncard =
      Fintype.card F * (Fintype.card F - 1) := by
  rw [ConjClasses.ncard_carrier_mk]
  refine index_eq_of_natCard_eq_mul card_sq_sub_one_pos ?_
    (natCard_GL_fin_two_eq_sq_sub_one_mul F)
  rw [natCard_centralizer_gl2NonSplitTorusHom hE hx, Nat.card_eq_fintype_card]

end GL2NonSplitTorus

section NonSemisimple

section CommRing

variable {R : Type*} [CommRing R] [IsCancelMulZero R] {a : Rˣ} {b : R}

/-- **The centralizer of a Jordan block with nonzero off-diagonal entry.** Over a commutative ring
in which nonzero elements cancel, the centralizer of `TauCeti.jordanGL a b = !![a, b; 0, a]` with
`b ≠ 0` is the scalar-unipotent subgroup `TauCeti.GL2ScalarUnipotent R` of the matrices
`!![x, y; 0, x]`.

Like the split case this needs no commutant, and for the same reason: only the two entry equations
`b · g₁₀ = 0` and `b · (g₁₁ - g₀₀) = 0` of `M g = g M` are used, and cancellation by the nonzero
`b` is what solves them — no division, so a commutative ring in which nonzero elements cancel is
enough, and a field is asked for only by the counting below. That the diagonal entry so obtained is
a unit is read off the determinant `g₀₀²`. The reverse inclusion is the commutativity of
`TauCeti.GL2ScalarUnipotent R`.

Over a field this is the centralizer of a **non-semisimple** element, and unlike the split and
elliptic cases it is **not** a torus: it is the product `Z U` of the centre with the unipotent
radical of the Borel subgroup, `Gₘ × Gₐ` rather than `Gₘ × Gₘ`, which is exactly the failure of `M`
to be semisimple. As with the two semisimple normal forms, that every non-semisimple element of
`GL₂(𝔽_q)` is conjugate to a Jordan block, and that a centralizer transports along such a
conjugation, are not proved here. -/
theorem centralizer_jordanGL (hb : b ≠ 0) :
    Subgroup.centralizer {jordanGL a b} = GL2ScalarUnipotent R := by
  ext h
  rw [mem_centralizer_singleton_iff_commute_val, mem_gl2ScalarUnipotent_iff]
  constructor
  · intro hcomm
    have hmul := hcomm.eq
    rw [coe_jordanGL] at hmul
    -- The `(0, 0)` entry of `M g = g M` reads `b · g₁₀ = 0`, and the `(0, 1)` entry
    -- `b · g₁₁ = b · g₀₀`; cancelling `b` leaves `g` upper triangular with equal diagonal entries.
    have h10 : (h : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
      have e00 : (a : R) * (h : Matrix (Fin 2) (Fin 2) R) 0 0
          + b * (h : Matrix (Fin 2) (Fin 2) R) 1 0
          = (h : Matrix (Fin 2) (Fin 2) R) 0 0 * (a : R) := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ hmul 0 0
      exact (mul_eq_zero.mp (by linear_combination e00)).resolve_left hb
    have h11 : (h : Matrix (Fin 2) (Fin 2) R) 1 1 = (h : Matrix (Fin 2) (Fin 2) R) 0 0 := by
      have e01 : (a : R) * (h : Matrix (Fin 2) (Fin 2) R) 0 1
          + b * (h : Matrix (Fin 2) (Fin 2) R) 1 1
          = (h : Matrix (Fin 2) (Fin 2) R) 0 0 * b
            + (h : Matrix (Fin 2) (Fin 2) R) 0 1 * (a : R) := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ hmul 0 1
      exact sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination e01)).resolve_left hb)
    -- The determinant is then `g₀₀²`, so the repeated diagonal entry is a unit.
    have hu : IsUnit ((h : Matrix (Fin 2) (Fin 2) R) 0 0) := by
      refine isUnit_of_mul_isUnit_left (y := (h : Matrix (Fin 2) (Fin 2) R) 0 0) ?_
      have hdet : (h : Matrix (Fin 2) (Fin 2) R).det
          = (h : Matrix (Fin 2) (Fin 2) R) 0 0 * (h : Matrix (Fin 2) (Fin 2) R) 0 0 := by
        rw [Matrix.det_fin_two, h10, h11]
        ring
      rw [← hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact (Matrix.GeneralLinearGroup.det h).isUnit
    refine ⟨hu.unit, (h : Matrix (Fin 2) (Fin 2) R) 0 1, Units.ext ?_⟩
    rw [coe_jordanGL, IsUnit.unit_spec]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h11]
  · rintro ⟨x, y, rfl⟩
    -- Conversely both blocks lie in `Z U`, which is abelian, so they commute already there.
    exact Commute.units_val (setLike_mul_comm
      (jordanGL_mem_gl2ScalarUnipotent a b) (jordanGL_mem_gl2ScalarUnipotent x y))

end CommRing

variable {F : Type*} [Field F] {a : Fˣ} {b : F}

/-- **The order of the centralizer of a regular non-semisimple element of `GL₂`**: the centralizer
is `TauCeti.GL2ScalarUnipotent F`, a copy of `Fˣ × (F, +)`, so over a field with `q` elements it has
`(q - 1) q` elements. As in the two semisimple cases no finiteness is assumed: over an infinite
field both sides are `0`. -/
theorem natCard_centralizer_jordanGL (hb : b ≠ 0) :
    Nat.card (Subgroup.centralizer {jordanGL a b}) = (Nat.card F - 1) * Nat.card F := by
  rw [centralizer_jordanGL hb, natCard_gl2ScalarUnipotent]

/-- **The size of a non-semisimple conjugacy class of `GL₂(𝔽_q)`**: it is
`q² - 1 = [GL₂(𝔽_q) : Z U]`.

This is the last of the four class sizes: a central class has `1` element, a split semisimple class
`q (q + 1)`, an elliptic class `q (q - 1)`, and a non-semisimple class `q² - 1`. -/
theorem ncard_carrier_mk_jordanGL [Fintype F] (hb : b ≠ 0) :
    (ConjClasses.mk (jordanGL a b)).carrier.ncard = Fintype.card F ^ 2 - 1 := by
  rw [ConjClasses.ncard_carrier_mk]
  refine index_eq_of_natCard_eq_mul (card_sub_one_mul_card_pos (F := F)) ?_ ?_
  · rw [natCard_centralizer_jordanGL hb, Nat.card_eq_fintype_card]
  · rw [natCard_GL_fin_two_eq_sq_sub_one_mul]
    ring

end NonSemisimple

section Central

variable {k : Type*} [CommSemiring k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The size of a central conjugacy class**: the conjugacy class of a scalar matrix is a single
point. For `GL₂(𝔽_q)` these are the `q - 1` central classes, the first of the four families of
conjugacy classes gathered in this file; nothing here is special to `Fin 2` or to a field, so the
statement is made for an arbitrary finite index type over a commutative semiring.

The centralizer half of the statement, `TauCeti.centralizer_scalar`, is in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal` with the rest of the general-index
material; only the class size is here, so that the foundational diagonal module does not have to
import conjugacy theory for it. -/
theorem ncard_carrier_mk_scalar (u : kˣ) :
    (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar ι u)).carrier.ncard = 1 :=
  ConjClasses.ncard_carrier_mk_of_mem_center (scalar_mem_center u)

end Central

end TauCeti
