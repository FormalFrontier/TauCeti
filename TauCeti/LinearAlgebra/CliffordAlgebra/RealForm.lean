/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The real Clifford algebras `Cliff(p, q)` and the base entries of the Bott table

Over `ℂ` a nondegenerate quadratic form is determined by its rank, so there is one Clifford algebra
in each dimension. Over `ℝ` this fails: a nondegenerate real form is classified by its signature
`(p, q)`, and the resulting algebras `Cliff(p, q)` run through matrix algebras over `ℝ`, `ℂ` and
`ℍ` in a pattern periodic modulo `8`. This file introduces the family of forms that the pattern is
indexed by, and pins the four small entries that fix the indexing convention.

`TauCeti.realCliffordForm p q` is the diagonal form on `Fin (p + q) → ℝ` with `+1` in the first `p`
coordinates and `-1` in the last `q`, written as a `QuadraticMap.weightedSumSquares` against the
sign vector `TauCeti.realCliffordWeight p q`. It is nondegenerate
(`TauCeti.nondegenerate_realCliffordForm`), and its Clifford algebra has dimension `2 ^ (p + q)`
(`TauCeti.finrank_cliffordAlgebra_realCliffordForm`).

The sign convention — generators of the *first* `p` coordinates square to `+1` — is not universal:
sources that make the first generators square to `-1` index the periodicity table by
`(p - q) mod 8` where this one uses `(q - p) mod 8`. The convention is therefore fixed here by
four explicit small identifications, which are the content of the rest of the file:

* `Cliff(1,0) ≅ ℝ × ℝ` — `TauCeti.realCliffordOneZeroEquivProd`;
* `Cliff(0,1) ≅ ℂ` — `TauCeti.realCliffordZeroOneEquivComplex`;
* `Cliff(0,2) ≅ ℍ` — `TauCeti.realCliffordZeroTwoEquivQuaternion`;
* `Cliff(1,1) ≅ M₂(ℝ)` — `TauCeti.realCliffordOneOneEquivMatrix`.

The middle two are Mathlib's `CliffordAlgebraComplex.equiv` and `CliffordAlgebraQuaternion.equiv`
transported along an isometry, since the forms Mathlib uses there are exactly the `(0,1)` and
`(0,2)` signature forms in disguise. The outer two are built here from the universal property: a
single generator squaring to `+1` splits the algebra into two copies of `ℝ`, and a hyperbolic pair
generates the whole of `M₂(ℝ)`. In both cases the constructed algebra map is proved *surjective* by
exhibiting explicit preimages, and injectivity is then forced by the dimension count
`2 ^ (p + q)`, which is the general mechanism the complex structure theorem uses as well.

## Implementation notes

`Cliff(p, q)` is spelled `CliffordAlgebra (realCliffordForm p q)` throughout rather than being
given an abbreviation, so that every lemma about a general `CliffordAlgebra` applies to it without
unfolding.

The scaffolding of the four constructions — the two transporting isometries and the two hand-built
algebra maps together with their surjectivity and the resulting bijectivity — is `private`: the
public interface is the four `AlgEquiv`s and the lemmas computing them on a generator, which is all
a downstream file needs.

All four identifications are bundled `AlgEquiv`s rather than the `Nonempty` existence statements
the roadmap asks for, and each comes with a lemma computing it on a generator: it is the
equivalences and their values, not their bare existence, that the Bott-periodicity step
`Cliff(p+1, q+1) ≅ Cliff(p, q) ⊗ M₂(ℝ)` will consume.

## Main definitions

* `TauCeti.realCliffordWeight` and `TauCeti.realCliffordForm`: the signature `(p, q)` sign vector
  and the diagonal real quadratic form it weights.
* `TauCeti.realCliffordOneZeroEquivProd`, `TauCeti.realCliffordZeroOneEquivComplex`,
  `TauCeti.realCliffordZeroTwoEquivQuaternion`, `TauCeti.realCliffordOneOneEquivMatrix`: the four
  base entries of the Bott table, each with a `..._ι` lemma computing it on a generator.

## Main results

* `TauCeti.nondegenerate_realCliffordForm`: the signature forms are nondegenerate.
* `TauCeti.finrank_cliffordAlgebra_realCliffordForm`:
  `finrank ℝ (CliffordAlgebra (realCliffordForm p q)) = 2 ^ (p + q)`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 7, "The real forms `Cliff(p, q)`".
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter I, §4.
-/

public section

open Module QuadraticMap

open scoped Quaternion

namespace TauCeti

/-! ### The real quadratic form of a signature -/

/-- The sign vector of signature `(p, q)`: `+1` on the first `p` coordinates of `Fin (p + q)` and
`-1` on the last `q`. -/
def realCliffordWeight (p q : ℕ) (i : Fin (p + q)) : ℝ := if (i : ℕ) < p then 1 else -1

/-- The real quadratic form of signature `(p, q)`: the diagonal form
`x ↦ ∑ᵢ₌₀^{p-1} xᵢ² - ∑ᵢ₌ₚ^{p+q-1} xᵢ²` on `Fin (p + q) → ℝ`. Its Clifford algebra is the real
Clifford algebra `Cliff(p, q)`. -/
def realCliffordForm (p q : ℕ) : QuadraticForm ℝ (Fin (p + q) → ℝ) :=
  weightedSumSquares ℝ (realCliffordWeight p q)

@[simp]
theorem realCliffordWeight_of_lt {p q : ℕ} {i : Fin (p + q)} (hi : (i : ℕ) < p) :
    realCliffordWeight p q i = 1 :=
  if_pos hi

@[simp]
theorem realCliffordWeight_of_le {p q : ℕ} {i : Fin (p + q)} (hi : p ≤ (i : ℕ)) :
    realCliffordWeight p q i = -1 :=
  if_neg (not_lt.2 hi)

@[simp]
theorem realCliffordWeight_mul_self (p q : ℕ) (i : Fin (p + q)) :
    realCliffordWeight p q i * realCliffordWeight p q i = 1 := by
  unfold realCliffordWeight
  split <;> norm_num

@[simp]
theorem realCliffordWeight_ne_zero (p q : ℕ) (i : Fin (p + q)) :
    realCliffordWeight p q i ≠ 0 := by
  intro h
  simpa [h] using realCliffordWeight_mul_self p q i

@[simp]
theorem realCliffordForm_apply (p q : ℕ) (v : Fin (p + q) → ℝ) :
    realCliffordForm p q v = ∑ i, realCliffordWeight p q i * (v i * v i) := by
  simp [realCliffordForm]

/-- The signature forms are nondegenerate: the radical of a weighted sum of squares is spanned by
the coordinates with weight zero, and every signature weight is `±1`. -/
theorem nondegenerate_realCliffordForm (p q : ℕ) : (realCliffordForm p q).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, realCliffordForm,
    QuadraticForm.radical_weightedSumSquares, Submodule.eq_bot_iff]
  intro v hv
  funext j
  exact Pi.mem_spanSubset_iff.1 hv j (realCliffordWeight_ne_zero p q j)

/-- The real Clifford algebra of signature `(p, q)` has dimension `2 ^ (p + q)`, as every Clifford
algebra of a space of that dimension does. This is the count that forces the surjections built
below to be isomorphisms. -/
@[simp]
theorem finrank_cliffordAlgebra_realCliffordForm (p q : ℕ) :
    finrank ℝ (CliffordAlgebra (realCliffordForm p q)) = 2 ^ (p + q) := by
  rw [TauCeti.CliffordAlgebra.finrank_eq_two_pow, Module.finrank_pi, Fintype.card_fin]

/-! ### The four base entries, in coordinates -/

@[simp]
theorem realCliffordForm_one_zero_apply (v : Fin (1 + 0) → ℝ) :
    realCliffordForm 1 0 v = v 0 * v 0 := by
  rw [realCliffordForm_apply]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_zero_one_apply (v : Fin (0 + 1) → ℝ) :
    realCliffordForm 0 1 v = -(v 0 * v 0) := by
  rw [realCliffordForm_apply]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_zero_two_apply (v : Fin (0 + 2) → ℝ) :
    realCliffordForm 0 2 v = -(v 0 * v 0) + -(v 1 * v 1) := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  simp [realCliffordWeight]

@[simp]
theorem realCliffordForm_one_one_apply (v : Fin (1 + 1) → ℝ) :
    realCliffordForm 1 1 v = v 0 * v 0 - v 1 * v 1 := by
  rw [realCliffordForm_apply, Fin.sum_univ_two]
  simp [realCliffordWeight]
  ring

/-! ### `Cliff(1,0) ≅ ℝ × ℝ` -/

/-- The algebra map `Cliff(1,0) → ℝ × ℝ` sending the generator `e` to `(1, -1)`. This is legitimate
because `(1, -1)` squares to `1 = Q e`, and it is the pair of the two characters `e ↦ 1` and
`e ↦ -1` of `ℝ[e]/(e² - 1)`. -/
private def realCliffordOneZeroToProd :
    CliffordAlgebra (realCliffordForm 1 0) →ₐ[ℝ] ℝ × ℝ :=
  CliffordAlgebra.lift _
    ⟨(LinearMap.proj 0).prod (-LinearMap.proj 0), fun v => by
      ext <;> simp [realCliffordForm_one_zero_apply]⟩

/-- The value of `realCliffordOneZeroToProd` on a generator. -/
private theorem realCliffordOneZeroToProd_ι (v : Fin (1 + 0) → ℝ) :
    realCliffordOneZeroToProd (CliffordAlgebra.ι _ v) = (v 0, -v 0) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- `realCliffordOneZeroToProd` is surjective: the two characters of `ℝ[e]/(e² - 1)` separate
`(1, 0)` and `(0, 1)`, so every pair is hit by an explicit combination of `1` and the generator.
With the dimension count `finrank_cliffordAlgebra_realCliffordForm` this makes it bijective. -/
private theorem realCliffordOneZeroToProd_surjective :
    Function.Surjective realCliffordOneZeroToProd := by
  rintro ⟨a, b⟩
  refine ⟨algebraMap ℝ _ ((a + b) / 2)
      + ((a - b) / 2) • CliffordAlgebra.ι (realCliffordForm 1 0) (Pi.single 0 1), ?_⟩
  ext <;> simp [realCliffordOneZeroToProd_ι] <;> ring

/-- `realCliffordOneZeroToProd` is bijective: it is surjective, and both sides have dimension `2`,
so surjectivity forces injectivity. -/
private theorem realCliffordOneZeroToProd_bijective :
    Function.Bijective realCliffordOneZeroToProd := by
  have hrank : finrank ℝ (CliffordAlgebra (realCliffordForm 1 0)) = finrank ℝ (ℝ × ℝ) := by
    rw [finrank_cliffordAlgebra_realCliffordForm, Module.finrank_prod, Module.finrank_self]
    norm_num
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := realCliffordOneZeroToProd.toLinearMap) hrank).2
    realCliffordOneZeroToProd_surjective, realCliffordOneZeroToProd_surjective⟩

/-- **`Cliff(1,0) ≅ ℝ × ℝ`**, the first base entry of the real periodicity table: a single
generator squaring to `+1` splits the algebra. -/
noncomputable def realCliffordOneZeroEquivProd :
    CliffordAlgebra (realCliffordForm 1 0) ≃ₐ[ℝ] ℝ × ℝ :=
  AlgEquiv.ofBijective realCliffordOneZeroToProd realCliffordOneZeroToProd_bijective

/-- `realCliffordOneZeroEquivProd` sends the generator of the coordinate `v` to the pair
`(v 0, -v 0)`: the two characters of `ℝ[e]/(e² - 1)` read off the two components. -/
@[simp]
theorem realCliffordOneZeroEquivProd_ι (v : Fin (1 + 0) → ℝ) :
    realCliffordOneZeroEquivProd (CliffordAlgebra.ι _ v) = (v 0, -v 0) := by
  rw [realCliffordOneZeroEquivProd, AlgEquiv.ofBijective_apply, realCliffordOneZeroToProd_ι]

/-! ### `Cliff(0,1) ≅ ℂ` -/

/-- The signature `(0,1)` form is Mathlib's `CliffordAlgebraComplex.Q`, `r ↦ -r²`, read on the
one-dimensional space `Fin (0 + 1) → ℝ`. -/
private def realCliffordZeroOneIsometry :
    (realCliffordForm 0 1).IsometryEquiv CliffordAlgebraComplex.Q :=
  ⟨(LinearEquiv.funUnique (Fin 1) ℝ ℝ : (Fin (0 + 1) → ℝ) ≃ₗ[ℝ] ℝ), fun v => by
    simp [realCliffordForm_zero_one_apply]⟩

/-- `realCliffordZeroOneIsometry` reads off the single coordinate. -/
private theorem realCliffordZeroOneIsometry_apply (v : Fin (0 + 1) → ℝ) :
    realCliffordZeroOneIsometry v = v 0 := by
  simp [realCliffordZeroOneIsometry, ← IsometryEquiv.coe_toLinearEquiv,
    LinearEquiv.funUnique_apply]

/-- **`Cliff(0,1) ≅ ℂ`**, the second base entry of the real periodicity table: a single generator
squaring to `-1` is a square root of `-1`. -/
noncomputable def realCliffordZeroOneEquivComplex :
    CliffordAlgebra (realCliffordForm 0 1) ≃ₐ[ℝ] ℂ :=
  (CliffordAlgebra.equivOfIsometry realCliffordZeroOneIsometry).trans
    CliffordAlgebraComplex.equiv

/-- `realCliffordZeroOneEquivComplex` unfolded into the two equivalences it composes. -/
private theorem realCliffordZeroOneEquivComplex_eq (x : CliffordAlgebra (realCliffordForm 0 1)) :
    realCliffordZeroOneEquivComplex x =
      CliffordAlgebraComplex.equiv
        (CliffordAlgebra.equivOfIsometry realCliffordZeroOneIsometry x) := rfl

/-- `realCliffordZeroOneEquivComplex` sends the generator of the coordinate `v` to the purely
imaginary complex number `v 0 • Complex.I`. -/
@[simp]
theorem realCliffordZeroOneEquivComplex_ι (v : Fin (0 + 1) → ℝ) :
    realCliffordZeroOneEquivComplex (CliffordAlgebra.ι _ v) = v 0 • Complex.I := by
  rw [realCliffordZeroOneEquivComplex_eq, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  simp only [IsometryEquiv.toIsometry_apply, realCliffordZeroOneIsometry_apply,
    CliffordAlgebraComplex.equiv_apply, CliffordAlgebraComplex.toComplex_ι, Complex.real_smul]

/-! ### `Cliff(0,2) ≅ ℍ` -/

/-- The signature `(0,2)` form is Mathlib's `CliffordAlgebraQuaternion.Q (-1) (-1)` read on
`Fin (0 + 2) → ℝ` instead of on `ℝ × ℝ`. -/
private def realCliffordZeroTwoIsometry :
    (realCliffordForm 0 2).IsometryEquiv (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1)) :=
  ⟨(LinearEquiv.finTwoArrow ℝ ℝ : (Fin (0 + 2) → ℝ) ≃ₗ[ℝ] ℝ × ℝ), fun v => by
    simp [realCliffordForm_zero_two_apply]⟩

/-- `realCliffordZeroTwoIsometry` reads off the two coordinates. -/
private theorem realCliffordZeroTwoIsometry_apply (v : Fin (0 + 2) → ℝ) :
    realCliffordZeroTwoIsometry v = (v 0, v 1) := by
  simp [realCliffordZeroTwoIsometry, ← IsometryEquiv.coe_toLinearEquiv,
    LinearEquiv.finTwoArrow_apply]

/-- **`Cliff(0,2) ≅ ℍ`**, the third base entry of the real periodicity table: two anticommuting
generators squaring to `-1` are the quaternion units `i` and `j`. -/
noncomputable def realCliffordZeroTwoEquivQuaternion :
    CliffordAlgebra (realCliffordForm 0 2) ≃ₐ[ℝ] ℍ[ℝ] :=
  (CliffordAlgebra.equivOfIsometry realCliffordZeroTwoIsometry).trans
    CliffordAlgebraQuaternion.equiv

/-- `realCliffordZeroTwoEquivQuaternion` unfolded into the two equivalences it composes. Stating
this separately is what lets the generator lemma below be proved by rewriting: the codomain of
`CliffordAlgebraQuaternion.equiv` is `ℍ[ℝ,-1,-1]` rather than the `ℍ[ℝ]` of the statement, so
`rw [AlgEquiv.trans_apply]` cannot see the composite. -/
private theorem realCliffordZeroTwoEquivQuaternion_eq
    (x : CliffordAlgebra (realCliffordForm 0 2)) :
    realCliffordZeroTwoEquivQuaternion x =
      CliffordAlgebraQuaternion.equiv
        (CliffordAlgebra.equivOfIsometry realCliffordZeroTwoIsometry x) := rfl

/-- `realCliffordZeroTwoEquivQuaternion` sends the generator of the coordinate `v` to the imaginary
quaternion `v 0 * i + v 1 * j`. -/
@[simp]
theorem realCliffordZeroTwoEquivQuaternion_ι (v : Fin (0 + 2) → ℝ) :
    realCliffordZeroTwoEquivQuaternion (CliffordAlgebra.ι _ v) = ⟨0, v 0, v 1, 0⟩ := by
  rw [realCliffordZeroTwoEquivQuaternion_eq, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  simp only [IsometryEquiv.toIsometry_apply, CliffordAlgebraQuaternion.equiv_apply,
    CliffordAlgebraQuaternion.toQuaternion_ι, realCliffordZeroTwoIsometry_apply]
  -- Both sides are now the same quadruple; they differ only in the instance path of the two zero
  -- components, `CliffordAlgebraQuaternion.toQuaternion` producing them in `ℍ[ℝ,-1,-1]` and the
  -- statement reading them in `ℍ[ℝ]`, so the components match on the nose.
  ext <;> rfl

/-! ### `Cliff(1,1) ≅ M₂(ℝ)` -/

/-- The algebra map `Cliff(1,1) → M₂(ℝ)` sending the `+1` generator to the diagonal involution
`!![1, 0; 0, -1]` and the `-1` generator to the rotation `!![0, 1; -1, 0]`. The two matrices
anticommute, so the map is well defined by the universal property. -/
private def realCliffordOneOneToMatrix :
    CliffordAlgebra (realCliffordForm 1 1) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift _
    ⟨(LinearMap.proj 0).smulRight !![1, 0; 0, -1] +
        (LinearMap.proj 1).smulRight !![0, 1; -1, 0], fun v => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [realCliffordForm_one_one_apply, Matrix.mul_apply, Fin.sum_univ_two,
          Algebra.algebraMap_eq_smul_one] <;> ring⟩

/-- The value of `realCliffordOneOneToMatrix` on a generator. -/
private theorem realCliffordOneOneToMatrix_ι (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneToMatrix (CliffordAlgebra.ι _ v) = !![v 0, v 1; -v 1, -v 0] := by
  rw [realCliffordOneOneToMatrix, CliffordAlgebra.lift_ι_apply]
  simp [Matrix.smul_of]

/-- `realCliffordOneOneToMatrix` is surjective: the images of `1`, the two generators and their
product are the four matrix units up to an invertible change of basis, so every matrix has an
explicit preimage. With the dimension count `finrank_cliffordAlgebra_realCliffordForm` this makes
it bijective. -/
private theorem realCliffordOneOneToMatrix_surjective :
    Function.Surjective realCliffordOneOneToMatrix := by
  intro m
  refine ⟨algebraMap ℝ _ ((m 0 0 + m 1 1) / 2)
      + ((m 0 0 - m 1 1) / 2) • CliffordAlgebra.ι (realCliffordForm 1 1) (Pi.single 0 1)
      + ((m 0 1 - m 1 0) / 2) • CliffordAlgebra.ι (realCliffordForm 1 1) (Pi.single 1 1)
      + ((m 0 1 + m 1 0) / 2) •
        (CliffordAlgebra.ι (realCliffordForm 1 1) (Pi.single 0 1) *
          CliffordAlgebra.ι (realCliffordForm 1 1) (Pi.single 1 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realCliffordOneOneToMatrix_ι, Algebra.algebraMap_eq_smul_one] <;> ring

/-- `realCliffordOneOneToMatrix` is bijective: it is surjective, and both sides have dimension `4`,
so surjectivity forces injectivity. -/
private theorem realCliffordOneOneToMatrix_bijective :
    Function.Bijective realCliffordOneOneToMatrix := by
  have hrank : finrank ℝ (CliffordAlgebra (realCliffordForm 1 1)) =
      finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [finrank_cliffordAlgebra_realCliffordForm, Module.finrank_matrix]
    simp
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := realCliffordOneOneToMatrix.toLinearMap) hrank).2
    realCliffordOneOneToMatrix_surjective, realCliffordOneOneToMatrix_surjective⟩

/-- **`Cliff(1,1) ≅ M₂(ℝ)`**, the fourth base entry of the real periodicity table and the seed of
the periodicity step `Cliff(p+1, q+1) ≅ Cliff(p, q) ⊗ M₂(ℝ)`. -/
noncomputable def realCliffordOneOneEquivMatrix :
    CliffordAlgebra (realCliffordForm 1 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  AlgEquiv.ofBijective realCliffordOneOneToMatrix realCliffordOneOneToMatrix_bijective

/-- `realCliffordOneOneEquivMatrix` sends the generator of the coordinate `v` to
`!![v 0, v 1; -v 1, -v 0]`, the combination `v 0 • !![1, 0; 0, -1] + v 1 • !![0, 1; -1, 0]` of the
images of the `+1` and `-1` generators. -/
@[simp]
theorem realCliffordOneOneEquivMatrix_ι (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneEquivMatrix (CliffordAlgebra.ι _ v) = !![v 0, v 1; -v 1, -v 0] := by
  rw [realCliffordOneOneEquivMatrix, AlgEquiv.ofBijective_apply, realCliffordOneOneToMatrix_ι]

end TauCeti
