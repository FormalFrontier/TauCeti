/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.GeneralLinearGroup.upperRightHom` and `Matrix.GeneralLinearGroup.scalar` occur in the
-- statements below, and this module re-exports `GeneralLinearGroup.Defs`, which supplies the `GL`
-- notation, the coercion of an element of `GL n R` to a function on indices, and
-- `Matrix.GeneralLinearGroup.det`.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
-- `Subgroup.index` occurs in the statements below.
public import Mathlib.GroupTheory.Index
-- `Matrix.BlockTriangular` occurs in the statement of `TauCeti.blockTriangular_id_iff`.
public import Mathlib.LinearAlgebra.Matrix.Block
-- The general upper-triangular group specializes to `TauCeti.GL2Borel` below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
-- Non-public: the order of `GL₂` over a finite field, and the number of units of a finite field,
-- are used only inside the counting proofs, so downstream importers do not pay for them.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The Borel subgroup of `GL₂`

The **Borel subgroup** `B` of `GL₂` is the `Fin 2` specialization of
`TauCeti.upperTriangularGroup`, the subgroup of invertible upper-triangular matrices. It is the
standard minimal parabolic: over a finite field it is the subgroup from which the principal
series `Ind_B^{GL₂}(α ⊗ β)` is induced, and its index `q + 1` is the dimension of that induced
representation.

Everything except the two counting results is proved over an arbitrary commutative ring, where the
subgroup already makes sense: upper-triangular matrices are closed under multiplication, and the
inverse of an invertible one is again upper triangular by
`Matrix.blockTriangular_inv_of_blockTriangular`. The constructor `TauCeti.GL2Borel.mk`, which does
not mention the subgroup, needs only a ring. Two facts organize the subgroup:

* the two diagonal entries of an element of `B` are units, and reading them off is a **group
  homomorphism** `TauCeti.GL2Borel.diag : B →* Rˣ × Rˣ`, the diagonal projection; it is split by
  the **split torus** `T`, the diagonal matrices `TauCeti.GL2Borel.torusHom : Rˣ × Rˣ →* B`, which
  is a section of it, and it is by composing with `TauCeti.GL2Borel.diag` that a pair of characters
  `α, β` of `Rˣ` inflates to a character of `B`;
* the kernel of the diagonal projection is the **unipotent radical** `U`, the image of
  `TauCeti.GL2Borel.unipotentHom`, and every element of `B` factors as a torus element times a
  unipotent one (`TauCeti.GL2Borel.eq_torusHom_mul_unipotentHom`) — the decomposition `B = T U`.
  Coordinatewise this is the bijection `B ≃ (Rˣ × Rˣ) × R` (`TauCeti.GL2Borel.equivProd`), the
  upper-right entry being the free coordinate.

Over a finite field with `q` elements these give `|B| = q (q - 1)²` and hence `[GL₂(𝔽_q) : B] =
q + 1`, the number of points of the projective line.

## Main definitions

* `TauCeti.GL2Borel R`: the upper-triangular subgroup of `GL (Fin 2) R`.
* `TauCeti.GL2Borel.mk`: the element of `GL (Fin 2) R` with prescribed diagonal units and
  upper-right entry; it lies in `TauCeti.GL2Borel R`.
* `TauCeti.GL2Borel.diag`: the two diagonal entries of an element of the Borel subgroup, as a
  homomorphism to `Rˣ × Rˣ`, and `TauCeti.GL2Borel.torusHom`, the split torus, its homomorphic
  section.
* `TauCeti.GL2Borel.unipotentHom`: the unipotent radical, `Matrix.GeneralLinearGroup.upperRightHom`
  seen as an additive character valued in the Borel subgroup.
* `TauCeti.GL2Borel.equivProd`: the bijection `B ≃ (Rˣ × Rˣ) × R`.

## Main results

* `TauCeti.GL2Borel.mem_iff_exists_mk`: an element of `GL₂` is upper triangular exactly when it is
  `!![a, b; 0, d]` for units `a`, `d`.
* `TauCeti.GL2Borel.mem_ker_diag_iff`: the kernel of `TauCeti.GL2Borel.diag` is the unipotent
  radical, the image of `TauCeti.GL2Borel.unipotentHom`.
* `TauCeti.GL2Borel.eq_torusHom_mul_unipotentHom`: the decomposition `B = T U`.
* `TauCeti.GL2Borel.det_diag`: the determinant of an element of `B` is the product of its two
  diagonal entries.
* `TauCeti.GL2Borel.exists_det_sub_algebraMap_eq_zero`: a matrix with an upper-triangular conjugate
  has an eigenvalue in the base ring.
* `TauCeti.GL2Borel.card_eq`: `|B| = q (q - 1)²` over a finite field with `q` elements.
* `TauCeti.GL2Borel.index_eq`: `[GL₂(𝔽_q) : B] = q + 1`.

## Implementation notes

The name follows the `GL2` prefix that
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` uses for this family of objects
(`GL2Borel`, `GL2PrincipalSeries`, `GL2Steinberg`, `GL2NonSplitTorus`), rather than being placed in
the `Matrix.GeneralLinearGroup` namespace; the statements are the roadmap's, with `[Field F]
[Fintype F]` weakened to `[CommRing R]` wherever the result does not count.

The subgroup is the `Fin 2` specialization of `TauCeti.upperTriangularGroup`. Its public membership
lemma is nevertheless stated as the concrete condition `g 1 0 = 0`, because that is what the
coordinate proofs below use; `TauCeti.blockTriangular_id_iff` identifies this condition with the
general upper-triangular predicate.

## References

This supplies the Borel subgroup of Layer 9 ("the representation theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`, whose `GL2Borel` is the subgroup
defined here, together with the index `q + 1` that its principal-series dimension count needs. See
also W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

namespace TauCeti

open Matrix

universe u

/-- In size `2`, block triangularity for `id : Fin 2 → Fin 2` is the single vanishing condition on
the lower-left entry. -/
theorem blockTriangular_id_iff {R : Type u} [Zero R] {M : Matrix (Fin 2) (Fin 2) R} :
    M.BlockTriangular id ↔ M 1 0 = 0 := by
  refine ⟨fun h => h (by decide), fun h i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

namespace GL2Borel

section Ring

variable {R : Type u} [Ring R]

/-- The invertible upper-triangular matrix `!![a, b; 0, d]` with prescribed diagonal units `a`, `d`
and prescribed upper-right entry `b`. -/
def mk (a d : Rˣ) (b : R) : GL (Fin 2) R where
  val := !![(a : R), b; 0, (d : R)]
  -- The inverse is written out, so no invertibility side condition is discharged twice.
  inv := !![((a⁻¹ : Rˣ) : R), -((a⁻¹ : Rˣ) * b * (d⁻¹ : Rˣ)); 0, ((d⁻¹ : Rˣ) : R)]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    simp [mul_assoc]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    simp [mul_assoc]

@[simp]
theorem coe_mk (a d : Rˣ) (b : R) :
    ((mk a d b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), b; 0, (d : R)] :=
  (rfl)

end Ring

end GL2Borel

section CommRing

variable (R : Type u) [CommRing R]

/-- The **Borel subgroup** of `GL₂`, obtained by specializing the general upper-triangular
subgroup to `Fin 2`. -/
abbrev GL2Borel : Subgroup (GL (Fin 2) R) := upperTriangularGroup (Fin 2) R

namespace GL2Borel

variable {R}

@[simp]
theorem mem_iff {g : GL (Fin 2) R} :
    g ∈ GL2Borel R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  UpperTriangularGroup.mem_iff.trans blockTriangular_id_iff

/-- The lower-left entry of an element of the Borel subgroup vanishes. -/
@[simp]
theorem apply_one_zero (g : GL2Borel R) :
    ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  mem_iff.mp g.2

/-- The `(0, 0)` entry is multiplicative on the Borel subgroup: only the lower-left entry of the
*right* factor is needed. -/
theorem mul_apply_zero_zero {g h : GL (Fin 2) R} (hh : h ∈ GL2Borel R) :
    ((g * h : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0
      = (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (h : Matrix (Fin 2) (Fin 2) R) 0 0 := by
  rw [mem_iff] at hh
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]
  ring

/-- The `(1, 1)` entry is multiplicative on the Borel subgroup: only the lower-left entry of the
*left* factor is needed. -/
theorem mul_apply_one_one {g h : GL (Fin 2) R} (hg : g ∈ GL2Borel R) :
    ((g * h : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1
      = (g : Matrix (Fin 2) (Fin 2) R) 1 1 * (h : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  rw [mem_iff] at hg
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg]
  ring

variable (R)

/-- The unipotent radical sits inside the Borel subgroup: `Matrix.GeneralLinearGroup.upperRightHom`
sends `b` to `!![1, b; 0, 1]`. -/
theorem upperRightHom_mem (b : R) :
    Matrix.GeneralLinearGroup.upperRightHom b ∈ GL2Borel R := by
  apply mem_iff.mpr
  simp [Matrix.GeneralLinearGroup.upperRightHom]

/-- The scalar matrices sit inside the Borel subgroup. -/
theorem scalar_mem (u : Rˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ GL2Borel R := by
  apply mem_iff.mpr
  simp [Matrix.scalar_apply]

variable {R}

theorem mk_mem (a d : Rˣ) (b : R) : mk a d b ∈ GL2Borel R := by
  apply mem_iff.mpr
  simp

/-- The **diagonal projection**: the general diagonal projection specialized to `Fin 2`, with its
two coordinates packaged as a pair of units. -/
def diag : GL2Borel R →* Rˣ × Rˣ :=
  (MonoidHom.mk' (fun t : Fin 2 → Rˣ ↦ (t 0, t 1)) fun _ _ ↦ rfl).comp
    (UpperTriangularGroup.diag (m := Fin 2) (R := R))

@[simp]
theorem diag_fst_val (g : GL2Borel R) :
    (((diag g).1 : Rˣ) : R) = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 :=
  UpperTriangularGroup.diag_apply_val g 0

@[simp]
theorem diag_snd_val (g : GL2Borel R) :
    (((diag g).2 : Rˣ) : R) = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 :=
  UpperTriangularGroup.diag_apply_val g 1

@[simp]
theorem diag_mk (a d : Rˣ) (b : R) : diag ⟨mk a d b, mk_mem a d b⟩ = (a, d) := by
  ext <;> simp

/-- The determinant of an element of the Borel subgroup is the product of the two torus
coordinates. -/
@[simp]
theorem det_diag (g : GL2Borel R) :
    Matrix.GeneralLinearGroup.det (g : GL (Fin 2) R) = (diag g).1 * (diag g).2 := by
  ext
  rw [Units.val_mul, diag_fst_val, diag_snd_val, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_of_isUpperTriangular (blockTriangular_id_iff.mpr (apply_one_zero g)),
    Fin.prod_univ_two]

/-- The **split torus** `T`, as a homomorphic section of `TauCeti.GL2Borel.diag`: the diagonal
matrix `!![a, 0; 0, d]`. Its existence is what upgrades the bijection
`TauCeti.GL2Borel.equivProd` to a genuine splitting `B = T U`. -/
def torusHom : Rˣ × Rˣ →* GL2Borel R :=
  (UpperTriangularGroup.diagonalHom (m := Fin 2) (R := R)).comp <|
    MonoidHom.mk' (fun p : Rˣ × Rˣ ↦ ![p.1, p.2]) fun _ _ ↦ by
      funext i
      fin_cases i <;> rfl

@[simp]
theorem coe_torusHom (p : Rˣ × Rˣ) :
    ((torusHom p : GL2Borel R) : GL (Fin 2) R) = mk p.1 p.2 0 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [torusHom, MonoidHom.comp_apply]
  rw [UpperTriangularGroup.coe_diagonalHom, coe_mk]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem diag_torusHom (p : Rˣ × Rˣ) : diag (torusHom p) = p := by
  ext <;> simp

/-- The **unipotent radical** `U`, as an additive character valued in the Borel subgroup: `b` is
sent to `!![1, b; 0, 1]`. It is `Matrix.GeneralLinearGroup.upperRightHom` with its codomain
restricted to `B`. -/
def unipotentHom : AddChar R (GL2Borel R) where
  toFun b := ⟨Matrix.GeneralLinearGroup.upperRightHom b, upperRightHom_mem R b⟩
  map_zero_eq_one' := Subtype.ext (Matrix.GeneralLinearGroup.upperRightHom.map_zero_eq_one)
  map_add_eq_mul' a b :=
    Subtype.ext (Matrix.GeneralLinearGroup.upperRightHom.map_add_eq_mul a b)

@[simp]
theorem coe_unipotentHom (b : R) :
    ((unipotentHom b : GL2Borel R) : GL (Fin 2) R) = Matrix.GeneralLinearGroup.upperRightHom b :=
  (rfl)

/-- The unipotent radical is diagonally trivial: both diagonal entries of `!![1, b; 0, 1]`
are `1`. -/
@[simp]
theorem diag_unipotentHom (b : R) : diag (unipotentHom b) = 1 := by
  ext <;> simp [Matrix.GeneralLinearGroup.upperRightHom]

/-- The kernel of the diagonal projection is the **unipotent radical**: the elements of the Borel
subgroup with both diagonal entries `1`, that is, the image of
`TauCeti.GL2Borel.unipotentHom`. -/
theorem mem_ker_diag_iff (g : GL2Borel R) :
    g ∈ (diag (R := R)).ker ↔ ∃ b : R, g = unipotentHom b := by
  constructor
  · intro hg
    refine ⟨((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩
    have h₀ : ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := by
      have := congrArg (fun p : Rˣ × Rˣ => ((p.1 : Rˣ) : R)) (MonoidHom.mem_ker.mp hg)
      simpa using this
    have h₁ : ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
      have := congrArg (fun p : Rˣ × Rˣ => ((p.2 : Rˣ) : R)) (MonoidHom.mem_ker.mp hg)
      simpa using this
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom, h₀, h₁, apply_one_zero g]
  · rintro ⟨b, rfl⟩
    exact MonoidHom.mem_ker.mpr (diag_unipotentHom b)

/-- **The Borel subgroup is `T U`**: every element of `B` is the diagonal matrix carrying its two
torus coordinates times the unipotent matrix carrying the remaining upper-right coordinate. -/
theorem eq_torusHom_mul_unipotentHom (g : GL2Borel R) :
    g = torusHom (diag g) *
      unipotentHom ((((diag g).1⁻¹ : Rˣ) : R) *
        ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1) := by
  -- The upper-right entry is the only one that needs the torus coordinate cancelled off.
  have h : ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 *
      ((((diag g).1⁻¹ : Rˣ) : R) * ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1)
      = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 := by
    rw [← diag_fst_val g]
    exact Units.mul_inv_cancel_left _ _
  refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom, h]

/-- **Coordinates on the Borel subgroup**: an element of `B` is exactly a pair of diagonal units
together with a free upper-right entry. This is the set-level form of the decomposition
`TauCeti.GL2Borel.eq_torusHom_mul_unipotentHom` into the split torus and the unipotent radical; it
is what the cardinality count below runs on. -/
def equivProd : GL2Borel R ≃ (Rˣ × Rˣ) × R where
  toFun g := (diag g, ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1)
  invFun p := ⟨mk p.1.1 p.1.2 p.2, mk_mem _ _ _⟩
  left_inv g := by
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    rw [coe_mk, Matrix.eta_fin_two ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)]
    simp [apply_one_zero g]
  right_inv p := by simp

@[simp]
theorem equivProd_apply (g : GL2Borel R) :
    equivProd g = (diag g, ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1) :=
  (rfl)

@[simp]
theorem equivProd_symm_apply (p : (Rˣ × Rˣ) × R) :
    (equivProd (R := R)).symm p = ⟨mk p.1.1 p.1.2 p.2, mk_mem _ _ _⟩ :=
  (rfl)

/-- **Normal form**: an element of `GL₂` is upper triangular exactly when it is `!![a, b; 0, d]`
for two units `a`, `d` and a scalar `b`. -/
theorem mem_iff_exists_mk {g : GL (Fin 2) R} :
    g ∈ GL2Borel R ↔ ∃ (a d : Rˣ) (b : R), g = mk a d b := by
  refine ⟨fun hg => ⟨(diag ⟨g, hg⟩).1, (diag ⟨g, hg⟩).2,
    (g : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩, ?_⟩
  · exact congrArg Subtype.val ((equivProd (R := R)).symm_apply_apply ⟨g, hg⟩).symm
  · rintro ⟨a, d, b, rfl⟩
    exact mk_mem a d b

/-- If some conjugate of `u : GL (Fin 2) R` is upper triangular then `u` has an eigenvalue in the
base ring: writing `a` for the upper-left entry of that conjugate, `det (u - a) = 0`. This is the
eigenvalue that an element of the non-split torus has to be shown not to have. -/
theorem exists_det_sub_algebraMap_eq_zero {u g : GL (Fin 2) R}
    (h : g * u * g⁻¹ ∈ GL2Borel R) :
    ∃ a : R,
      ((u : Matrix (Fin 2) (Fin 2) R) - algebraMap R (Matrix (Fin 2) (Fin 2) R) a).det = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 2) (Fin 2) R,
      ((g * u * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = N := ⟨_, rfl⟩
  refine ⟨N 0 0, ?_⟩
  -- A scalar matrix is central, so conjugating `u - a` conjugates `u` and leaves `a` alone.
  have hgc : (g : Matrix (Fin 2) (Fin 2) R) * algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) := by
    rw [← Algebra.commutes (N 0 0) (g : Matrix (Fin 2) (Fin 2) R), mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]
  have key : (g : Matrix (Fin 2) (Fin 2) R) *
      ((u : Matrix (Fin 2) (Fin 2) R) - algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0)) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      N - algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hgc, ← hN, Units.val_mul, Units.val_mul]
  have h10 : N 1 0 = 0 := by rw [← hN]; exact mem_iff.mp h
  rw [← Matrix.det_units_conj g, key, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.algebraMap_matrix_apply, h10]

variable (R)

/-- The Borel subgroup is proper: the swap `!![0, 1; 1, 0]` is invertible but not upper
triangular. -/
theorem ne_top [Nontrivial R] : GL2Borel R ≠ ⊤ := by
  have hdet : IsUnit (Matrix.det !![(0 : R), 1; 1, 0]) := by
    simp [Matrix.det_fin_two_of]
  intro h
  have : Matrix.GeneralLinearGroup.mk'' _ hdet ∈ GL2Borel R := h ▸ Subgroup.mem_top _
  rw [mem_iff] at this
  simp at this

end GL2Borel

end CommRing

section FiniteField

variable (F : Type u) [Field F] [Fintype F]

namespace GL2Borel

/-- **The order of the Borel subgroup** of `GL₂(𝔽_q)` is `q (q - 1)²`: two diagonal units and one
free upper-right entry. -/
theorem card_eq :
    Nat.card (GL2Borel F) = Fintype.card F * (Fintype.card F - 1) ^ 2 := by
  rw [Nat.card_congr (equivProd (R := F)), Nat.card_prod, Nat.card_prod, Nat.card_units,
    Nat.card_eq_fintype_card]
  ring

/-- **The index of the Borel subgroup** of `GL₂(𝔽_q)` is `q + 1`, the number of points of the
projective line — hence the dimension of the principal series induced from `B`. -/
theorem index_eq : (GL2Borel F).index = Fintype.card F + 1 := by
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hpos : 0 < Fintype.card F * (Fintype.card F - 1) ^ 2 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) 2)
  have hcard := Subgroup.card_mul_index (GL2Borel F)
  rw [card_eq, natCard_GL_fin_two] at hcard
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hcard]
  ring

end GL2Borel

end FiniteField

end TauCeti
