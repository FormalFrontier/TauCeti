/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` is imported publicly: `GL (Fin 2) R`
-- occurs in every statement below, and the cardinality of the general linear group over a finite
-- field is what the index computation runs on. It re-exports
-- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`, hence the `GL` notation, the coercion of
-- an element of `GL n R` to a function on indices, and `Matrix.GeneralLinearGroup.det`.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- `Matrix.GeneralLinearGroup.upperRightHom` and `Matrix.GeneralLinearGroup.scalar` occur in the
-- statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
-- `Subgroup.index` occurs in the statements below.
public import Mathlib.GroupTheory.Index
-- The `!![a, b; c, d]` notation occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Notation
-- Non-public: the `2 × 2` adjugate and the number of units of a finite field are used only inside
-- proofs, so downstream importers do not pay for them.
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The Borel subgroup of `GL₂`

The **Borel subgroup** `B` of `GL₂` is the subgroup of invertible upper-triangular matrices. It is
the standard minimal parabolic: over a finite field it is the subgroup from which the principal
series `Ind_B^{GL₂}(α ⊗ β)` is induced, and its index `q + 1` is the dimension of that induced
representation.

Everything except the two counting results is proved over an arbitrary commutative ring, where the
subgroup already makes sense: an upper-triangular matrix is invertible exactly when both diagonal
entries are units, and the inverse is again upper triangular because the `2 × 2` adjugate of an
upper-triangular matrix is upper triangular. Two facts organize the subgroup:

* the two diagonal entries of an element of `B` are units, and reading them off is a **group
  homomorphism** `TauCeti.GL2Borel.diag : B →* Rˣ × Rˣ`, split by the diagonal matrices
  (`TauCeti.GL2Borel.torusHom`) — this is the split torus `T`, and it is through it that a pair of
  characters `α, β` of `Rˣ` inflates to a character of `B`;
* forgetting nothing, `B` is in bijection with `(Rˣ × Rˣ) × R` (`TauCeti.GL2Borel.equivProd`), the
  upper-right entry being the free coordinate — the set-level form of the decomposition `B = T U`
  into the torus and the unipotent radical `U = ker (diag)`.

Over a finite field with `q` elements these give `|B| = q (q - 1)²` and hence `[GL₂(𝔽_q) : B] =
q + 1`, the number of points of the projective line.

## Main definitions

* `TauCeti.GL2Borel R`: the upper-triangular subgroup of `GL (Fin 2) R`.
* `TauCeti.GL2Borel.mk`: the element of `GL (Fin 2) R` with prescribed diagonal units and
  upper-right entry; it lies in `TauCeti.GL2Borel R`.
* `TauCeti.GL2Borel.diag`: the two diagonal entries of an element of the Borel subgroup, as a
  homomorphism to `Rˣ × Rˣ`, and `TauCeti.GL2Borel.torusHom`, its homomorphic section.
* `TauCeti.GL2Borel.equivProd`: the bijection `B ≃ (Rˣ × Rˣ) × R`.

## Main results

* `TauCeti.GL2Borel.mem_iff_exists_mk`: an invertible matrix is upper triangular exactly when it is
  `!![a, b; 0, d]` for units `a`, `d`.
* `TauCeti.GL2Borel.mem_ker_diag_iff`: the kernel of `TauCeti.GL2Borel.diag` is the unipotent
  radical, the image of `Matrix.GeneralLinearGroup.upperRightHom`.
* `TauCeti.GL2Borel.det_diag`: the determinant of an element of `B` is the product of its two
  diagonal entries.
* `TauCeti.GL2Borel.card_eq`: `|B| = q (q - 1)²` over a finite field with `q` elements.
* `TauCeti.GL2Borel.index_eq`: `[GL₂(𝔽_q) : B] = q + 1`.

## Implementation notes

The name follows the `GL2` prefix that
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` uses for this family of objects
(`GL2Borel`, `GL2PrincipalSeries`, `GL2Steinberg`, `GL2NonSplitTorus`), rather than being placed in
the `Matrix.GeneralLinearGroup` namespace; the statements are the roadmap's, with `[Field F]
[Fintype F]` weakened to `[CommRing R]` wherever the result does not count.

Membership is spelled by the single vanishing condition `g 1 0 = 0` rather than through
`Matrix.BlockTriangular`: in size `2` the two are the same condition, and the explicit form is what
every proof below uses.

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

section CommRing

variable (R : Type u) [CommRing R]

/-- The **Borel subgroup** of `GL₂`: the invertible upper-triangular `2 × 2` matrices, that is,
those `g` with `g 1 0 = 0`. It is a subgroup because the lower-left entry of a product of
upper-triangular matrices vanishes, and because the `2 × 2` adjugate of an upper-triangular matrix
is upper triangular, so the inverse of an invertible upper-triangular matrix is again upper
triangular. -/
def GL2Borel : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
    ring
  one_mem' := by
    simp [Matrix.one_apply_ne]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [hg]

namespace GL2Borel

variable {R}

@[simp]
theorem mem_iff {g : GL (Fin 2) R} :
    g ∈ GL2Borel R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  Iff.rfl

/-- The lower-left entry of an element of the Borel subgroup vanishes. -/
theorem apply_one_zero (g : GL2Borel R) :
    ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  g.2

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

/-- The determinant of an upper-triangular `2 × 2` matrix is the product of its diagonal
entries. -/
theorem det_val {g : GL (Fin 2) R} (hg : g ∈ GL2Borel R) :
    ((Matrix.GeneralLinearGroup.det g : Rˣ) : R)
      = (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  rw [mem_iff] at hg
  simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hg]

variable (R)

/-- The unipotent radical sits inside the Borel subgroup: `Matrix.GeneralLinearGroup.upperRightHom`
sends `b` to `!![1, b; 0, 1]`. -/
theorem upperRightHom_mem (b : R) :
    Matrix.GeneralLinearGroup.upperRightHom b ∈ GL2Borel R := by
  simp [mem_iff, Matrix.GeneralLinearGroup.upperRightHom]

/-- The scalar matrices sit inside the Borel subgroup. -/
theorem scalar_mem (u : Rˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ GL2Borel R := by
  simp [mem_iff, Matrix.scalar_apply, Matrix.diagonal_apply_ne]

variable {R}

/-- The invertible upper-triangular matrix `!![a, b; 0, d]` with prescribed diagonal units `a`, `d`
and prescribed upper-right entry `b`. Its inverse is written out, so no invertibility side
condition is discharged twice. -/
def mk (a d : Rˣ) (b : R) : GL (Fin 2) R where
  val := !![(a : R), b; 0, (d : R)]
  inv := !![((a⁻¹ : Rˣ) : R), -((a⁻¹ : Rˣ) * b * (d⁻¹ : Rˣ)); 0, ((d⁻¹ : Rˣ) : R)]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    simp [mul_comm, mul_left_comm, mul_assoc]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    congr 1
    simp

@[simp]
theorem mk_val (a d : Rˣ) (b : R) :
    ((mk a d b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), b; 0, (d : R)] :=
  (rfl)

theorem mk_mem (a d : Rˣ) (b : R) : mk a d b ∈ GL2Borel R := by
  simp [mem_iff]

/-- The two diagonal entries of an element of the Borel subgroup, as units of `R`: the inverse of
`g` is again upper triangular, so the diagonal entries of `g` and of `g⁻¹` multiply to the diagonal
entries of `1`. This is the **split torus** `T`, and it is a group homomorphism because the
diagonal of a product of upper-triangular matrices is the product of the diagonals. -/
def diag : GL2Borel R →* Rˣ × Rˣ where
  toFun g :=
    (⟨((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0,
        (((g : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0,
        by
          have := mul_apply_zero_zero (g := (g : GL (Fin 2) R))
            ((GL2Borel R).inv_mem g.2)
          rw [mul_inv_cancel] at this
          simpa using this.symm,
        by
          have := mul_apply_zero_zero (g := ((g : GL (Fin 2) R)⁻¹ : GL (Fin 2) R)) g.2
          rw [inv_mul_cancel] at this
          simpa using this.symm⟩,
      ⟨((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1,
        (((g : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1,
        by
          have := mul_apply_one_one (h := ((g : GL (Fin 2) R)⁻¹ : GL (Fin 2) R)) g.2
          rw [mul_inv_cancel] at this
          simpa using this.symm,
        by
          have := mul_apply_one_one (h := (g : GL (Fin 2) R))
            ((GL2Borel R).inv_mem g.2)
          rw [inv_mul_cancel] at this
          simpa using this.symm⟩)
  map_one' := by
    ext <;> simp
  map_mul' g h := by
    ext
    · exact mul_apply_zero_zero h.2
    · exact mul_apply_one_one g.2

@[simp]
theorem diag_fst_val (g : GL2Borel R) :
    (((diag g).1 : Rˣ) : R) = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 :=
  (rfl)

@[simp]
theorem diag_snd_val (g : GL2Borel R) :
    (((diag g).2 : Rˣ) : R) = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 :=
  (rfl)

@[simp]
theorem diag_mk (a d : Rˣ) (b : R) : diag ⟨mk a d b, mk_mem a d b⟩ = (a, d) := by
  ext <;> simp

/-- The determinant of an element of the Borel subgroup is the product of the two torus
coordinates. -/
theorem det_diag (g : GL2Borel R) :
    Matrix.GeneralLinearGroup.det (g : GL (Fin 2) R) = (diag g).1 * (diag g).2 := by
  ext
  simpa using det_val g.2

/-- The **split torus** `T`, as a homomorphic section of `TauCeti.GL2Borel.diag`: the diagonal
matrix `!![a, 0; 0, d]`. Its existence is what upgrades the bijection
`TauCeti.GL2Borel.equivProd` to a genuine splitting `B = T U`. -/
def torusHom : Rˣ × Rˣ →* GL2Borel R where
  toFun p := ⟨mk p.1 p.2 0, mk_mem _ _ _⟩
  map_one' := by
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem torusHom_val (p : Rˣ × Rˣ) :
    ((torusHom p : GL2Borel R) : GL (Fin 2) R) = mk p.1 p.2 0 :=
  (rfl)

@[simp]
theorem diag_torusHom (p : Rˣ × Rˣ) : diag (torusHom p) = p := by
  ext <;> simp

/-- The torus homomorphism is surjective: the diagonal matrix `!![a, 0; 0, d]` realizes `(a, d)`. -/
theorem diag_surjective : Function.Surjective (diag (R := R)) := fun p =>
  ⟨torusHom p, diag_torusHom p⟩

/-- The kernel of the torus homomorphism is the **unipotent radical**: the elements of the Borel
subgroup with both diagonal entries `1`, that is, the image of
`Matrix.GeneralLinearGroup.upperRightHom`. -/
theorem mem_ker_diag_iff (g : GL2Borel R) :
    g ∈ (diag (R := R)).ker ↔
      ∃ b : R, (g : GL (Fin 2) R) = Matrix.GeneralLinearGroup.upperRightHom b := by
  constructor
  · intro hg
    refine ⟨((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩
    have h₀ : ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := by
      have := congrArg (fun p : Rˣ × Rˣ => ((p.1 : Rˣ) : R)) (MonoidHom.mem_ker.mp hg)
      simpa using this
    have h₁ : ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
      have := congrArg (fun p : Rˣ × Rˣ => ((p.2 : Rˣ) : R)) (MonoidHom.mem_ker.mp hg)
      simpa using this
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom, h₀, h₁, apply_one_zero g]
  · rintro ⟨b, hb⟩
    refine MonoidHom.mem_ker.mpr ?_
    ext <;> simp [hb, Matrix.GeneralLinearGroup.upperRightHom]

/-- **The Borel subgroup is `T U`**: an element of `B` is exactly a pair of diagonal units together
with a free upper-right entry. This is the set-level form of the decomposition into the split torus
and the unipotent radical; it is what the cardinality count below runs on. -/
def equivProd : GL2Borel R ≃ (Rˣ × Rˣ) × R where
  toFun g := (diag g, ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1)
  invFun p := ⟨mk p.1.1 p.1.2 p.2, mk_mem _ _ _⟩
  left_inv g := by
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    rw [mk_val, Matrix.eta_fin_two ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)]
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

/-- **Normal form**: an invertible `2 × 2` matrix is upper triangular exactly when it is
`!![a, b; 0, d]` for two units `a`, `d` and a scalar `b`. In particular an upper-triangular matrix
is invertible precisely when both of its diagonal entries are units. -/
theorem mem_iff_exists_mk {g : GL (Fin 2) R} :
    g ∈ GL2Borel R ↔ ∃ (a d : Rˣ) (b : R), g = mk a d b := by
  refine ⟨fun hg => ⟨(diag ⟨g, hg⟩).1, (diag ⟨g, hg⟩).2,
    (g : Matrix (Fin 2) (Fin 2) R) 0 1, ?_⟩, ?_⟩
  · exact congrArg Subtype.val ((equivProd (R := R)).symm_apply_apply ⟨g, hg⟩).symm
  · rintro ⟨a, d, b, rfl⟩
    exact mk_mem a d b

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
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hG : Nat.card (GL (Fin 2) F) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field, ← hq]
    simp [Fin.prod_univ_two]
  have hcard := Subgroup.card_mul_index (GL2Borel F)
  rw [card_eq, hG] at hcard
  have hkey : q * (q - 1) ^ 2 * (q + 1) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    zify [h1, h2, h3]
    ring
  have hpos : 0 < q * (q - 1) ^ 2 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) 2)
  exact Nat.eq_of_mul_eq_mul_left hpos (hcard.trans hkey.symm)

end GL2Borel

end FiniteField

end TauCeti
