/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# Scaling and negating integral lattices

Multiplying the form of an integral lattice by an integer leaves its carrier fixed and preserves
integrality. This file equips integral lattices with that scalar action and computes the induced
integral form, Gram matrix, determinant, discriminant, radical, and signature. Positive scaling
preserves the positive and negative indices of inertia, while negative scaling exchanges them;
negating the form is the special case `-1`.

The scalar is integral because arbitrary rational scaling need not preserve an integral form. A
later development may admit rational scalars together with the necessary integrality hypothesis;
the canonical operation internal to integral lattices is the integer action defined here.

## Main definitions and results

* `TauCeti.IntegralLattice.scale`: multiply the rational form by an integer while keeping the
  carrier fixed.
* `TauCeti.IntegralLattice.instMulActionInt`: the integer multiplicative action on integral
  lattices.
* `TauCeti.IntegralLattice.instInvolutiveNeg`: form negation, defined as scaling by `-1`.
* `TauCeti.IntegralLattice.isEven_neg_iff`: form negation preserves evenness.
* `TauCeti.IntegralLattice.gramMatrix_smul`: scaling multiplies every Gram-matrix entry.
* `TauCeti.IntegralLattice.determinant_smul`: the determinant is multiplied by the scalar to the
  lattice rank.
* `TauCeti.IntegralLattice.discriminant_smul`: the discriminant is multiplied by the absolute
  scalar to the lattice rank.
* `TauCeti.IntegralLattice.signature_smul_of_pos` and
  `TauCeti.IntegralLattice.signature_smul_of_neg`: scaling preserves or exchanges the two
  non-null indices according to the sign.
* `TauCeti.IntegralLattice.discriminant_neg`: form negation preserves the discriminant.
* `TauCeti.IntegralLattice.signature_neg`: form negation exchanges the positive and negative
  indices and preserves the null index.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1, form scaling and negation.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## Integer scaling -/

/-- Scale the form of an integral lattice by an integer, leaving its carrier unchanged.

Integer scaling preserves integrality because an integer multiple of every integral pairing is
again integral. The scalar acts on the rational form through the canonical map `ℤ → ℚ`.

The definition is marked `@[reducible]` because the carriers `(scale n L).carrier` and
`L.carrier` are definitionally equal, so a `Basis ι ℤ L` is definitionally a
`Basis ι ℤ (scale n L)` and instance search requires reducible unfolding to elaborate statements
without boilerplate transports. -/
@[expose, reducible]
def scale (n : ℤ) (L : IntegralLattice V) : IntegralLattice V where
  carrier := L.carrier
  form := (n : ℚ) • L.form
  isLattice := L.isLattice
  isSymm := L.isSymm.smul (n : ℚ)
  le_dual := by
    intro x hx
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have hmem := Submodule.smul_mem (1 : Submodule ℤ ℚ) n
      (L.form_mem_one ⟨x, hx⟩ ⟨y, hy⟩)
    simpa only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul] using hmem

/-- Integral lattices carry the canonical multiplicative action which scales their forms by
integers. -/
instance instMulActionInt : MulAction ℤ (IntegralLattice V) where
  smul := scale
  one_smul L := by
    apply IntegralLattice.ext (L := scale 1 L) (M := L)
    · rfl
    · ext x y
      simp
  mul_smul m n L := by
    apply IntegralLattice.ext (L := scale (m * n) L) (M := scale m (scale n L))
    · rfl
    · ext x y
      simp only [LinearMap.smul_apply, Int.cast_mul]
      ring

/-- Definitional bridge between scalar multiplication and `scale`. -/
theorem smul_def (n : ℤ) (L : IntegralLattice V) : n • L = scale n L :=
  (rfl)

@[simp]
theorem smul_carrier (n : ℤ) (L : IntegralLattice V) :
    (n • L).carrier = L.carrier :=
  (rfl)

@[simp]
theorem smul_form (n : ℤ) (L : IntegralLattice V) :
    (n • L).form = (n : ℚ) • L.form :=
  (rfl)

/-- Scaling the form does not change the rank of the carrier. -/
@[simp]
theorem finrank_smul (n : ℤ) (L : IntegralLattice V) :
    Module.finrank ℤ ↥(n • L) = Module.finrank ℤ L :=
  (rfl)

/-- The integral form of a scaled lattice is the corresponding integer multiple of the original
integral form. -/
theorem integralForm_smul_apply (n : ℤ) (L : IntegralLattice V) (x y : L) :
    (n • L).integralForm x y = n * L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  rw [integralForm_cast (n • L), Int.cast_mul, integralForm_cast L, smul_form,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Scaling commutes with the construction of the restricted integral form. -/
@[simp]
theorem integralForm_smul (n : ℤ) (L : IntegralLattice V) :
    (n • L).integralForm = n • L.integralForm := by
  ext x y
  exact integralForm_smul_apply n L x y

/-! ## Gram matrices and invariants -/

/-- Scaling a lattice multiplies every entry of every Gram matrix by the scalar. -/
@[simp]
theorem gramMatrix_smul (n : ℤ) (L : IntegralLattice V) {ι : Type v}
    (e : Basis ι ℤ L) :
    (n • L).gramMatrix e =
      (n • L.gramMatrix e : Matrix ι ι ℤ) := by
  ext i j
  rw [gramMatrix_apply (n • L), integralForm_smul_apply, ← gramMatrix_apply L,
    Matrix.smul_apply, smul_eq_mul]

/-- The Gram determinant of a scaled lattice is multiplied by the scalar to the size of the
basis. -/
@[simp]
theorem gramDet_smul (n : ℤ) (L : IntegralLattice V) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (e : Basis ι ℤ L) :
    (n • L).gramDet e = n ^ Fintype.card ι * L.gramDet e := by
  rw [gramDet_def (n • L), gramMatrix_smul, Matrix.det_smul, gramDet_def L]

/-- Scaling multiplies the signed determinant by the scalar to the rank of the lattice. -/
@[simp]
theorem determinant_smul (n : ℤ) (L : IntegralLattice V) :
    (n • L).determinant = n ^ Module.finrank ℤ L * L.determinant := by
  classical
  rw [determinant_eq_gramDet (n • L) (Module.Free.chooseBasis ℤ L),
    gramDet_smul, ← Module.finrank_eq_card_chooseBasisIndex,
    ← determinant_eq_gramDet L (Module.Free.chooseBasis ℤ L)]

/-- Scaling by a nonzero integer preserves nondegeneracy of the rational form.

This is a named API lemma rather than a simp lemma: simplification already derives it from
`smul_form` and the corresponding bilinear-form result. -/
theorem nondegenerate_smul_iff {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).form.Nondegenerate ↔ L.form.Nondegenerate := by
  rw [smul_form]
  exact TauCeti.BilinForm.nondegenerate_smul_iff
    (IsRegular.of_ne_zero (Int.cast_ne_zero.mpr hn))

/-! ## Radical and signature -/

/-- Scaling by a nonzero integer preserves the radical. -/
@[simp]
theorem radical_smul {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).radical = L.radical := by
  ext x
  rw [(n • L).mem_radical_iff, L.mem_radical_iff, smul_form]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro hx y
    exact (mul_eq_zero.mp (hx y)).resolve_left (Int.cast_ne_zero.mpr hn)
  · intro hx y
    rw [hx y, mul_zero]

/-- Scaling by a nonzero integer preserves the null index. -/
@[simp]
theorem sigNull_smul {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).sigNull = L.sigNull := by
  rw [sigNull, radical_smul hn, sigNull]

/-- Scaling by a positive integer preserves the positive index. -/
@[simp]
theorem sigPos_smul_of_pos {n : ℤ} (hn : 0 < n) (L : IntegralLattice V) :
    (n • L).sigPos = L.sigPos := by
  let _ := L.finiteDimensional
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [sigPos]
  rw [smul_form, LinearMap.BilinMap.toQuadraticMap_smul]
  exact QuadraticForm.sigPos_smul_of_pos L.form.toQuadraticMap hnq

/-- Scaling by a positive integer preserves the negative index. -/
@[simp]
theorem sigNeg_smul_of_pos {n : ℤ} (hn : 0 < n) (L : IntegralLattice V) :
    (n • L).sigNeg = L.sigNeg := by
  let _ := L.finiteDimensional
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [sigNeg]
  rw [smul_form, LinearMap.BilinMap.toQuadraticMap_smul]
  exact QuadraticForm.sigNeg_smul_of_pos L.form.toQuadraticMap hnq

/-- Scaling by a positive integer preserves the signature. -/
@[simp]
theorem signature_smul_of_pos {n : ℤ} (hn : 0 < n) (L : IntegralLattice V) :
    (n • L).signature = L.signature := by
  rw [signature, sigPos_smul_of_pos hn, sigNull_smul hn.ne', sigNeg_smul_of_pos hn,
    signature]

/-- Scaling by a negative integer exchanges the positive and negative indices. -/
@[simp]
theorem sigPos_smul_of_neg {n : ℤ} (hn : n < 0) (L : IntegralLattice V) :
    (n • L).sigPos = L.sigNeg := by
  let _ := L.finiteDimensional
  have hnq : (n : ℚ) < 0 := by exact_mod_cast hn
  rw [sigPos, sigNeg]
  rw [smul_form, LinearMap.BilinMap.toQuadraticMap_smul]
  exact QuadraticForm.sigPos_smul_of_neg L.form.toQuadraticMap hnq

/-- Scaling by a negative integer exchanges the negative and positive indices. -/
@[simp]
theorem sigNeg_smul_of_neg {n : ℤ} (hn : n < 0) (L : IntegralLattice V) :
    (n • L).sigNeg = L.sigPos := by
  let _ := L.finiteDimensional
  have hnq : (n : ℚ) < 0 := by exact_mod_cast hn
  rw [sigNeg, sigPos]
  rw [smul_form, LinearMap.BilinMap.toQuadraticMap_smul]
  exact QuadraticForm.sigNeg_smul_of_neg L.form.toQuadraticMap hnq

/-- Scaling by a negative integer exchanges the positive and negative indices and preserves the
null index. -/
@[simp]
theorem signature_smul_of_neg {n : ℤ} (hn : n < 0) (L : IntegralLattice V) :
    (n • L).signature = (L.sigNeg, L.sigNull, L.sigPos) := by
  rw [signature, sigPos_smul_of_neg hn, sigNull_smul hn.ne, sigNeg_smul_of_neg hn]

/-- Scaling multiplies the discriminant by the absolute scalar to the rank of the lattice. -/
@[simp]
theorem discriminant_smul (n : ℤ) (L : IntegralLattice V) :
    (n • L).discriminant = n.natAbs ^ Module.finrank ℤ L * L.discriminant := by
  rw [discriminant_def, determinant_smul, Int.natAbs_mul, Int.natAbs_pow, discriminant_def]

/-! ## Form negation -/

/-- Negating an integral lattice negates its form and leaves its carrier fixed. -/
instance instInvolutiveNeg : InvolutiveNeg (IntegralLattice V) where
  neg L := (-1 : ℤ) • L
  neg_neg L := by
    rw [← mul_smul]
    norm_num

/-- Definitional bridge between negation and scaling by `-1`. -/
theorem neg_def (L : IntegralLattice V) : -L = (-1 : ℤ) • L :=
  (rfl)

@[simp]
theorem neg_carrier (L : IntegralLattice V) : (-L).carrier = L.carrier :=
  (rfl)

@[simp]
theorem neg_form (L : IntegralLattice V) : (-L).form = -L.form := by
  rw [neg_def, smul_form]
  norm_num only [Int.cast_neg, Int.cast_one]
  exact neg_one_smul ℚ L.form

/-- Negating the form does not change the rank of the carrier. -/
@[simp]
theorem finrank_neg (L : IntegralLattice V) :
    Module.finrank ℤ ↥(-L) = Module.finrank ℤ L :=
  (rfl)

/-- The integral form of the negated lattice is the negative of the original integral form. -/
theorem integralForm_neg_apply (L : IntegralLattice V) (x y : L) :
    (-L).integralForm x y = -L.integralForm x y := by
  -- `rw [neg_def]` cannot rewrite through arguments whose type depends on the lattice carrier.
  change ((-1 : ℤ) • L).integralForm x y = -L.integralForm x y
  rw [integralForm_smul_apply, neg_one_mul]

/-- Form negation commutes with the construction of the restricted integral form. -/
@[simp]
theorem integralForm_neg (L : IntegralLattice V) :
    (-L).integralForm = -L.integralForm := by
  -- `rw [neg_def]` cannot rewrite an equality of forms whose domain depends on the carrier.
  change ((-1 : ℤ) • L).integralForm = -L.integralForm
  rw [integralForm_smul, neg_one_smul ℤ]

/-- An integral lattice is even if and only if its form negation is even. -/
@[simp]
theorem isEven_neg_iff (L : IntegralLattice V) : (-L).IsEven ↔ L.IsEven := by
  rw [(-L).isEven_iff_forall_norm, L.isEven_iff_forall_norm]
  constructor
  · intro h x
    obtain ⟨z, hz⟩ := h x
    refine ⟨-z, ?_⟩
    rw [norm_apply] at hz ⊢
    rw [neg_form] at hz
    simp only [LinearMap.neg_apply] at hz
    push_cast
    linarith
  · intro h x
    obtain ⟨z, hz⟩ := h x
    refine ⟨-z, ?_⟩
    rw [norm_apply] at hz ⊢
    rw [neg_form]
    simp only [LinearMap.neg_apply]
    push_cast
    rw [hz]
    ring

/-- Negation multiplies every Gram-matrix entry by `-1`. -/
@[simp]
theorem gramMatrix_neg (L : IntegralLattice V) {ι : Type v} (e : Basis ι ℤ L) :
    (-L).gramMatrix e = -L.gramMatrix e := by
  -- `rw [neg_def]` cannot rewrite through a basis whose type depends on the lattice carrier.
  change ((-1 : ℤ) • L).gramMatrix e = -L.gramMatrix e
  rw [gramMatrix_smul, neg_one_smul ℤ]

/-- Negating the form multiplies a Gram determinant by `(-1)` to the size of its basis. -/
@[simp]
theorem gramDet_neg (L : IntegralLattice V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    (-L).gramDet e = (-1 : ℤ) ^ Fintype.card ι * L.gramDet e := by
  -- `rw [neg_def]` cannot rewrite through a basis whose type depends on the lattice carrier.
  change ((-1 : ℤ) • L).gramDet e = (-1 : ℤ) ^ Fintype.card ι * L.gramDet e
  exact gramDet_smul (-1) L e

/-- Negating the form multiplies the signed determinant by `(-1)` to the lattice rank. -/
@[simp]
theorem determinant_neg (L : IntegralLattice V) :
    (-L).determinant = (-1 : ℤ) ^ Module.finrank ℤ L * L.determinant := by
  rw [neg_def, determinant_smul]

/-- Form negation preserves nondegeneracy.

This is a named API lemma rather than a simp lemma: simplification already derives it from
`neg_form` and the corresponding bilinear-form result. -/
theorem nondegenerate_neg_iff (L : IntegralLattice V) :
    (-L).form.Nondegenerate ↔ L.form.Nondegenerate := by
  rw [neg_def]
  exact nondegenerate_smul_iff (by norm_num) L

/-- Negating the form of a nondegenerate integral lattice preserves nondegeneracy. -/
instance instIsNondegenerateNeg (L : IntegralLattice V) [L.IsNondegenerate] :
    (-L).IsNondegenerate :=
  ⟨L.nondegenerate_neg_iff.mpr L.form_nondegenerate⟩

/-- Form negation preserves the radical. -/
@[simp]
theorem radical_neg (L : IntegralLattice V) : (-L).radical = L.radical := by
  rw [neg_def, radical_smul (by norm_num)]

/-- Form negation preserves the null index. -/
@[simp]
theorem sigNull_neg (L : IntegralLattice V) : (-L).sigNull = L.sigNull := by
  rw [neg_def, sigNull_smul (by norm_num)]

/-- Form negation exchanges the positive and negative indices. -/
@[simp]
theorem sigPos_neg (L : IntegralLattice V) : (-L).sigPos = L.sigNeg := by
  rw [neg_def, sigPos_smul_of_neg (by norm_num)]

/-- Form negation exchanges the negative and positive indices. -/
@[simp]
theorem sigNeg_neg (L : IntegralLattice V) : (-L).sigNeg = L.sigPos := by
  rw [neg_def, sigNeg_smul_of_neg (by norm_num)]

/-- Form negation exchanges the positive and negative indices and preserves the null index. -/
@[simp]
theorem signature_neg (L : IntegralLattice V) :
    (-L).signature = (L.sigNeg, L.sigNull, L.sigPos) := by
  rw [neg_def, signature_smul_of_neg (by norm_num)]

/-- Form negation preserves the nonnegative discriminant. -/
@[simp]
theorem discriminant_neg (L : IntegralLattice V) : (-L).discriminant = L.discriminant := by
  rw [neg_def, discriminant_smul]
  norm_num

/-! ## Interaction with constructors -/

@[simp]
theorem smul_ofSubmodule (n : ℤ) (S : Submodule ℤ V) [hS : S.IsLattice ℚ]
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm) (hle : S ≤ B.dualSubmodule S) :
    n • ofSubmodule S B hB hle = ofSubmodule S ((n : ℚ) • B) (hB.smul (n : ℚ))
      (by
        intro x hx
        rw [LinearMap.BilinForm.mem_dualSubmodule]
        intro y hy
        have hmem := Submodule.smul_mem (1 : Submodule ℤ ℚ) n (hle hx y hy)
        simpa only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul] using hmem) := by
  apply IntegralLattice.ext <;> simp

@[simp]
theorem neg_ofSubmodule (S : Submodule ℤ V) [hS : S.IsLattice ℚ]
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm) (hle : S ≤ B.dualSubmodule S) :
    -ofSubmodule S B hB hle = ofSubmodule S (-B) hB.neg
      (by
        intro x hx
        rw [LinearMap.BilinForm.mem_dualSubmodule]
        intro y hy
        have hmem := Submodule.neg_mem (1 : Submodule ℤ ℚ) (hle hx y hy)
        simpa only [LinearMap.neg_apply] using hmem) := by
  rw [neg_def, smul_ofSubmodule]
  apply IntegralLattice.ext
  · simp only [ofSubmodule_carrier]
  · rw [ofSubmodule_form, ofSubmodule_form]
    norm_num only [Int.cast_neg, Int.cast_one]
    exact neg_one_smul ℚ B

@[simp]
theorem smul_ofBasis (n : ℤ) {ι : Type*} [Finite ι] (b : Basis ι ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    n • ofBasis b B hB hint = ofBasis b ((n : ℚ) • B) (hB.smul (n : ℚ))
      (fun i j ↦ by
        have hmem := Submodule.smul_mem (1 : Submodule ℤ ℚ) n (hint i j)
        simpa only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul] using hmem) := by
  apply IntegralLattice.ext <;> simp

@[simp]
theorem neg_ofBasis {ι : Type*} [Finite ι] (b : Basis ι ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    -ofBasis b B hB hint = ofBasis b (-B) hB.neg
      (fun i j ↦ by
        have hmem := Submodule.neg_mem (1 : Submodule ℤ ℚ) (hint i j)
        simpa only [LinearMap.neg_apply] using hmem) := by
  rw [neg_def, smul_ofBasis]
  apply IntegralLattice.ext
  · simp only [ofBasis_carrier]
  · rw [ofBasis_form, ofBasis_form]
    norm_num only [Int.cast_neg, Int.cast_one]
    exact neg_one_smul ℚ B

open Classical in
@[simp]
theorem smul_ofGramMatrix (n : ℤ) {ι : Type*} [Fintype ι] (b : Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    n • ofGramMatrix b G hG = ofGramMatrix b (n • G) (hG.smul n) := by
  apply IntegralLattice.ext
  · rw [smul_carrier, ofGramMatrix_carrier, ofGramMatrix_carrier]
  · have hmap : (n • G).map (algebraMap ℤ ℚ) = (n : ℚ) • G.map (algebraMap ℤ ℚ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rfl
    rw [smul_form, ofGramMatrix_form, ofGramMatrix_form, hmap, map_smul]

open Classical in
@[simp]
theorem neg_ofGramMatrix {ι : Type*} [Fintype ι] (b : Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    -ofGramMatrix b G hG = ofGramMatrix b (-G) hG.neg := by
  simpa only [neg_def, neg_one_smul ℤ] using smul_ofGramMatrix (-1) b G hG

end TauCeti.IntegralLattice
