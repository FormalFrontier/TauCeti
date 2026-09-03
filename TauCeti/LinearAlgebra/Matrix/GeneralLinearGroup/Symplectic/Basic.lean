/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.symplecticGroup`, `Matrix.J`, and the `Matrix.SymplecticGroup` lemmas occur in the
-- statements below.
public import Mathlib.LinearAlgebra.SymplecticGroup
-- This module re-exports `GeneralLinearGroup.Defs`, which supplies the `GL` notation, the
-- coercion of an element of `GL n R` to a matrix, and `Matrix.GeneralLinearGroup.mk''`.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `Matrix.reindexAlgEquiv` is the body of `TauCeti.reindexGL`, and `finSumFinEquiv` occurs in
-- the statements of the `Fin`-indexed section.
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The symplectic group as a subgroup of the general linear group

For a commutative ring `R` and a finite index type `l`, the matrices `M` with `M J Mᵀ = J` form
Mathlib's `Matrix.symplecticGroup l R`, a `Submonoid` of the matrix monoid whose elements happen
to be invertible: its inverse is a separate `Inv` instance, and its `Group` structure is built by
hand. The algebraic-group development instead needs the symplectic group *inside the general
linear group* — the concrete target that the points of the symplectic group scheme will be
identified with, the way `TauCeti.GL2Borel` is the concrete target for the Borel coordinate Hopf
algebra.

`TauCeti.GLSymplectic` is that subgroup of `GL (l ⊕ l) R`. Its carrier is literally membership of
the underlying matrix in `Matrix.symplecticGroup l R`, so the defining conditions `M J Mᵀ = J`
and `Mᵀ J M = J` transfer directly, and `TauCeti.GLSymplectic.mulEquivSymplecticGroup` identifies
the subgroup with Mathlib's group so that neither view is reproved from the other. Invertibility
costs nothing: a symplectic matrix has unit determinant
(`Matrix.SymplecticGroup.symplectic_det`), which is what makes the two carriers agree, and
closure under the unit inverse is Mathlib's computation `M⁻¹ = (-J) Mᵀ J`
(`Matrix.SymplecticGroup.inv_eq_symplectic_inv`) transported across `Matrix.coe_units_inv`.

Everything works over an arbitrary commutative ring and an arbitrary finite index type, including
the empty index type and the zero ring; there is no nontriviality, rank, or characteristic
hypothesis. The index type is `l ⊕ l` throughout, matching `Matrix.J`.

The final sections construct the elementary one-parameter subgroups belonging to the long roots
`±2eᵢ` and the short roots `eᵢ-eⱼ`, `eᵢ+eⱼ`, and `-eᵢ-eⱼ` in `Fin (m+m)` coordinates. The
symplectic coordinate Hopf algebra and group scheme live in
`TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic`; their root-subgroup morphisms live in
`TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup`.

## Main declarations

* `TauCeti.GLSymplectic`: the symplectic matrices as a subgroup of `GL (l ⊕ l) R`.
* `TauCeti.GLSymplectic.mem_iff` and `TauCeti.GLSymplectic.mem_iff'`: the two standard forms of
  the defining condition, `M J Mᵀ = J` and `Mᵀ J M = J`.
* `TauCeti.GLSymplectic.ofSymplecticGroup`: a symplectic matrix, read into the general linear
  group through its unit determinant.
* `TauCeti.GLSymplectic.mulEquivSymplecticGroup`: the group identification with
  `Matrix.symplecticGroup`.
* `TauCeti.GLSymplectic.symJ`: the standard alternating form, as an element of the subgroup.
* `TauCeti.GLSymplectic.map`: the group morphism induced by a ring morphism of value rings,
  restricting `Matrix.GeneralLinearGroup.map`.
* `TauCeti.JFin` and `TauCeti.GLSymplecticFin`: the alternating form and the symplectic subgroup
  in `Fin (m + m)` coordinates, transported along `finSumFinEquiv`, with
  `TauCeti.GLSymplecticFin.mulEquivGLSymplectic` identifying the two presentations. The
  `Fin`-indexed form is what the symplectic coordinate Hopf algebra cuts out of `GLₘ₊ₘ`, whose
  coordinate ring is `Fin`-indexed.
* `TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom` and
  `negativeLongRootTransvectionHom`: the two families of long-root one-parameter subgroups.
* `TauCeti.GLSymplecticFin.differenceShortRootHom`, `positiveSumShortRootHom`, and
  `negativeSumShortRootHom`: the three
  families of short-root one-parameter subgroups.
* `TauCeti.GLSymplecticFin.ShortRootFamily`: a uniform index for the three short-root families.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex`: a uniform index for all long- and short-root
  one-parameter subgroups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3 and §24.6, where `Sp₂ₙ` is introduced as the
  subgroup of `GL₂ₙ` preserving a nondegenerate alternating form.

The identification with Mathlib's `Matrix.symplecticGroup` is routine and is not adapted from the
reference.
-/

public section

open Matrix

namespace TauCeti

universe u v

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type u) [CommRing R]

/-- The **symplectic group** as a subgroup of `GL (l ⊕ l) R`: the invertible matrices whose
underlying matrix satisfies `M J Mᵀ = J`. `TauCeti.GLSymplectic.mulEquivSymplecticGroup`
identifies it with Mathlib's submonoid form `Matrix.symplecticGroup`. -/
def GLSymplectic : Subgroup (GL (l ⊕ l) R) where
  carrier := {M | (M : Matrix (l ⊕ l) (l ⊕ l) R) ∈ Matrix.symplecticGroup l R}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    exact Submonoid.mul_mem _ ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one]
    exact Submonoid.one_mem _
  inv_mem' {M} hM := by
    simp only [Set.mem_ofPred_eq] at hM ⊢
    rw [Matrix.coe_units_inv, SymplecticGroup.inv_eq_symplectic_inv _ hM]
    exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ (SymplecticGroup.neg_mem (SymplecticGroup.J_mem l R))
        (SymplecticGroup.transpose_mem hM)) (SymplecticGroup.J_mem l R)

namespace GLSymplectic

variable {l R}

@[simp]
theorem mem_iff_mem_symplecticGroup {M : GL (l ⊕ l) R} :
    M ∈ GLSymplectic l R ↔ (M : Matrix (l ⊕ l) (l ⊕ l) R) ∈ Matrix.symplecticGroup l R :=
  Iff.rfl

/-- Membership in the symplectic subgroup, in the form `M J Mᵀ = J`. -/
theorem mem_iff {M : GL (l ⊕ l) R} :
    M ∈ GLSymplectic l R ↔
      (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = J l R :=
  SymplecticGroup.mem_iff

/-- Membership in the symplectic subgroup, in the transposed form `Mᵀ J M = J`. -/
theorem mem_iff' {M : GL (l ⊕ l) R} :
    M ∈ GLSymplectic l R ↔
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R) = J l R :=
  SymplecticGroup.mem_iff'

/-- An upper unitriangular block matrix is symplectic when its upper-right block is symmetric. -/
theorem fromBlocks_upper_mem (B : Matrix l l R) (hB : Bᵀ = B) :
    Matrix.fromBlocks 1 B 0 1 ∈ Matrix.symplecticGroup l R := by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB]

/-- A lower unitriangular block matrix is symplectic when its lower-left block is symmetric. -/
theorem fromBlocks_lower_mem (C : Matrix l l R) (hC : Cᵀ = C) :
    Matrix.fromBlocks 1 0 C 1 ∈ Matrix.symplecticGroup l R := by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hC]

/-- A block-diagonal matrix is symplectic when its diagonal blocks satisfy the defining inverse
transpose relation. -/
theorem fromBlocks_diagonal_mem (A D : Matrix l l R) (hAD : Aᵀ * D = 1) :
    Matrix.fromBlocks A 0 0 D ∈ Matrix.symplecticGroup l R := by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hAD]

variable (l R)

/-- A symplectic matrix, viewed in the general linear group through its unit determinant
(`Matrix.SymplecticGroup.symplectic_det`). -/
noncomputable def ofSymplecticGroup (S : Matrix.symplecticGroup l R) : GL (l ⊕ l) R :=
  Matrix.GeneralLinearGroup.mk'' _ (SymplecticGroup.symplectic_det S.2)

@[simp]
theorem coe_ofSymplecticGroup (S : Matrix.symplecticGroup l R) :
    (ofSymplecticGroup l R S : Matrix (l ⊕ l) (l ⊕ l) R) =
      (S : Matrix (l ⊕ l) (l ⊕ l) R) := by
  simp [ofSymplecticGroup]

theorem ofSymplecticGroup_mem (S : Matrix.symplecticGroup l R) :
    ofSymplecticGroup l R S ∈ GLSymplectic l R := by
  simpa only [mem_iff_mem_symplecticGroup, coe_ofSymplecticGroup] using S.2

/-- **The symplectic subgroup of the general linear group is Mathlib's symplectic group.** The
two carriers agree because a symplectic matrix has unit determinant, so the equivalence is the
identity on underlying matrices; its content is that the two group structures match. -/
noncomputable def mulEquivSymplecticGroup : GLSymplectic l R ≃* Matrix.symplecticGroup l R where
  toFun M := ⟨((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R), M.2⟩
  invFun S := ⟨ofSymplecticGroup l R S, ofSymplecticGroup_mem l R S⟩
  left_inv M := by
    refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
    simp
  right_inv S := by
    refine Subtype.ext ?_
    simp
  map_mul' M N := rfl

@[simp]
theorem coe_mulEquivSymplecticGroup (M : GLSymplectic l R) :
    ((mulEquivSymplecticGroup l R M : Matrix.symplecticGroup l R) :
        Matrix (l ⊕ l) (l ⊕ l) R) =
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) := by
  simp [mulEquivSymplecticGroup]

/-- The standard alternating form `Matrix.J`, as an element of the symplectic subgroup. -/
noncomputable def symJ : GLSymplectic l R :=
  ⟨ofSymplecticGroup l R (SymplecticGroup.symJ l R),
    ofSymplecticGroup_mem l R (SymplecticGroup.symJ l R)⟩

@[simp]
theorem coe_symJ : ((symJ l R : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = J l R := by
  simp [symJ, SymplecticGroup.symJ]

section Map

variable {l R} {S : Type*} [CommRing S]

/-- A ring morphism of value rings carries symplectic matrices to symplectic matrices. -/
theorem map_mem (f : R →+* S) {M : GL (l ⊕ l) R} (hM : M ∈ GLSymplectic l R) :
    Matrix.GeneralLinearGroup.map f M ∈ GLSymplectic l S :=
  SymplecticGroup.map_mem hM f

variable (l) in
/-- The group morphism between symplectic subgroups induced by a ring morphism of value rings:
the restriction of `Matrix.GeneralLinearGroup.map`, which acts entrywise. -/
def map (f : R →+* S) : GLSymplectic l R →* GLSymplectic l S where
  toFun M := ⟨Matrix.GeneralLinearGroup.map f M, map_mem f M.2⟩
  map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map f))
  map_mul' M N := Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map f) M.1 N.1)

/-- The underlying general-linear value of the induced morphism is
`Matrix.GeneralLinearGroup.map`. -/
@[simp]
theorem coe_map (f : R →+* S) (M : GLSymplectic l R) :
    ((map l f M : GLSymplectic l S) : GL (l ⊕ l) S) =
      Matrix.GeneralLinearGroup.map f (M : GL (l ⊕ l) R) := by
  simp [map]

@[simp]
theorem map_id : map l (RingHom.id R) = MonoidHom.id (GLSymplectic l R) := by
  refine MonoidHom.ext fun M => Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  simp

@[simp]
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) :
    map l (g.comp f) = (map l g).comp (map l f) := by
  refine MonoidHom.ext fun M => Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  simp

end Map

end GLSymplectic

/-! ### The `Fin`-indexed presentation

The coordinate ring of `GLₙ` is indexed by `Fin n`, so the symplectic group scheme cuts its
subgroup out of `GL (Fin (m + m)) A` rather than `GL (Fin m ⊕ Fin m) A`. This section transports
the alternating form and the subgroup along `finSumFinEquiv` and records that nothing is lost. -/

section FinIndex

variable (m : ℕ) (R : Type u)

section

variable [CommSemiring R]

/-- Reindexing along `finSumFinEquiv`, as a group isomorphism of general linear groups. -/
def reindexGL : GL (Fin (m + m)) R ≃* GL (Fin m ⊕ Fin m) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R finSumFinEquiv.symm).toRingEquiv.toMulEquiv

@[simp]
theorem coe_reindexGL (M : GL (Fin (m + m)) R) :
    (reindexGL m R M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
      (M : Matrix (Fin (m + m)) (Fin (m + m)) R).submatrix finSumFinEquiv finSumFinEquiv := by
  simp [reindexGL, Units.coe_mapEquiv, Matrix.reindex_apply]

end

-- `Matrix.J` and `Matrix.map_J` are stated for commutative rings, so the form and the
-- subgroup require `[CommRing R]` even though the reindexing above does not.
variable [CommRing R]

/-- The standard alternating form in `Fin (m + m)` coordinates: `Matrix.J`, transported along
`finSumFinEquiv`. -/
def JFin : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  (J (Fin m) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

variable {R} in
/-- Entrywise application of a ring morphism carries the transported alternating form to the
transported alternating form. -/
@[simp]
theorem JFin_map {S : Type*} [CommRing S] (f : R →+* S) : (JFin m R).map f = JFin m S := by
  have h := Matrix.map_J (l := Fin m) (R := R) (S := S) f
  ext i j
  simpa [JFin] using congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

/-- Transporting back along `finSumFinEquiv` recovers `Matrix.J`. -/
@[simp]
theorem JFin_submatrix :
    (JFin m R).submatrix finSumFinEquiv finSumFinEquiv = J (Fin m) R := by
  ext i j
  simp [JFin]

/-- The symplectic subgroup of `GL (Fin (m + m)) R`: the pullback of `TauCeti.GLSymplectic`
along the reindexing isomorphism. -/
def GLSymplecticFin : Subgroup (GL (Fin (m + m)) R) :=
  (GLSymplectic (Fin m) R).comap (reindexGL m R).toMonoidHom

namespace GLSymplecticFin

variable {m R}

/-- Membership in the `Fin`-indexed symplectic subgroup is the defining condition
`M J Mᵀ = J` against the transported alternating form. -/
@[simp]
theorem mem_iff {M : GL (Fin (m + m)) R} :
    M ∈ GLSymplecticFin m R ↔
      (M : Matrix (Fin (m + m)) (Fin (m + m)) R) * JFin m R *
          (M : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ =
        JFin m R := by
  rw [GLSymplecticFin, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, GLSymplectic.mem_iff,
    coe_reindexGL, ← JFin_submatrix m (R := R), Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  constructor
  · intro h
    have := congrArg (fun N => N.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) h
    simpa [Matrix.submatrix_submatrix, JFin] using this
  · intro h
    rw [h]

/-- Membership in the `Fin`-indexed symplectic subgroup, in the transposed form `Mᵀ J M = J`. -/
theorem mem_iff' {M : GL (Fin (m + m)) R} :
    M ∈ GLSymplecticFin m R ↔
      (M : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ * JFin m R *
          (M : Matrix (Fin (m + m)) (Fin (m + m)) R) =
        JFin m R := by
  rw [GLSymplecticFin, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, GLSymplectic.mem_iff',
    coe_reindexGL, ← JFin_submatrix m (R := R), Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  constructor
  · intro h
    have := congrArg (fun N => N.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) h
    simpa [Matrix.submatrix_submatrix, JFin] using this
  · intro h
    rw [h]

variable (m R)

/-- The two presentations of the symplectic subgroup agree: reindexing along `finSumFinEquiv`
identifies the `Fin (m + m)`-indexed subgroup with the `Fin m ⊕ Fin m`-indexed one. -/
def mulEquivGLSymplectic : GLSymplecticFin m R ≃* GLSymplectic (Fin m) R where
  toFun M := ⟨reindexGL m R M, M.2⟩
  invFun N := ⟨(reindexGL m R).symm N, by
    rw [GLSymplecticFin, Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact N.2⟩
  left_inv M := Subtype.ext (by simp)
  right_inv N := Subtype.ext (by simp)
  map_mul' M N := Subtype.ext (map_mul (reindexGL m R) _ _)

@[simp]
theorem coe_mulEquivGLSymplectic (M : GLSymplecticFin m R) :
    ((mulEquivGLSymplectic m R M : GLSymplectic (Fin m) R) : GL (Fin m ⊕ Fin m) R) =
      reindexGL m R (M : GL (Fin (m + m)) R) := by
  simp [mulEquivGLSymplectic]

/-- A ring morphism carries `Fin`-indexed symplectic matrices to symplectic matrices. -/
def map {S : Type*} [CommRing S] (f : R →+* S) :
    GLSymplecticFin m R →* GLSymplecticFin m S where
  toFun M := ⟨Matrix.GeneralLinearGroup.map f M, by
    have hM := M.2
    rw [mem_iff] at hM ⊢
    -- Membership stores the same matrix equation through the `GL` and subtype coercions;
    -- no public lemma exposes all of those wrappers at once.
    change M.1.val.map f * JFin m S * (M.1.val.map f)ᵀ = JFin m S
    simpa only [Matrix.map_mul, Matrix.transpose_map, JFin_map] using
      congrArg (fun X => X.map f) hM⟩
  map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map f))
  map_mul' M N := Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map f) M.1 N.1)

/-- The underlying general-linear element of a mapped symplectic matrix is its entrywise map. -/
@[simp]
theorem coe_map {S : Type*} [CommRing S] (f : R →+* S) (M : GLSymplecticFin m R) :
    ((GLSymplecticFin.map m R f M : GLSymplecticFin m S) : GL (Fin (m + m)) S) =
      Matrix.GeneralLinearGroup.map f (M : GL (Fin (m + m)) R) :=
  (rfl)

end GLSymplecticFin

/-! ### Long-root transvections -/

namespace GLSymplecticFin

variable {m R}

/-- An upper-block and a lower-block index have distinct images in `Fin (m + m)`. -/
theorem finSumFinEquiv_inl_ne_inr (i j : Fin m) :
    finSumFinEquiv (Sum.inl i) ≠ finSumFinEquiv (Sum.inr j) :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr

/-- A lower-block and an upper-block index have distinct images in `Fin (m + m)`. -/
theorem finSumFinEquiv_inr_ne_inl (i j : Fin m) :
    finSumFinEquiv (Sum.inr i) ≠ finSumFinEquiv (Sum.inl j) :=
  finSumFinEquiv.injective.ne Sum.inr_ne_inl

/-- Reindexing a transvection from `Fin (m + m)` coordinates to sum coordinates recovers the
transvection at the corresponding sum indices. -/
@[simp]
theorem reindexGL_transvectionUnit (i j : Fin m ⊕ Fin m) (hij : i ≠ j) (c : R) :
    reindexGL m R
        (transvectionUnit (finSumFinEquiv.injective.ne hij) c) =
      transvectionUnit hij c := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  simp only [coe_reindexGL, coe_transvectionUnit, Matrix.submatrix_apply]
  simp [Matrix.transvection, Matrix.single, Matrix.one_apply,
    finSumFinEquiv.injective.eq_iff]

private theorem upperLongRoot_mem (i : Fin m) (c : R) :
    transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : Fin m ⊕ Fin m) ≠ Sum.inr i) c ∈
      GLSymplectic (Fin m) R := by
  rw [GLSymplectic.mem_iff_mem_symplecticGroup]
  have hmatrix :
      (transvectionUnit
          (Sum.inl_ne_inr : (Sum.inl i : Fin m ⊕ Fin m) ≠ Sum.inr i) c :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
        Matrix.fromBlocks 1 (Matrix.single i i c) 0 1 := by
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.transvection, Matrix.single, Matrix.fromBlocks, Matrix.one_apply]
  rw [hmatrix]
  exact GLSymplectic.fromBlocks_upper_mem _ (by simp)

private theorem lowerLongRoot_mem (i : Fin m) (c : R) :
    transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : Fin m ⊕ Fin m) ≠ Sum.inl i) c ∈
      GLSymplectic (Fin m) R := by
  rw [GLSymplectic.mem_iff_mem_symplecticGroup]
  have hmatrix :
      (transvectionUnit
          (Sum.inr_ne_inl : (Sum.inr i : Fin m ⊕ Fin m) ≠ Sum.inl i) c :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
        Matrix.fromBlocks 1 0 (Matrix.single i i c) 1 := by
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.transvection, Matrix.single, Matrix.fromBlocks, Matrix.one_apply]
  rw [hmatrix]
  exact GLSymplectic.fromBlocks_lower_mem _ (by simp)

/-- The symplectic matrix `x_{2eᵢ}(c) = 1 + c E_{i,m+i}`, in `Fin (m + m)` coordinates. -/
def positiveLongRootTransvectionUnit (i : Fin m) (c : R) : GLSymplecticFin m R :=
  ⟨transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c, by
    rw [GLSymplecticFin, Subgroup.mem_comap]
    -- Membership in the comap is definitionally membership after `reindexGL`; there is no
    -- dedicated theorem for this specialized transvection goal.
    change reindexGL m R (transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c) ∈ _
    rw [reindexGL_transvectionUnit]
    exact upperLongRoot_mem i c⟩

/-- The matrix underlying the positive long-root transvection is the corresponding elementary
transvection. -/
@[simp]
theorem coe_positiveLongRootTransvectionUnit (i : Fin m) (c : R) :
    ((positiveLongRootTransvectionUnit i c : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      transvectionUnit (finSumFinEquiv_inl_ne_inr i i) c :=
  by rw [positiveLongRootTransvectionUnit]

/-- The symplectic matrix `x_{-2eᵢ}(c) = 1 + c E_{m+i,i}`, in `Fin (m + m)` coordinates. -/
def negativeLongRootTransvectionUnit (i : Fin m) (c : R) : GLSymplecticFin m R :=
  ⟨transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c, by
    rw [GLSymplecticFin, Subgroup.mem_comap]
    -- Membership in the comap is definitionally membership after `reindexGL`; there is no
    -- dedicated theorem for this specialized transvection goal.
    change reindexGL m R (transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c) ∈ _
    rw [reindexGL_transvectionUnit]
    exact lowerLongRoot_mem i c⟩

/-- The matrix underlying the negative long-root transvection is the corresponding elementary
transvection. -/
@[simp]
theorem coe_negativeLongRootTransvectionUnit (i : Fin m) (c : R) :
    ((negativeLongRootTransvectionUnit i c : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      transvectionUnit (finSumFinEquiv_inr_ne_inl i i) c :=
  by rw [negativeLongRootTransvectionUnit]

/-- The positive long-root transvections form a one-parameter subgroup. -/
def positiveLongRootTransvectionHom (i : Fin m) :
    Multiplicative R →* GLSymplecticFin m R where
  toFun c := positiveLongRootTransvectionUnit i (Multiplicative.toAdd c)
  map_one' := Subtype.ext (transvectionUnit_zero _)
  map_mul' c d :=
    Subtype.ext (transvectionUnit_add _ (Multiplicative.toAdd c) (Multiplicative.toAdd d))

/-- The negative long-root transvections form a one-parameter subgroup. -/
def negativeLongRootTransvectionHom (i : Fin m) :
    Multiplicative R →* GLSymplecticFin m R where
  toFun c := negativeLongRootTransvectionUnit i (Multiplicative.toAdd c)
  map_one' := Subtype.ext (transvectionUnit_zero _)
  map_mul' c d :=
    Subtype.ext (transvectionUnit_add _ (Multiplicative.toAdd c) (Multiplicative.toAdd d))

@[simp]
theorem positiveLongRootTransvectionHom_apply (i : Fin m) (c : Multiplicative R) :
    positiveLongRootTransvectionHom i c =
      positiveLongRootTransvectionUnit i (Multiplicative.toAdd c) :=
  (rfl)

@[simp]
theorem negativeLongRootTransvectionHom_apply (i : Fin m) (c : Multiplicative R) :
    negativeLongRootTransvectionHom i c =
      negativeLongRootTransvectionUnit i (Multiplicative.toAdd c) :=
  (rfl)

/-- Adding parameters multiplies positive long-root transvections. -/
@[simp]
theorem positiveLongRootTransvectionUnit_add (i : Fin m) (c d : R) :
    positiveLongRootTransvectionUnit i (c + d) =
      positiveLongRootTransvectionUnit i c * positiveLongRootTransvectionUnit i d := by
  simpa only [positiveLongRootTransvectionHom_apply, toAdd_ofAdd, toAdd_mul] using
    ((positiveLongRootTransvectionHom (R := R) i).map_mul
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd d))

/-- Inverting a positive long-root transvection negates its parameter. -/
@[simp]
theorem positiveLongRootTransvectionUnit_inv (i : Fin m) (c : R) :
    (positiveLongRootTransvectionUnit i c)⁻¹ =
      positiveLongRootTransvectionUnit i (-c) := by
  simpa only [positiveLongRootTransvectionHom_apply, toAdd_ofAdd, toAdd_inv] using
    (map_inv (positiveLongRootTransvectionHom (R := R) i) (Multiplicative.ofAdd c)).symm

/-- Adding parameters multiplies negative long-root transvections. -/
@[simp]
theorem negativeLongRootTransvectionUnit_add (i : Fin m) (c d : R) :
    negativeLongRootTransvectionUnit i (c + d) =
      negativeLongRootTransvectionUnit i c * negativeLongRootTransvectionUnit i d := by
  simpa only [negativeLongRootTransvectionHom_apply, toAdd_ofAdd, toAdd_mul] using
    ((negativeLongRootTransvectionHom (R := R) i).map_mul
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd d))

/-- Inverting a negative long-root transvection negates its parameter. -/
@[simp]
theorem negativeLongRootTransvectionUnit_inv (i : Fin m) (c : R) :
    (negativeLongRootTransvectionUnit i c)⁻¹ =
      negativeLongRootTransvectionUnit i (-c) := by
  simpa only [negativeLongRootTransvectionHom_apply, toAdd_ofAdd, toAdd_inv] using
    (map_inv (negativeLongRootTransvectionHom (R := R) i) (Multiplicative.ofAdd c)).symm

/-- Positive long-root transvections are natural in the coefficient ring. -/
@[simp]
theorem map_positiveLongRootTransvectionUnit {S : Type*} [CommRing S]
    (f : R →+* S) (i : Fin m) (c : R) :
    GLSymplecticFin.map m R f (positiveLongRootTransvectionUnit i c) =
      positiveLongRootTransvectionUnit i (f c) := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, coe_positiveLongRootTransvectionUnit,
    coe_positiveLongRootTransvectionUnit, map_transvectionUnit]

/-- Negative long-root transvections are natural in the coefficient ring. -/
@[simp]
theorem map_negativeLongRootTransvectionUnit {S : Type*} [CommRing S]
    (f : R →+* S) (i : Fin m) (c : R) :
    GLSymplecticFin.map m R f (negativeLongRootTransvectionUnit i c) =
      negativeLongRootTransvectionUnit i (f c) := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, coe_negativeLongRootTransvectionUnit,
    coe_negativeLongRootTransvectionUnit, map_transvectionUnit]

/-- Distinct parameters give distinct positive long-root transvections. -/
theorem positiveLongRootTransvectionUnit_injective (i : Fin m) :
    Function.Injective (positiveLongRootTransvectionUnit (R := R) i) :=
  fun _ _ h => transvectionUnit_injective (finSumFinEquiv_inl_ne_inr i i)
    (congrArg (fun g : GLSymplecticFin m R => (g : GL (Fin (m + m)) R)) h)

/-- Distinct parameters give distinct negative long-root transvections. -/
theorem negativeLongRootTransvectionUnit_injective (i : Fin m) :
    Function.Injective (negativeLongRootTransvectionUnit (R := R) i) :=
  fun _ _ h => transvectionUnit_injective (finSumFinEquiv_inr_ne_inl i i)
    (congrArg (fun g : GLSymplecticFin m R => (g : GL (Fin (m + m)) R)) h)

/-! ### Short-root elements -/

/-- The two indices of the first transvection defining `x_{eᵢ-eⱼ}` are distinct. -/
theorem differenceShortRoot_first_indices_ne {i j : Fin m} (hij : i ≠ j) :
    (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i) ≠
      finSumFinEquiv (Sum.inl j) :=
  (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)).injective.ne
    (Sum.inl_injective.ne hij)

/-- The two indices of the second transvection defining `x_{eᵢ-eⱼ}` are distinct. -/
theorem differenceShortRoot_second_indices_ne {i j : Fin m} (hij : i ≠ j) :
    (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j) ≠
      finSumFinEquiv (Sum.inr i) :=
  (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)).injective.ne
    (Sum.inr_injective.ne hij.symm)

/-- In sum coordinates, the two elementary matrices defining a difference-root element form a
block-diagonal pair of transvections. -/
theorem coe_differenceShortRootTransvectionUnits {i j : Fin m} (hij : i ≠ j) (c : R) :
    ((transvectionUnit (Sum.inl_injective.ne hij) c *
        transvectionUnit (Sum.inr_injective.ne hij.symm) (-c) :
          GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
      Matrix.fromBlocks (Matrix.transvection i j c) 0 0
        (Matrix.transvection j i (-c)) := by
  simp only [Units.val_mul, coe_transvectionUnit, Matrix.transvection, Matrix.mul_add,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.single_mul_single_of_ne _ _ _ _ Sum.inl_ne_inr]
  ext a b
  cases a <;> cases b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Matrix.zero_apply, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, ite_false, add_zero]

private theorem differenceShortRoot_mem {i j : Fin m} (hij : i ≠ j) (c : R) :
    transvectionUnit (differenceShortRoot_first_indices_ne hij) c *
        transvectionUnit (differenceShortRoot_second_indices_ne hij) (-c) ∈
      GLSymplecticFin m R := by
  rw [GLSymplecticFin, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [map_mul]
  have hfirst := reindexGL_transvectionUnit (R := R)
    (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) c
  have hsecond := reindexGL_transvectionUnit (R := R)
    (Sum.inr j) (Sum.inr i) (Sum.inr_injective.ne hij.symm) (-c)
  rw [hfirst, hsecond, GLSymplectic.mem_iff_mem_symplecticGroup]
  rw [coe_differenceShortRootTransvectionUnits hij c]
  apply GLSymplectic.fromBlocks_diagonal_mem
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.single_mul_single_of_ne _ _ _ _ hij]
  rw [add_zero, add_assoc, ← Matrix.single_add]
  simp

private theorem positiveSumShortRoot_mem {i j : Fin m} (c : R) :
    transvectionUnit (finSumFinEquiv_inl_ne_inr i j) c *
        transvectionUnit (finSumFinEquiv_inl_ne_inr j i) c ∈
      GLSymplecticFin m R := by
  rw [GLSymplecticFin, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [map_mul]
  have hfirst := reindexGL_transvectionUnit (R := R)
    (Sum.inl i) (Sum.inr j) Sum.inl_ne_inr c
  have hsecond := reindexGL_transvectionUnit (R := R)
    (Sum.inl j) (Sum.inr i) Sum.inl_ne_inr c
  rw [hfirst, hsecond, GLSymplectic.mem_iff_mem_symplecticGroup]
  have hmatrix :
      ((transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : Fin m ⊕ Fin m) ≠ Sum.inr j) c *
          transvectionUnit (Sum.inl_ne_inr : (Sum.inl j : Fin m ⊕ Fin m) ≠ Sum.inr i) c :
            GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
        Matrix.fromBlocks 1 (Matrix.single i j c + Matrix.single j i c) 0 1 := by
    simp only [Units.val_mul, coe_transvectionUnit, Matrix.transvection, Matrix.mul_add,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.single_mul_single_of_ne _ _ _ _ Sum.inr_ne_inl]
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.single, Matrix.fromBlocks, Matrix.one_apply, add_comm]
  rw [hmatrix]
  exact GLSymplectic.fromBlocks_upper_mem _
    (by simp [Matrix.transpose_add, Matrix.transpose_single, add_comm])

private theorem negativeSumShortRoot_mem {i j : Fin m} (c : R) :
    transvectionUnit (finSumFinEquiv_inr_ne_inl i j) c *
        transvectionUnit (finSumFinEquiv_inr_ne_inl j i) c ∈
      GLSymplecticFin m R := by
  rw [GLSymplecticFin, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [map_mul]
  have hfirst := reindexGL_transvectionUnit (R := R)
    (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl c
  have hsecond := reindexGL_transvectionUnit (R := R)
    (Sum.inr j) (Sum.inl i) Sum.inr_ne_inl c
  rw [hfirst, hsecond, GLSymplectic.mem_iff_mem_symplecticGroup]
  have hmatrix :
      ((transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : Fin m ⊕ Fin m) ≠ Sum.inl j) c *
          transvectionUnit (Sum.inr_ne_inl : (Sum.inr j : Fin m ⊕ Fin m) ≠ Sum.inl i) c :
            GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) =
        Matrix.fromBlocks 1 0 (Matrix.single i j c + Matrix.single j i c) 1 := by
    simp only [Units.val_mul, coe_transvectionUnit, Matrix.transvection, Matrix.mul_add,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.single_mul_single_of_ne _ _ _ _ Sum.inl_ne_inr]
    ext a b
    cases a <;> cases b <;>
      simp [Matrix.single, Matrix.fromBlocks, Matrix.one_apply, add_comm]
  rw [hmatrix]
  exact GLSymplectic.fromBlocks_lower_mem _
    (by simp [Matrix.transpose_add, Matrix.transpose_single, add_comm])

/-- The one-parameter subgroup attached to the short root `eᵢ-eⱼ`. -/
def differenceShortRootHom {i j : Fin m} (hij : i ≠ j) :
    Multiplicative R →* GLSymplecticFin m R :=
  MonoidHom.codRestrict
    (commutingTransvectionPairHom
      (differenceShortRoot_first_indices_ne hij)
      (differenceShortRoot_second_indices_ne hij)
      (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inr_ne_inl i i)
      (invMonoidHom : Multiplicative R →* Multiplicative R))
    (GLSymplecticFin m R) (fun c ↦ by
      simpa only [commutingTransvectionPairHom_apply, invMonoidHom_apply, toAdd_inv] using
        differenceShortRoot_mem hij c.toAdd)

/-- The paired one-parameter subgroup
`c ↦ (1 + c E_{i,m+j})(1 + c E_{j,m+i})`.

When `i ≠ j`, this is the short-root subgroup for `eᵢ+eⱼ`; on the diagonal it is the
corresponding doubled long-root parametrization. -/
private def positiveSumPairedHom (i j : Fin m) :
    Multiplicative R →* GLSymplecticFin m R :=
  MonoidHom.codRestrict
    (commutingTransvectionPairHom
      (finSumFinEquiv_inl_ne_inr i j) (finSumFinEquiv_inl_ne_inr j i)
      (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl i i)
      (MonoidHom.id _))
    (GLSymplecticFin m R) (fun c ↦ by
      simpa only [commutingTransvectionPairHom_apply, MonoidHom.id_apply] using
        positiveSumShortRoot_mem c.toAdd)

/-- The paired one-parameter subgroup
`c ↦ (1 + c E_{m+i,j})(1 + c E_{m+j,i})`.

When `i ≠ j`, this is the short-root subgroup for `-eᵢ-eⱼ`; on the diagonal it is the
corresponding doubled long-root parametrization. -/
private def negativeSumPairedHom (i j : Fin m) :
    Multiplicative R →* GLSymplecticFin m R :=
  MonoidHom.codRestrict
    (commutingTransvectionPairHom
      (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr i i)
      (MonoidHom.id _))
    (GLSymplecticFin m R) (fun c ↦ by
      simpa only [commutingTransvectionPairHom_apply, MonoidHom.id_apply] using
        negativeSumShortRoot_mem c.toAdd)

/-- The one-parameter subgroup attached to the short root `eᵢ+eⱼ`. -/
def positiveSumShortRootHom {i j : Fin m} (_hij : i ≠ j) :
    Multiplicative R →* GLSymplecticFin m R :=
  positiveSumPairedHom i j

/-- The one-parameter subgroup attached to the short root `-eᵢ-eⱼ`. -/
def negativeSumShortRootHom {i j : Fin m} (_hij : i ≠ j) :
    Multiplicative R →* GLSymplecticFin m R :=
  negativeSumPairedHom i j

/-- The symplectic short-root element
`x_{eᵢ-eⱼ}(c) = (1 + c E_{i,j})(1 - c E_{m+j,m+i})`. -/
def differenceShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin m R :=
  differenceShortRootHom hij (Multiplicative.ofAdd c)

/-- The paired symplectic element
`(1 + c E_{i,m+j})(1 + c E_{j,m+i})`, which is `x_{eᵢ+eⱼ}(c)` when `i ≠ j`. -/
def positiveSumShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin m R :=
  positiveSumShortRootHom hij (Multiplicative.ofAdd c)

/-- The paired symplectic element
`(1 + c E_{m+i,j})(1 + c E_{m+j,i})`, which is `x_{-eᵢ-eⱼ}(c)` when `i ≠ j`. -/
def negativeSumShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin m R :=
  negativeSumShortRootHom hij (Multiplicative.ofAdd c)

/-- The difference short-root homomorphism evaluates to its paired transvection. -/
@[simp]
theorem differenceShortRootHom_apply {i j : Fin m} (hij : i ≠ j)
    (c : Multiplicative R) :
    differenceShortRootHom hij c =
      differenceShortRootUnit hij c.toAdd := by
  rw [differenceShortRootUnit]
  rw [ofAdd_toAdd]

/-- The positive-sum short-root homomorphism evaluates to its paired transvection. -/
@[simp]
theorem positiveSumShortRootHom_apply {i j : Fin m} (hij : i ≠ j) (c : Multiplicative R) :
    positiveSumShortRootHom hij c =
      positiveSumShortRootUnit hij c.toAdd := by
  rw [positiveSumShortRootUnit]
  rw [ofAdd_toAdd]

/-- The negative-sum short-root homomorphism evaluates to its paired transvection. -/
@[simp]
theorem negativeSumShortRootHom_apply {i j : Fin m} (hij : i ≠ j) (c : Multiplicative R) :
    negativeSumShortRootHom hij c =
      negativeSumShortRootUnit hij c.toAdd := by
  rw [negativeSumShortRootUnit]
  rw [ofAdd_toAdd]

/-- The general-linear matrix underlying `x_{eᵢ-eⱼ}(c)` is its two-transvection formula. -/
@[simp]
theorem coe_differenceShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    ((differenceShortRootUnit hij c : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      transvectionUnit (differenceShortRoot_first_indices_ne hij) c *
        transvectionUnit (differenceShortRoot_second_indices_ne hij) (-c) := by
  simp [differenceShortRootUnit, differenceShortRootHom,
    commutingTransvectionPairHom_apply]

/-- The general-linear matrix underlying `x_{eᵢ+eⱼ}(c)` is its two-transvection formula. -/
@[simp]
theorem coe_positiveSumShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    ((positiveSumShortRootUnit hij c : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      transvectionUnit (finSumFinEquiv_inl_ne_inr i j) c *
        transvectionUnit (finSumFinEquiv_inl_ne_inr j i) c := by
  simp [positiveSumShortRootUnit, positiveSumShortRootHom, positiveSumPairedHom,
    commutingTransvectionPairHom_apply]

/-- The general-linear matrix underlying `x_{-eᵢ-eⱼ}(c)` is its two-transvection formula. -/
@[simp]
theorem coe_negativeSumShortRootUnit {i j : Fin m} (hij : i ≠ j) (c : R) :
    ((negativeSumShortRootUnit hij c : GLSymplecticFin m R) : GL (Fin (m + m)) R) =
      transvectionUnit (finSumFinEquiv_inr_ne_inl i j) c *
        transvectionUnit (finSumFinEquiv_inr_ne_inl j i) c := by
  simp [negativeSumShortRootUnit, negativeSumShortRootHom, negativeSumPairedHom,
    commutingTransvectionPairHom_apply]

/-- Swapping the two indices does not change a positive-sum short-root homomorphism. -/
theorem positiveSumShortRootHom_swap {i j : Fin m} (hij : i ≠ j) :
    positiveSumShortRootHom (R := R) hij = positiveSumShortRootHom hij.symm := by
  apply MonoidHom.ext
  intro c
  rw [positiveSumShortRootHom_apply, positiveSumShortRootHom_apply]
  apply Subtype.ext
  rw [coe_positiveSumShortRootUnit, coe_positiveSumShortRootUnit]
  exact (commute_transvectionUnit
    (finSumFinEquiv_inl_ne_inr i j) (finSumFinEquiv_inl_ne_inr j i)
    (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl i i)
    c.toAdd c.toAdd).eq

/-- Swapping the two indices does not change a negative-sum short-root homomorphism. -/
theorem negativeSumShortRootHom_swap {i j : Fin m} (hij : i ≠ j) :
    negativeSumShortRootHom (R := R) hij = negativeSumShortRootHom hij.symm := by
  apply MonoidHom.ext
  intro c
  rw [negativeSumShortRootHom_apply, negativeSumShortRootHom_apply]
  apply Subtype.ext
  rw [coe_negativeSumShortRootUnit, coe_negativeSumShortRootUnit]
  exact (commute_transvectionUnit
    (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inr_ne_inl j i)
    (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr i i)
    c.toAdd c.toAdd).eq

/-- Difference short-root elements commute with change of coefficient ring. -/
@[simp]
theorem map_differenceShortRootUnit {S : Type*} [CommRing S]
    (f : R →+* S) {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin.map m R f (differenceShortRootUnit hij c) =
      differenceShortRootUnit hij (f c) := by
  apply Subtype.ext
  simp

/-- Positive-sum short-root elements commute with change of coefficient ring. -/
@[simp]
theorem map_positiveSumShortRootUnit {S : Type*} [CommRing S]
    (f : R →+* S) {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin.map m R f (positiveSumShortRootUnit hij c) =
      positiveSumShortRootUnit hij (f c) := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, coe_positiveSumShortRootUnit,
    coe_positiveSumShortRootUnit, map_mul, map_transvectionUnit,
    map_transvectionUnit]

/-- Negative-sum short-root elements commute with change of coefficient ring. -/
@[simp]
theorem map_negativeSumShortRootUnit {S : Type*} [CommRing S]
    (f : R →+* S) {i j : Fin m} (hij : i ≠ j) (c : R) :
    GLSymplecticFin.map m R f (negativeSumShortRootUnit hij c) =
      negativeSumShortRootUnit hij (f c) := by
  apply Subtype.ext
  rw [GLSymplecticFin.coe_map, coe_negativeSumShortRootUnit,
    coe_negativeSumShortRootUnit, map_mul, map_transvectionUnit,
    map_transvectionUnit]

/-- The `(i,j)` entry recovers the parameter of a difference short-root element. -/
theorem differenceShortRootUnit_apply_inl_inl {i j : Fin m} (hij : i ≠ j) (c : R) :
    (((differenceShortRootUnit hij c : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = c := by
  rw [coe_differenceShortRootUnit, Units.val_mul,
    coe_transvectionUnit, coe_transvectionUnit]
  rw [Matrix.mul_transvection_apply_of_ne
    (hb := finSumFinEquiv_inl_ne_inr j i)]
  simp [Matrix.transvection, Matrix.single, hij]

/-- The `(i,m+j)` entry recovers the parameter of a positive-sum short-root element. -/
theorem positiveSumShortRootUnit_apply_inl_inr {i j : Fin m} (hij : i ≠ j) (c : R) :
    (((positiveSumShortRootUnit hij c : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = c := by
  rw [coe_positiveSumShortRootUnit, Units.val_mul,
    coe_transvectionUnit, coe_transvectionUnit]
  rw [Matrix.mul_transvection_apply_of_ne
    (hb := differenceShortRoot_second_indices_ne hij)]
  have hcross : Fin.castAdd m i ≠ j.addNat m := by
    simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.natAdd_eq_addNat] using
      finSumFinEquiv_inl_ne_inr i j
  simp [Matrix.transvection, Matrix.single, hcross]

/-- The `(m+i,j)` entry recovers the parameter of a negative-sum short-root element. -/
theorem negativeSumShortRootUnit_apply_inr_inl {i j : Fin m} (hij : i ≠ j) (c : R) :
    (((negativeSumShortRootUnit hij c : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
      (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c := by
  rw [coe_negativeSumShortRootUnit, Units.val_mul,
    coe_transvectionUnit, coe_transvectionUnit]
  rw [Matrix.mul_transvection_apply_of_ne
    (hb := differenceShortRoot_first_indices_ne hij.symm)]
  have hcross : i.addNat m ≠ Fin.castAdd m j := by
    simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.natAdd_eq_addNat] using
      finSumFinEquiv_inr_ne_inl i j
  simp [Matrix.transvection, Matrix.single, hcross]

/-- Distinct parameters give distinct difference short-root elements. -/
theorem differenceShortRootUnit_injective {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (differenceShortRootUnit (R := R) hij) := by
  intro c d h
  simpa only [differenceShortRootUnit_apply_inl_inl hij] using congrArg
    (fun g : GLSymplecticFin m R ↦
      (((g : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)))) h

/-- Distinct parameters give distinct positive-sum short-root elements. -/
theorem positiveSumShortRootUnit_injective {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (positiveSumShortRootUnit (R := R) hij) := by
  intro c d h
  simpa only [positiveSumShortRootUnit_apply_inl_inr hij] using congrArg
    (fun g : GLSymplecticFin m R ↦
      (((g : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)))) h

/-- Distinct parameters give distinct negative-sum short-root elements. -/
theorem negativeSumShortRootUnit_injective {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (negativeSumShortRootUnit (R := R) hij) := by
  intro c d h
  simpa only [negativeSumShortRootUnit_apply_inr_inl hij] using congrArg
    (fun g : GLSymplecticFin m R ↦
      (((g : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)
        (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)))) h

/-- The three uniform families of short roots in the standard type-`Cₘ` realization.

The difference family is ordered: swapping `i` and `j` changes `eᵢ-eⱼ` to its negative. The two
sum families are symmetric in `i` and `j`. -/
inductive ShortRootFamily
  | difference
  | positiveSum
  | negativeSum
  deriving DecidableEq

namespace ShortRootFamily

/-- The matrix one-parameter subgroup belonging to a family of short roots. -/
def hom (family : ShortRootFamily) {i j : Fin m} (hij : i ≠ j) :
    Multiplicative R →* GLSymplecticFin m R :=
  match family with
  | difference => differenceShortRootHom hij
  | positiveSum => positiveSumShortRootHom hij
  | negativeSum => negativeSumShortRootHom hij

/-- The difference family specializes to the concrete difference short-root homomorphism. -/
@[simp]
theorem hom_difference {i j : Fin m} (hij : i ≠ j) :
    (ShortRootFamily.difference).hom (R := R) hij = differenceShortRootHom hij := by
  rw [hom]

/-- The positive-sum family specializes to the concrete positive-sum short-root homomorphism. -/
@[simp]
theorem hom_positiveSum {i j : Fin m} (hij : i ≠ j) :
    (ShortRootFamily.positiveSum).hom (R := R) hij = positiveSumShortRootHom hij := by
  rw [hom]

/-- The negative-sum family specializes to the concrete negative-sum short-root homomorphism. -/
@[simp]
theorem hom_negativeSum {i j : Fin m} (hij : i ≠ j) :
    (ShortRootFamily.negativeSum).hom (R := R) hij = negativeSumShortRootHom hij := by
  rw [hom]

/-- Evaluating a short-root one-parameter subgroup commutes with change of coefficients. -/
@[simp]
theorem map_hom_apply {S : Type v} [CommRing S] (family : ShortRootFamily)
    (f : R →+* S) {i j : Fin m} (hij : i ≠ j) (c : Multiplicative R) :
    GLSymplecticFin.map m R f (family.hom hij c) =
      family.hom hij (Multiplicative.ofAdd (f c.toAdd)) := by
  cases family <;> simp [hom]

/-- Every short-root one-parameter subgroup is injective. -/
theorem hom_injective (family : ShortRootFamily) {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (family.hom (R := R) hij) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  cases family
  · apply differenceShortRootUnit_injective hij
    simpa only [hom_difference, differenceShortRootHom_apply] using h
  · apply positiveSumShortRootUnit_injective hij
    simpa only [hom_positiveSum, positiveSumShortRootHom_apply] using h
  · apply negativeSumShortRootUnit_injective hij
    simpa only [hom_negativeSum, negativeSumShortRootHom_apply] using h

end ShortRootFamily

/-- An extensional index for the root one-parameter subgroups of the standard symplectic group.

Difference roots retain their ordered pair of indices. The symmetric positive- and negative-sum
roots store their indices in increasing order, so each root has only one index. -/
inductive RootSubgroupIndex (m : ℕ)
  | positiveLong (i : Fin m)
  | negativeLong (i : Fin m)
  | difference (i j : Fin m) (hij : i ≠ j)
  | positiveSum (i j : Fin m) (hij : i < j)
  | negativeSum (i j : Fin m) (hij : i < j)

namespace RootSubgroupIndex

/-- The canonical root index for a short-root family and two distinct indices. Sum roots are
normalized to increasing index order. -/
def short (family : ShortRootFamily) (i j : Fin m) (hij : i ≠ j) :
    RootSubgroupIndex m :=
  match family with
  | .difference => .difference i j hij
  | .positiveSum =>
      if h : i < j then .positiveSum i j h
      else .positiveSum j i (lt_of_le_of_ne (le_of_not_gt h) hij.symm)
  | .negativeSum =>
      if h : i < j then .negativeSum i j h
      else .negativeSum j i (lt_of_le_of_ne (le_of_not_gt h) hij.symm)

/-- The canonical short-root index leaves a difference root ordered. -/
@[simp]
theorem short_difference (i j : Fin m) (hij : i ≠ j) :
    short .difference i j hij = .difference i j hij := by
  rw [short]

/-- Increasing indices are already the canonical order for a positive sum root. -/
@[simp]
theorem short_positiveSum_of_lt (i j : Fin m) (hij : i < j) :
    short .positiveSum i j hij.ne = .positiveSum i j hij := by
  rw [short]
  simp only [hij, ↓reduceDIte]

/-- Increasing indices are already the canonical order for a negative sum root. -/
@[simp]
theorem short_negativeSum_of_lt (i j : Fin m) (hij : i < j) :
    short .negativeSum i j hij.ne = .negativeSum i j hij := by
  rw [short]
  simp only [hij, ↓reduceDIte]

/-- Swapping the inputs gives the same canonical positive-sum root index. -/
theorem short_positiveSum_swap (i j : Fin m) (hij : i ≠ j) :
    short .positiveSum i j hij = short .positiveSum j i hij.symm := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [short, h, not_lt_of_ge h.le]
  · simp [short, h, not_lt_of_ge h.le]

/-- Swapping the inputs gives the same canonical negative-sum root index. -/
theorem short_negativeSum_swap (i j : Fin m) (hij : i ≠ j) :
    short .negativeSum i j hij = short .negativeSum j i hij.symm := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [short, h, not_lt_of_ge h.le]
  · simp [short, h, not_lt_of_ge h.le]

/-- The matrix one-parameter subgroup selected by a symplectic root index. -/
def hom (root : RootSubgroupIndex m) : Multiplicative R →* GLSymplecticFin m R :=
  match root with
  | positiveLong i => positiveLongRootTransvectionHom i
  | negativeLong i => negativeLongRootTransvectionHom i
  | difference _ _ hij => differenceShortRootHom hij
  | positiveSum _ _ hij => positiveSumShortRootHom hij.ne
  | negativeSum _ _ hij => negativeSumShortRootHom hij.ne

/-- The positive-long constructor selects the positive long-root homomorphism. -/
@[simp]
theorem hom_positiveLong (i : Fin m) :
    (RootSubgroupIndex.positiveLong i).hom (R := R) = positiveLongRootTransvectionHom i := by
  rw [hom]

/-- The negative-long constructor selects the negative long-root homomorphism. -/
@[simp]
theorem hom_negativeLong (i : Fin m) :
    (RootSubgroupIndex.negativeLong i).hom (R := R) = negativeLongRootTransvectionHom i := by
  rw [hom]

/-- The difference-root constructor selects the corresponding difference-root homomorphism. -/
@[simp]
theorem hom_difference (i j : Fin m) (hij : i ≠ j) :
    (RootSubgroupIndex.difference i j hij).hom (R := R) = differenceShortRootHom hij := by
  rw [hom]

/-- The positive-sum constructor selects the corresponding positive-sum homomorphism. -/
@[simp]
theorem hom_positiveSum (i j : Fin m) (hij : i < j) :
    (RootSubgroupIndex.positiveSum i j hij).hom (R := R) =
      positiveSumShortRootHom hij.ne := by
  rw [hom]

/-- The negative-sum constructor selects the corresponding negative-sum homomorphism. -/
@[simp]
theorem hom_negativeSum (i j : Fin m) (hij : i < j) :
    (RootSubgroupIndex.negativeSum i j hij).hom (R := R) =
      negativeSumShortRootHom hij.ne := by
  rw [hom]

/-- The short constructor selects its family's short-root homomorphism. -/
@[simp]
theorem hom_short (family : ShortRootFamily) (i j : Fin m) (hij : i ≠ j) :
    (RootSubgroupIndex.short family i j hij).hom (R := R) = family.hom hij := by
  cases family with
  | difference => rfl
  | positiveSum =>
      rw [short]
      split
      · rfl
      · rw [hom, ShortRootFamily.hom]
        exact (positiveSumShortRootHom_swap (R := R) hij).symm
  | negativeSum =>
      rw [short]
      split
      · rfl
      · rw [hom, ShortRootFamily.hom]
        exact (negativeSumShortRootHom_swap (R := R) hij).symm

/-- Evaluating any root one-parameter subgroup commutes with change of coefficients. -/
@[simp]
theorem map_hom_apply {S : Type v} [CommRing S] (root : RootSubgroupIndex m)
    (f : R →+* S) (c : Multiplicative R) :
    GLSymplecticFin.map m R f (root.hom c) =
      root.hom (Multiplicative.ofAdd (f c.toAdd)) := by
  cases root with
  | positiveLong i => simp [hom]
  | negativeLong i => simp [hom]
  | difference i j hij => simp [hom]
  | positiveSum i j hij => simp [hom]
  | negativeSum i j hij => simp [hom]

/-- Every symplectic root one-parameter subgroup is injective. -/
theorem hom_injective (root : RootSubgroupIndex m) :
    Function.Injective (root.hom (R := R)) := by
  intro c d h
  cases root with
  | positiveLong i =>
      apply Multiplicative.toAdd.injective
      apply positiveLongRootTransvectionUnit_injective i
      simpa only [hom, positiveLongRootTransvectionHom_apply] using h
  | negativeLong i =>
      apply Multiplicative.toAdd.injective
      apply negativeLongRootTransvectionUnit_injective i
      simpa only [hom, negativeLongRootTransvectionHom_apply] using h
  | difference i j hij =>
      exact (ShortRootFamily.difference).hom_injective hij h
  | positiveSum i j hij =>
      exact (ShortRootFamily.positiveSum).hom_injective hij.ne h
  | negativeSum i j hij =>
      exact (ShortRootFamily.negativeSum).hom_injective hij.ne h

end RootSubgroupIndex

end GLSymplecticFin

end FinIndex

end TauCeti
