/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Datum
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.WeylGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# The Weyl group of the diagonal torus in the general linear group

For a field `k` with a nontrivial unit group, the normalizer quotient of the diagonal torus in
`GL_n(k)` is the permutation group of the coordinate lines. Independently, the Weyl group of the
diagonal coordinate root datum is the permutation group of its universe-lifted coordinates. This
file identifies those two groups and proves that the identification gives the same actions on the
character lattice and on the roots.

Concretely, the class of a normalizing matrix `g` maps to the root-datum automorphism attached to
`diagonalNormalizerPerm g`. The class of a permutation matrix for the transposition `(i j)` maps
to reflection in the root `e_i - e_j`. Thus the group-of-points normalizer computation and the
coordinate root datum describe the same Weyl group of the standard split torus in `GL_n`.

## Main declarations

* `TauCeti.GeneralLinear.diagonalNormalizerQuotientMulEquivWeylGroup`: the canonical equivalence
  from the diagonal normalizer quotient to the Weyl group of `diagonalRootDatum`.
* `TauCeti.GeneralLinear.diagonalNormalizerQuotientMulEquivWeylGroup_smul_apply`: its action on
  the character lattice.
* `TauCeti.GeneralLinear.diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL_swap`: a
  transposition matrix maps to the corresponding root reflection.
* `TauCeti.GeneralLinear.diagonalNormalizer_mul_diagGL_mul_inv`: conjugation by a normalizer
  element permutes the diagonal coordinates by the same permutation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This completes the Weyl-group identification for the standard split `GL_n` example in Layer 7,
"Root datum `(G, T)` with its Weyl group", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] [Nontrivial kˣ] {n : ℕ}

/-- Transport a permutation of `Fin n` to the universe-lifted coordinate type used by the
diagonal root datum. -/
noncomputable def liftCoordinatePerm (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (ULift.{u} (Fin n)) :=
  Equiv.ulift.symm.permCongr e

@[simp]
theorem liftCoordinatePerm_apply (e : Equiv.Perm (Fin n)) (i : Fin n) :
    liftCoordinatePerm e (ULift.up i) = ULift.up (e i) := by
  simp [liftCoordinatePerm, Equiv.permCongr_apply]

@[simp]
theorem liftCoordinatePerm_symm_apply (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (liftCoordinatePerm e).symm (ULift.up i) = ULift.up (e.symm i) := by
  apply (liftCoordinatePerm e).injective
  rw [Equiv.apply_symm_apply, liftCoordinatePerm_apply]
  exact congrArg ULift.up (e.apply_symm_apply i).symm

/-- **The normalizer quotient of the diagonal torus is the Weyl group of its coordinate root
datum.** The intermediate permutation is transported from `Fin n` to the universe-lifted
coordinate type used by `diagonalRootDatum`. The theorem
`diagonalRootDatum_eq_coordinateRootDatum` identifies the displayed target with the Weyl group
of `diagonalRootDatum n`. -/
noncomputable def diagonalNormalizerQuotientMulEquivWeylGroup (k : Type u) [Field k]
    [Nontrivial kˣ] (n : ℕ) :
    Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n) ≃*
      (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))).weylGroup :=
  (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).trans <|
    Equiv.ulift.symm.permCongrHom.trans SplitTorus.coordinatePermMulEquivWeylGroup

/-- On a normalizer representative, the Weyl-group equivalence is the root-datum automorphism
induced by its coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_mk
    (g : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (g : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n)) =
      SplitTorus.coordinatePermMulEquivWeylGroup
        (liftCoordinatePerm (diagonalNormalizerPerm (k := k) (n := n) g)) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  simp only [MulEquiv.trans_apply, Equiv.permCongrHom_coe]
  refine congrArg (SplitTorus.coordinatePermMulEquivWeylGroup
    (σ := ULift.{u} (Fin n))) ?_
  change Equiv.ulift.symm.permCongr
      (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)
        (g : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n))) = _
  rw [diagonalNormalizerQuotientMulEquivPerm_mk]
  rfl

/-- A permutation matrix represents the Weyl element induced by the same coordinate
permutation, transported to the universe-lifted root coordinates. -/
theorem diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL
    (e : Equiv.Perm (Fin n)) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (⟨permutationGL (k := k) e, permutationGL_mem_normalizer e⟩ :
          Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) =
      SplitTorus.coordinatePermMulEquivWeylGroup (liftCoordinatePerm e) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup_mk,
    diagonalNormalizerPerm_permutationGL]

/-- The Weyl element represented by a normalizer class acts on characters by the inverse of the
associated coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_smul_apply
    (q : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n))
    (x : ULift.{u} (Fin n) →₀ ℤ) (i : Fin n) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n q • x) (ULift.up i) =
      x (ULift.up
        ((diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n) q).symm i)) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  simp only [MulEquiv.trans_apply, Equiv.permCongrHom_coe,
    SplitTorus.coordinatePermMulEquivWeylGroup_smul_apply]
  change x ((liftCoordinatePerm
    (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n) q)).symm
      (ULift.up i)) = _
  rw [liftCoordinatePerm_symm_apply]

/-- The Weyl element represented by a normalizer class applies the associated coordinate
permutation simultaneously to both entries of a root index. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_indexEquiv_apply
    (q : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n))
    (p : DiagonalRootIndex n) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n q).1.indexEquiv p =
      SplitTorus.coordinatePermRootIndex
        (liftCoordinatePerm
          (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n) q)) p := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  exact SplitTorus.coordinatePermMulEquivWeylGroup_indexEquiv_apply _ _

/-- Transporting a coordinate transposition to lifted coordinates gives the corresponding
transposition of the lifted coordinates. -/
theorem liftCoordinatePerm_swap (i j : Fin n) :
    liftCoordinatePerm (Equiv.swap i j) =
      Equiv.swap (ULift.up i) (ULift.up j) := by
  exact Equiv.symm_trans_swap_trans i j Equiv.ulift.symm

/-- A transposition matrix maps to reflection in the corresponding diagonal root. -/
theorem diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL_swap
    (i j : Fin n) (hij : i ≠ j) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (⟨permutationGL (k := k) (Equiv.swap i j),
          permutationGL_mem_normalizer (Equiv.swap i j)⟩ :
          Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) =
      RootPairing.weylGroup.ofIdx
        (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n)))
        (⟨(ULift.up i, ULift.up j), fun h ↦ hij (ULift.up_injective h)⟩ :
          DiagonalRootIndex n) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL,
    liftCoordinatePerm_swap,
    SplitTorus.coordinatePermMulEquivWeylGroup_swap]

/-- Conversely, the reflection in `e_i - e_j` corresponds to the normalizer class of the
transposition matrix swapping the two coordinate lines. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_symm_reflection
    (i j : Fin n) (hij : i ≠ j) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n).symm
        (RootPairing.weylGroup.ofIdx
          (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n)))
          (⟨(ULift.up i, ULift.up j), fun h ↦ hij (ULift.up_injective h)⟩ :
            DiagonalRootIndex n)) =
      (⟨permutationGL (k := k) (Equiv.swap i j),
        permutationGL_mem_normalizer (Equiv.swap i j)⟩ :
        Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) := by
  apply (diagonalNormalizerQuotientMulEquivWeylGroup k n).injective
  rw [MulEquiv.apply_symm_apply,
    diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL_swap]

private theorem diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL
    (g : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)))
    (d : Fin n → kˣ) (e : Equiv.Perm (Fin n))
    (h : (g : GL (Fin n) k) = diagGL d * permutationGL (k := k) e) :
    diagonalNormalizerPerm (k := k) (n := n) g = e := by
  let gd : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) :=
    ⟨diagGL d, Subgroup.le_normalizer
      (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩)⟩
  let ge : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)) :=
    ⟨permutationGL (k := k) e, permutationGL_mem_normalizer e⟩
  have hg : g = gd * ge := Subtype.ext h
  have hgd : diagonalNormalizerPerm (k := k) (n := n) gd = 1 :=
    (diagonalNormalizerPerm_eq_one_iff gd).mpr
      (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩)
  rw [hg, map_mul, hgd, one_mul]
  exact diagonalNormalizerPerm_permutationGL e

/-- **Conjugation by a diagonal-normalizer element permutes the diagonal coordinates by the same
permutation that its Weyl class induces on the root datum.** -/
theorem diagonalNormalizer_mul_diagGL_mul_inv
    (g : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k)))
    (t : Fin n → kˣ) :
    (g : GL (Fin n) k) * diagGL t * (g : GL (Fin n) k)⁻¹ =
      diagGL (fun i ↦ t ((diagonalNormalizerPerm (k := k) (n := n) g).symm i)) := by
  obtain ⟨d, e, hge⟩ := mem_normalizer_diagonalTorus_iff_exists.mp g.property
  have he := diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL g d e hge
  rw [he, hge]
  calc
    (diagGL d * permutationGL (k := k) e) * diagGL t *
          (diagGL d * permutationGL (k := k) e)⁻¹ =
        diagGL d *
          (permutationGL (k := k) e * diagGL t *
            (permutationGL (k := k) e)⁻¹) * (diagGL d)⁻¹ := by group
    _ = diagGL d * diagGL (fun i ↦ t (e⁻¹ i)) * (diagGL d)⁻¹ := by
      rw [permutationGL_mul_diagGL_mul_inv]
    _ = diagGL (fun i ↦ t (e⁻¹ i)) := by
      have hcomm : Commute (diagGL d) (diagGL (fun i ↦ t (e⁻¹ i))) := by
        exact (Commute.all d (fun i ↦ t (e⁻¹ i))).map diagGL
      rw [hcomm.eq]
      simp

end

end TauCeti.GeneralLinear
