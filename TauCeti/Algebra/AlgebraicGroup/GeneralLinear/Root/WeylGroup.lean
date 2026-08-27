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

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances Layer 7, "Root datum `(G, T)` with its Weyl group", of the ReductiveGroups roadmap
through the group-of-points Weyl group of the standard split maximal torus of `GL_n`; the
scheme-level identification is not addressed here.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] [Nontrivial kˣ] {n : ℕ}

private theorem diagonalRootDatum_eq_coordinateRootDatum (n : ℕ) :
    diagonalRootDatum.{u} n = SplitTorus.coordinateRootDatum (ULift.{u} (Fin n)) := by
  rw [diagonalRootDatum]

/-- Transport between the Weyl groups across the opaque `diagonalRootDatum` wrapper. -/
noncomputable def diagonalWeylGroupMulEquivCoordinateWeylGroup (n : ℕ) :
    (diagonalRootDatum.{u} n).weylGroup ≃*
      (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))).weylGroup := by
  rw [diagonalRootDatum_eq_coordinateRootDatum]

private theorem diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_smul_apply
    (w : (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))).weylGroup)
    (x : ULift.{u} (Fin n) →₀ ℤ) (a : ULift.{u} (Fin n)) :
    ((diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm w • x) a =
      (w • x) a := by
  have h := diagonalRootDatum_eq_coordinateRootDatum.{u} n
  cases h
  rfl

private theorem diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_indexEquiv_apply
    (w : (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))).weylGroup)
    (p : DiagonalRootIndex n) :
    ((diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm w).1.indexEquiv p =
      w.1.indexEquiv p := by
  have h := diagonalRootDatum_eq_coordinateRootDatum.{u} n
  cases h
  rfl

private theorem diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_ofIdx
    (p : DiagonalRootIndex n) :
    (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
        (RootPairing.weylGroup.ofIdx
          (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))) p) =
      RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} n) p := by
  have h := diagonalRootDatum_eq_coordinateRootDatum.{u} n
  cases h
  rfl

/-- **The normalizer quotient of the diagonal torus is the Weyl group of its coordinate root
datum.** The intermediate permutation is transported from `Fin n` to the universe-lifted
coordinate type used by `diagonalRootDatum`. -/
noncomputable def diagonalNormalizerQuotientMulEquivWeylGroup (k : Type u) [Field k]
    [Nontrivial kˣ] (n : ℕ) :
    Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n) ≃*
      (diagonalRootDatum.{u} n).weylGroup :=
  ((diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).trans <|
    Equiv.ulift.symm.permCongrHom.trans SplitTorus.coordinatePermMulEquivWeylGroup).trans <|
      (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm

/-- On a normalizer representative, the Weyl-group equivalence is the root-datum automorphism
induced by its coordinate permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_mk
    (g : Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (g : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n)) =
      (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
        (SplitTorus.coordinatePermMulEquivWeylGroup
          (Equiv.ulift.symm.permCongrHom
            (diagonalNormalizerPerm (k := k) (n := n) g))) := by
  simp only [diagonalNormalizerQuotientMulEquivWeylGroup, MulEquiv.trans_apply,
    Equiv.permCongrHom_coe, diagonalNormalizerQuotientMulEquivPerm_mk]

/-- A permutation matrix represents the Weyl element induced by the same coordinate
permutation, transported to the universe-lifted root coordinates. -/
theorem diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL
    (e : Equiv.Perm (Fin n)) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (⟨permutationGL (k := k) e, permutationGL_mem_normalizer e⟩ :
          Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) =
      (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
        (SplitTorus.coordinatePermMulEquivWeylGroup
          (Equiv.ulift.symm.permCongrHom e)) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup_mk,
    diagonalNormalizerPerm_permutationGL]

/-- The Weyl element represented by a normalizer class acts on the character lattice by moving
each coordinate through its associated permutation; equivalently, its value at a coordinate is
the original value at the inverse image of that coordinate. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_smul_apply
    (q : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n))
    (x : ULift.{u} (Fin n) →₀ ℤ) (a : ULift.{u} (Fin n)) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n q • x) a =
      x (ULift.up
        ((diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n) q).symm a.down)) := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  simp only [MulEquiv.trans_apply, Equiv.permCongrHom_coe,
    diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_smul_apply,
    SplitTorus.coordinatePermMulEquivWeylGroup_smul_apply]
  rw [Equiv.permCongr_def]
  rfl

/-- The Weyl element represented by a normalizer class applies the associated coordinate
permutation simultaneously to both entries of a root index. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_indexEquiv_apply
    (q : Subgroup.normalizerQuotient (TauCeti.diagonalTorus k n))
    (p : DiagonalRootIndex n) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n q).1.indexEquiv p =
      SplitTorus.coordinatePermRootIndex
        (Equiv.ulift.symm.permCongrHom
          (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n) q)) p := by
  rw [diagonalNormalizerQuotientMulEquivWeylGroup]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_indexEquiv_apply]
  exact SplitTorus.coordinatePermMulEquivWeylGroup_indexEquiv_apply _ _

/-- A transposition matrix maps to reflection in the corresponding diagonal root. -/
theorem diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL_swap
    (i j : Fin n) (hij : i ≠ j) :
    diagonalNormalizerQuotientMulEquivWeylGroup k n
        (⟨permutationGL (k := k) (Equiv.swap i j),
          permutationGL_mem_normalizer (Equiv.swap i j)⟩ :
          Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) =
      RootPairing.weylGroup.ofIdx
        (diagonalRootDatum.{u} n)
        (⟨(ULift.up i, ULift.up j), fun h ↦ hij (congrArg ULift.down h)⟩ :
          DiagonalRootIndex n) := by
  have hijLift : (ULift.up i : ULift.{u} (Fin n)) ≠ ULift.up j :=
    fun h ↦ hij (congrArg ULift.down h)
  have hlift :
      (Equiv.ulift.{u, 0}.symm : Fin n ≃ ULift.{u} (Fin n)).permCongr
          (Equiv.swap i j) =
        Equiv.swap (ULift.up i) (ULift.up j) := by
    rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
    simp
  rw [diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL]
  calc
    (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
          (SplitTorus.coordinatePermMulEquivWeylGroup
            (Equiv.ulift.symm.permCongrHom (Equiv.swap i j))) =
        (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
          (SplitTorus.coordinatePermMulEquivWeylGroup
            (Equiv.swap (ULift.up i) (ULift.up j))) :=
      congrArg ((diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm ∘
        SplitTorus.coordinatePermMulEquivWeylGroup) hlift
    _ = (diagonalWeylGroupMulEquivCoordinateWeylGroup.{u} n).symm
        (RootPairing.weylGroup.ofIdx
          (SplitTorus.coordinateRootDatum (ULift.{u} (Fin n)))
          (⟨(ULift.up i, ULift.up j), hijLift⟩ : DiagonalRootIndex n)) := by
      congr 1
      exact SplitTorus.coordinatePermMulEquivWeylGroup_swap _ _ _
    _ = _ := diagonalWeylGroupMulEquivCoordinateWeylGroup_symm_ofIdx _

/-- Conversely, the reflection in `e_i - e_j` corresponds to the normalizer class of the
transposition matrix swapping the two coordinate lines. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivWeylGroup_symm_ofIdx
    (i j : Fin n) (hij : i ≠ j) :
    (diagonalNormalizerQuotientMulEquivWeylGroup k n).symm
        (RootPairing.weylGroup.ofIdx
          (diagonalRootDatum.{u} n)
          (⟨(ULift.up i, ULift.up j), fun h ↦ hij (congrArg ULift.down h)⟩ :
            DiagonalRootIndex n)) =
      (⟨permutationGL (k := k) (Equiv.swap i j),
        permutationGL_mem_normalizer (Equiv.swap i j)⟩ :
        Subgroup.normalizer (TauCeti.diagonalTorus k n : Set (GL (Fin n) k))) := by
  apply (diagonalNormalizerQuotientMulEquivWeylGroup k n).injective
  rw [MulEquiv.apply_symm_apply,
    diagonalNormalizerQuotientMulEquivWeylGroup_permutationGL_swap]

end

end TauCeti.GeneralLinear
