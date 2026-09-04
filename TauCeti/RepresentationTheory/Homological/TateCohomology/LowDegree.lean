/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Low-degree Tate cohomology

This file gives the two low-degree descriptions used by the Nakayama map. For a representation
`M` of a finite group, degree zero is the quotient of the invariant submodule by the image of the
norm. For a trivial integral representation `A`, the comparison with first group homology
identifies degree `-2` with `Gᵃᵇ ⊗[ℤ] A`, and hence, for `A = ℤ`, with the additive form of the
abelianization.

The degree-zero construction is adapted from
`ClassFieldTheory/Cohomology/TateCohomology.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`. The degree-`-2` identification combines Mathlib's
comparison with group homology, `groupHomology.H1AddEquivOfIsTrivial`, and the tensor-product
right unitor.

## Main definitions

* `TauCeti.TateCohomology.H0IsoNormQuotient`: `Ĥ⁰(G, M) ≅ Mᴳ / N_G M`.
* `TauCeti.TateCohomology.HNegTwoIsoH1`: `Ĥ⁻²(G, M) ≅ H₁(G, M)`.
* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial`:
  `Ĥ⁻²(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` for a trivial `A : Rep ℤ G`.
* `TauCeti.TateCohomology.HNegTwoAddEquivAbelianization`:
  `Ĥ⁻²(G, ℤ) ≃+ Additive (Gᵃᵇ)`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Limits groupCohomology groupHomology LinearMap Rep
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

namespace Zero

variable (M : Rep R G)

/-- The concrete short complex whose homology is degree-zero Tate cohomology. -/
private def shortComplex : ShortComplex (ModuleCat R) :=
  .mk M.norm.toModuleCatHom (d₀₁ M) (norm_comp_d_eq_zero M)

/-- The degree-zero part of the Tate complex is the norm-to-coboundary short complex. -/
private def isoShortComplex : (tateComplex M).sc 0 ≅ shortComplex M := by
  have hnorm :
      (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom = M.tateNorm ≫ (cochainsIso₀ M).hom := by
    simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (by exact chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      hnorm (comp_d₀₁_eq M)

end Zero

/-- Degree-zero Tate cohomology is the quotient of the invariant submodule by the image of the
norm. -/
def H0IsoNormQuotient (M : Rep R G) :
    tateCohomology M 0 ≅
      ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := calc
  tateCohomology M 0
      ≅ (Zero.shortComplex M).homology :=
    ShortComplex.homologyMapIso (Zero.isoShortComplex M)
  _ ≅ ModuleCat.of R (LinearMap.ker (d₀₁ M).hom ⧸ _) :=
    ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R
      (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := by
    refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (d₀₁_ker_eq_invariants M)) ?_).toModuleIso
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨M.norm.hom y, norm_comp_d_eq_zero_apply _ y⟩, ⟨_, rfl⟩, rfl⟩

/-- In degree `-2`, Tate cohomology agrees with first group homology. This is the degree-`-2`
component of Mathlib's comparison `TateCohomology.isoGroupHomology`, named so that composites with
it, and the lemmas identifying their values, can be stated at the type `groupHomology.H1 M`. -/
def HNegTwoIsoH1 (M : Rep R G) : tateCohomology M (-2) ≅ groupHomology.H1 M :=
  (TateCohomology.isoGroupHomology (-2) 1 (by omega)).app M

variable {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) [A.IsTrivial]

/-- For a trivial representation `A` over `ℤ`, degree-`-2` Tate cohomology is the tensor product of
the additive abelianization of the group with `A`. -/
def HNegTwoAddEquivTensorOfIsTrivial :
    tateCohomology A (-2) ≃+ (Additive <| Abelianization G) ⊗[ℤ] A :=
  (HNegTwoIsoH1 A).toLinearEquiv.toAddEquiv.trans (H1AddEquivOfIsTrivial A)

/-- The degree-`-2` identification sends the homology class represented by `(g, a)` to the
elementary tensor `⟦g⟧ ⊗ₜ a`. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_apply_HNegTwoIsoH1_inv (g : G) (a : A) :
    HNegTwoAddEquivTensorOfIsTrivial A
      ((HNegTwoIsoH1 A).inv (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))) =
      Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] a := by
  have hx : (HNegTwoIsoH1 A).toLinearEquiv.toAddEquiv
      ((HNegTwoIsoH1 A).inv (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))) =
      H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)) :=
    (HNegTwoIsoH1 A).inv_hom_id_apply _
  simp only [HNegTwoAddEquivTensorOfIsTrivial, AddEquiv.trans_apply]
  rw [hx, H1AddEquivOfIsTrivial_single]

/-- The degree-`-2` Tate cohomology of the trivial integral representation is the additive
abelianization of the group. -/
def HNegTwoAddEquivAbelianization :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  (HNegTwoAddEquivTensorOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- The degree-`-2` identification sends the homology class represented by `(g, 1)` to the class
of `g` in the additive abelianization. -/
@[simp]
theorem HNegTwoAddEquivAbelianization_apply_HNegTwoIsoH1_inv (g : G) :
    HNegTwoAddEquivAbelianization
      ((HNegTwoIsoH1 (Rep.trivial ℤ G ℤ)).inv
        (H1π (Rep.trivial ℤ G ℤ)
          ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g 1)))) =
      Additive.ofMul (Abelianization.of g) := by
  simp only [HNegTwoAddEquivAbelianization, AddEquiv.trans_apply]
  rw [HNegTwoAddEquivTensorOfIsTrivial_apply_HNegTwoIsoH1_inv]
  simp

end TauCeti.TateCohomology
