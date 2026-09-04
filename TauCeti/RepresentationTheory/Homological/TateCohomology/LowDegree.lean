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
norm. For the trivial integral representation, the comparison with first group homology
identifies degree `-2` with the additive form of the abelianization.

The degree-zero construction is adapted from
`ClassFieldTheory/Cohomology/TateCohomology.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`. The degree-`-2` identification combines Mathlib's
comparison with group homology, `groupHomology.H1AddEquivOfIsTrivial`, and the tensor-product
right unitor.

## Main definitions

* `TauCeti.TateCohomology.tateHZeroEquivNormQuotient`: `Ĥ⁰(G, M) ≅ Mᴳ / N_G M`.
* `TauCeti.TateCohomology.tateHMinusTwoEquivAbelianization`:
  `Ĥ⁻²(G, ℤ) ≃+ Additive (Gᵃᵇ)`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits groupCohomology groupHomology LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

namespace Zero

variable (M : Rep R G)

/-- The concrete short complex whose homology is degree-zero Tate cohomology. -/
@[simps]
def shortComplex : ShortComplex (ModuleCat R) :=
  .mk M.norm.toModuleCatHom (d₀₁ M) (norm_comp_d_eq_zero M)

/-- The degree-zero part of the Tate complex is the norm-to-coboundary short complex. -/
@[simps!]
def isoShortComplex : (tateComplex M).sc 0 ≅ shortComplex M := by
  have hnorm :
      (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom = M.tateNorm ≫ (cochainsIso₀ M).hom := by
    simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (by exact chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      hnorm (comp_d₀₁_eq M)

end Zero

/-- Degree-zero Tate cohomology is the quotient of the invariant submodule by the image of the
norm. -/
def tateHZeroEquivNormQuotient (M : Rep R G) :
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

variable {G : Type} [Group G] [Fintype G]

/-- In degree `-2`, Mathlib's comparison between Tate cohomology and group homology specializes to
an isomorphism with first group homology. -/
def negTwoIsoGroupHomology :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≅
      groupHomology (Rep.trivial ℤ G ℤ) 1 :=
  (TateCohomology.isoGroupHomology (-2) 1 (by omega)).app (Rep.trivial ℤ G ℤ)

/-- The degree-`-2` Tate cohomology of the trivial integral representation is the additive
abelianization of the group. -/
def tateHMinusTwoEquivAbelianization :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  ((negTwoIsoGroupHomology (G := G)).toLinearEquiv.toAddEquiv.trans
    (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ))).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- The degree-`-2` identification sends the homology class represented by `(g, 1)` to the class
of `g` in the additive abelianization. -/
@[simp]
theorem tateHMinusTwoEquivAbelianization_apply_negTwoIsoGroupHomology_inv (g : G) :
    tateHMinusTwoEquivAbelianization
      ((negTwoIsoGroupHomology (G := G)).inv
        (groupHomology.H1π (Rep.trivial ℤ G ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
            (Finsupp.single g 1)))) =
      Additive.ofMul (Abelianization.of g) := by
  let x := groupHomology.H1π (Rep.trivial ℤ G ℤ)
    ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g 1))
  have hx : (negTwoIsoGroupHomology (G := G)).toLinearEquiv.toAddEquiv
      ((negTwoIsoGroupHomology (G := G)).inv x) = x :=
    (negTwoIsoGroupHomology (G := G)).inv_hom_id_apply x
  simp only [tateHMinusTwoEquivAbelianization, AddEquiv.trans_apply]
  rw [hx]
  rw [groupHomology.H1AddEquivOfIsTrivial_single]
  simp

end TauCeti.TateCohomology
