/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Low-degree Tate cohomology

This file gives the two low-degree descriptions used by the Nakayama map. For a representation
`M` of a finite group, degree zero is the quotient of the invariant submodule by the image of the
norm. For a trivial representation `A`, the comparison with first group homology identifies degree
`-2` with `Gᵃᵇ ⊗[ℤ] A`, and hence, for the trivial integral representation, with the additive form
of the abelianization.

The degree-zero construction is adapted from
`ClassFieldTheory/Cohomology/TateCohomology.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`. The degree-`-2` identification combines Mathlib's
comparison with group homology, `groupHomology.H1AddEquivOfIsTrivial`, and the tensor-product
right unitor.

## Main definitions

* `TauCeti.TateCohomology.H0IsoNormQuotient`: `Ĥ⁰(G, M) ≅ Mᴳ / N_G M`.
* `TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial`:
  `Ĥ⁻²(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` for a trivial representation `A`.
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

/-- The map from invariant representatives to degree-zero Tate cohomology. -/
def H0π (M : Rep R G) : ModuleCat.of R M.ρ.invariants ⟶ tateCohomology M 0 :=
  ModuleCat.ofHom (Submodule.mkQ ((range M.ρ.norm).submoduleOf M.ρ.invariants)) ≫
    (H0IsoNormQuotient M).inv

instance (M : Rep R G) : Epi (H0π M) :=
  have : Epi (ModuleCat.ofHom (Submodule.mkQ ((range M.ρ.norm).submoduleOf M.ρ.invariants))) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  inferInstanceAs <| Epi (_ ≫ _)

/-- Passing an invariant representative to degree-zero Tate cohomology and then applying the
low-degree identification is the quotient map by the norm image. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_H0IsoNormQuotient_hom (M : Rep R G) :
    H0π M ≫ (H0IsoNormQuotient M).hom =
      ModuleCat.ofHom (Submodule.mkQ ((range M.ρ.norm).submoduleOf M.ρ.invariants)) := by
  simp [H0π]

/-- An invariant represents the zero degree-zero Tate cohomology class exactly when it lies in
the image of the norm. -/
@[simp]
theorem H0π_eq_zero_iff {M : Rep R G} (y : M.ρ.invariants) :
    H0π M y = 0 ↔ y ∈ (range M.ρ.norm).submoduleOf M.ρ.invariants := by
  rw [← Submodule.Quotient.mk_eq_zero, ← H0π_comp_H0IsoNormQuotient_hom_apply]
  exact ((H0IsoNormQuotient M).toLinearEquiv.map_eq_zero_iff).symm

/-- Two invariants represent the same degree-zero Tate cohomology class exactly when their
difference lies in the image of the norm. -/
@[simp]
theorem H0π_eq_iff {M : Rep R G} (y z : M.ρ.invariants) :
    H0π M y = H0π M z ↔ y - z ∈ (range M.ρ.norm).submoduleOf M.ρ.invariants := by
  rw [← sub_eq_zero, ← map_sub, H0π_eq_zero_iff]

/-- Every degree-zero Tate cohomology class is represented by an invariant, so a property of all
classes follows from the property of the classes of invariants. -/
@[elab_as_elim]
theorem H0_induction_on {M : Rep R G} {C : tateCohomology M 0 → Prop} (x : tateCohomology M 0)
    (h : ∀ y : M.ρ.invariants, C (H0π M y)) : C x := by
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective ((range M.ρ.norm).submoduleOf M.ρ.invariants)
    ((H0IsoNormQuotient M).hom x)
  simpa [H0π, hy] using h y

variable (A : Rep R G) [A.IsTrivial]

/-- For a trivial representation `A`, degree-`-2` Tate cohomology is the tensor product of the
additive abelianization of the group with `A`. -/
def HNegTwoAddEquivTensorOfIsTrivial :
    tateCohomology A (-2) ≃+ (Additive <| Abelianization G) ⊗[ℤ] A :=
  let e : tateCohomology A (-2) ≅ groupHomology.H1 A :=
    (TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).app A
  e.toLinearEquiv.toAddEquiv.trans (H1AddEquivOfIsTrivial A)

/-- The degree-`-2` identification sends the homology class represented by `(g, a)` to the
elementary tensor `⟦g⟧ ⊗ₜ a`. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_single (g : G) (a : A) :
    HNegTwoAddEquivTensorOfIsTrivial A
      ((TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).inv.app A
        (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))) =
      Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] a := by
  let e : tateCohomology A (-2) ≅ groupHomology.H1 A :=
    (TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).app A
  -- The natural isomorphism lands in `groupHomology.functor R G 1`, whereas the low-degree API
  -- uses the definitionally equal alias `groupHomology.H1`; an explicit rewrite cannot cross
  -- that boundary at implicit transparency.
  change HNegTwoAddEquivTensorOfIsTrivial A
    (e.inv (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))) = _
  -- Unfolding the composite similarly exposes the functor value rather than `H1`, so record the
  -- definitionally equal, well-typed low-degree form before applying the isomorphism law.
  change (H1AddEquivOfIsTrivial A)
    (e.hom (e.inv (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))))) = _
  rw [e.inv_hom_id_apply, H1AddEquivOfIsTrivial_single]

/-- The inverse degree-`-2` identification sends an elementary tensor to the corresponding Tate
homology class. -/
@[simp]
theorem HNegTwoAddEquivTensorOfIsTrivial_symm_tmul (g : G) (a : A) :
    (HNegTwoAddEquivTensorOfIsTrivial A).symm
        (Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] a) =
      (TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).inv.app A
        (H1π A ((cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))) := by
  apply (HNegTwoAddEquivTensorOfIsTrivial A).injective
  rw [AddEquiv.apply_symm_apply, HNegTwoAddEquivTensorOfIsTrivial_single]

variable {G : Type} [Group G] [Fintype G]

/-- The degree-`-2` Tate cohomology of the trivial integral representation is the additive
abelianization of the group. -/
def HNegTwoAddEquivAbelianization :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  (HNegTwoAddEquivTensorOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- The degree-`-2` identification sends the homology class represented by `(g, 1)` to the class
of `g` in the additive abelianization. -/
@[simp]
theorem HNegTwoAddEquivAbelianization_single_one (g : G) :
    HNegTwoAddEquivAbelianization
      ((TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).inv.app
        (Rep.trivial ℤ G ℤ)
        (H1π (Rep.trivial ℤ G ℤ)
          ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g 1)))) =
      Additive.ofMul (Abelianization.of g) := by
  simp only [HNegTwoAddEquivAbelianization, AddEquiv.trans_apply]
  rw [HNegTwoAddEquivTensorOfIsTrivial_single]
  simp

/-- The inverse integral degree-`-2` identification sends the class of `g` to the Tate homology
class represented by `(g, 1)`. -/
@[simp]
theorem HNegTwoAddEquivAbelianization_symm_of (g : G) :
    HNegTwoAddEquivAbelianization.symm (Additive.ofMul (Abelianization.of g)) =
      (TateCohomology.isoGroupHomology (-2) 1 (Eq.refl (-2))).inv.app
        (Rep.trivial ℤ G ℤ)
        (H1π (Rep.trivial ℤ G ℤ)
          ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g 1))) := by
  apply HNegTwoAddEquivAbelianization.injective
  rw [AddEquiv.apply_symm_apply, HNegTwoAddEquivAbelianization_single_one]

end TauCeti.TateCohomology
