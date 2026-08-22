/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Diagram automorphisms of the pinned simply connected root datum

A symmetry of the Bourbaki-numbered Dynkin diagram of a valid `TauCeti.DynkinType` is a permutation
`σ` of `Fin t.rank` preserving the Cartan matrix. This file turns each such permutation into an
automorphism of the pinned simply connected root datum
`TauCeti.DynkinType.simplyConnectedRootDatum`, multiplicatively in `σ`.

Both pinned lattices are coordinate spaces, so both maps of the automorphism are permutations of
coordinates, but the two permutations are transpose to one another and must be told apart. The
character lattice carries the fundamental weights as its standard basis, and its map is
precomposition with `σ⁻¹`, which permutes the fundamental weights by `σ`. Mathlib's coweight slot
holds the transpose of that map, so the cocharacter lattice, which carries the simple coroots as
its standard basis, receives precomposition with `σ`, which permutes the simple coroots by `σ⁻¹`;
the coroots themselves are nevertheless permuted by `σ`, by
`TauCeti.DynkinType.coroot_diagramRootPerm`.

What is not visible from the coordinates is the accompanying permutation of the root enumeration
`Fin t.numRoots`, since the non-simple roots are stored as explicit coordinate tables per family.
That permutation is obtained here from Mathlib's `RootPairing.Base.equivOfCartanMatrixEq` applied
to the rational root system `TauCeti.DynkinType.rationalRootSystem`, which is where the roots span
and a base therefore determines an isomorphism; the resulting equations transport back to `ℤ`
because the base change is the coordinatewise cast.

The multiplicativity is the point rather than a bonus. A Steinberg endomorphism of a graph-twisted
finite group of Lie type composes the field Frobenius with the graph automorphism attached to a
diagram symmetry of order two or three, and the relation `γ ^ 2 = 1` or `γ ^ 3 = 1` it needs is the
image of the corresponding relation on `σ` under the homomorphism
`TauCeti.DynkinType.diagramAutHom` built below.

The group of node permutations that the construction consumes is
`TauCeti.DynkinType.diagramSymmetry`, pinned in
`TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`.

## Main definitions

* `TauCeti.DynkinType.diagramRootPerm`: the induced permutation of the pinned root enumeration.
* `TauCeti.DynkinType.rationalDiagramAut` and `TauCeti.DynkinType.diagramAut`: the induced
  automorphisms of the rational root system and of the pinned integral datum.
* `TauCeti.DynkinType.diagramAutHom`: the homomorphism out of `diagramSymmetry` sending each
  diagram symmetry to the automorphism `diagramAut` it induces on the pinned integral datum.

## Main results

* `TauCeti.DynkinType.diagramRootPerm_simpleIndex`: the induced permutation extends `σ` along the
  Bourbaki numbering of the simple roots.
* `TauCeti.DynkinType.root_diagramRootPerm` and `TauCeti.DynkinType.coroot_diagramRootPerm`: every
  root and coroot has its coordinates permuted by `σ`.
* `TauCeti.DynkinType.eq_diagramAut`: an automorphism of the pinned datum whose weight map is the
  coordinate permutation is the diagram automorphism, so the construction is the unique such
  automorphism.
* `TauCeti.DynkinType.diagramAut_pow_eq_one`: a node permutation of finite order induces an
  automorphism of the same finite order relation.

## References

The diagram automorphism attached to a symmetry of a pinned root datum is Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`: "Pinnings ... This is what makes 'the' graph
automorphism well defined, so it is data, not a property", and it is the "isomorphism of root data"
that the isomorphism theorem for pinned groups there lifts to a group scheme. Its consumer is
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`, the graph-twisted Steinberg maps. See
R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15, and
N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
-/

public section

namespace TauCeti.DynkinType

variable {t : DynkinType} {σ τ : Equiv.Perm (Fin t.rank)}

/-! ## The induced permutation of the pinned root enumeration -/

noncomputable section

variable (ht : t.Valid)

/-- Transported along the Bourbaki numbering by `Equiv.permCongr`, a symmetry of the Cartan matrix
of `t` is a symmetry of the Cartan matrix of the pinned rational base. -/
private theorem cartanMatrix_rationalBase_permCongr (hσ : σ ∈ t.diagramSymmetry)
    (i j : (t.rationalBase ht).support) :
    (t.rationalBase ht).cartanMatrix ((t.simpleSupportEquiv ht).permCongr σ i)
        ((t.simpleSupportEquiv ht).permCongr σ j) =
      (t.rationalBase ht).cartanMatrix i j := by
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  obtain ⟨j, rfl⟩ := (t.simpleSupportEquiv ht).surjective j
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [cartanMatrix_rationalBase, cartanMatrix_rationalBase]
  exact mem_diagramSymmetry_iff.mp hσ i j

/-- **The automorphism of the rational root system** attached to a symmetry of the Bourbaki-numbered
Cartan matrix. Over `ℚ` the roots span, so a self-map of the base which preserves the Cartan matrix
extends to the whole root system, by Mathlib's rigidity theorem. -/
def rationalDiagramAut (hσ : σ ∈ t.diagramSymmetry) : (t.rationalRootSystem ht).Aut :=
  (t.rationalBase ht).equivOfCartanMatrixEq (t.rationalBase ht)
    ((t.simpleSupportEquiv ht).permCongr σ) (cartanMatrix_rationalBase_permCongr ht hσ)

/-- **The permutation of the pinned root enumeration** realized by a symmetry of the Cartan
matrix. -/
def diagramRootPerm (hσ : σ ∈ t.diagramSymmetry) : Equiv.Perm (Fin t.numRoots) :=
  (rationalDiagramAut ht hσ).indexEquiv

/-- The rational diagram automorphism acts on the root enumeration by
`TauCeti.DynkinType.diagramRootPerm`. -/
@[simp] theorem rationalDiagramAut_indexEquiv (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).indexEquiv = diagramRootPerm ht hσ := by
  rw [diagramRootPerm]

/-- The induced permutation of the root enumeration extends the node permutation along the Bourbaki
numbering of the simple roots. -/
@[simp] theorem diagramRootPerm_simpleIndex (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    diagramRootPerm ht hσ (t.simpleIndex ht i) = t.simpleIndex ht (σ i) := by
  have h := equivOfCartanMatrixEq_indexEquiv_apply (t.rationalBase ht) (t.rationalBase ht)
    ((t.simpleSupportEquiv ht).permCongr σ) (cartanMatrix_rationalBase_permCongr ht hσ)
    (t.simpleSupportEquiv ht i)
  rw [diagramRootPerm, rationalDiagramAut, ← coe_simpleSupportEquiv, h]
  simp

/-! ## The coordinates are permuted by the node permutation -/

/-- The weight map of the rational automorphism is precomposition with `σ⁻¹`, so it permutes the
fundamental weights, the standard basis of the character lattice, by `σ`. -/
@[simp] theorem rationalDiagramAut_weightMap (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).toHom.weightMap =
      (LinearEquiv.funCongrLeft ℚ ℚ σ.symm).toLinearMap := by
  apply (t.rationalBase ht).toWeightBasis.ext
  intro i
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  rw [RootPairing.Base.toWeightBasis_apply, RootPairing.Hom.root_weightMap_apply,
    rationalDiagramAut_indexEquiv, coe_simpleSupportEquiv, diagramRootPerm_simpleIndex]
  ext k
  simp only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    root_rationalRootSystem, root_simpleIndex]
  exact congrArg _ (by simpa using mem_diagramSymmetry_iff.mp hσ i (σ.symm k))

/-- **Every root of the pinned datum has its fundamental-weight coordinates permuted** by a symmetry
of the Cartan matrix. -/
@[simp] theorem root_diagramRootPerm (hσ : σ ∈ t.diagramSymmetry) (k : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).root (diagramRootPerm ht hσ k) =
      fun j => (t.simplyConnectedRootDatum ht).root k (σ.symm j) := by
  have h := RootPairing.Hom.root_weightMap_apply (t.rationalRootSystem ht)
    (t.rationalRootSystem ht) k (rationalDiagramAut ht hσ).toHom
  rw [rationalDiagramAut_weightMap] at h
  ext j
  have := congrFun h j
  simp only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    root_rationalRootSystem] at this
  exact_mod_cast this.symm

/-- The *inverse* of the coweight equivalence of the rational automorphism is precomposition with
`σ⁻¹`, so it permutes the simple coroots, the standard basis of the cocharacter lattice, by `σ`.
It is this inverse, and not the coweight map itself, which carries a coroot to the coroot of the
permuted index. -/
@[simp] theorem rationalDiagramAut_coweightEquiv_symm (hσ : σ ∈ t.diagramSymmetry) :
    (RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht) (t.rationalRootSystem ht)
        (rationalDiagramAut ht hσ)).symm = LinearEquiv.funCongrLeft ℚ ℚ σ.symm := by
  apply LinearEquiv.toLinearMap_injective
  apply (t.rationalBase ht).toCoweightBasis.ext
  intro i
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  rw [RootPairing.Base.toCoweightBasis_apply]
  -- Mathlib's `equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot` is stated for the equivalence
  -- produced by the rigidity theorem, so unfold `rationalDiagramAut` back to that form.
  simp only [LinearEquiv.coe_coe, rationalDiagramAut]
  rw [equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot (t.rationalBase ht) (t.rationalBase ht)
    ((t.simpleSupportEquiv ht).permCongr σ) (cartanMatrix_rationalBase_permCongr ht hσ)
    (t.simpleSupportEquiv ht i)]
  ext k
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, coe_simpleSupportEquiv,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, coroot_rationalRootSystem,
    coroot_simpleIndex, Pi.single_apply]
  rcases eq_or_ne k (σ i) with h | h
  · subst h
    simp
  · have h' : ¬ (σ.symm k = i) := fun hc => h (by rw [← hc, Equiv.apply_symm_apply])
    simp [h, h']

/-- The coweight map of the rational automorphism is precomposition with `σ`, the transpose of the
weight map, so it permutes the simple coroots by `σ⁻¹`. -/
@[simp] theorem rationalDiagramAut_coweightMap (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).toHom.coweightMap =
      (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [← RootPairing.Equiv.coweightEquiv_apply]
  apply (RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht)
    (t.rationalRootSystem ht) (rationalDiagramAut ht hσ)).symm.injective
  rw [LinearEquiv.symm_apply_apply, rationalDiagramAut_coweightEquiv_symm]
  ext j
  simp

/-- **Every coroot of the pinned datum has its simple-coroot coordinates permuted** by a symmetry of
the Cartan matrix. -/
@[simp] theorem coroot_diagramRootPerm (hσ : σ ∈ t.diagramSymmetry) (k : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).coroot (diagramRootPerm ht hσ k) =
      fun j => (t.simplyConnectedRootDatum ht).coroot k (σ.symm j) := by
  have h1 : (RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht) (t.rationalRootSystem ht)
      (rationalDiagramAut ht hσ)) ((t.rationalRootSystem ht).coroot (diagramRootPerm ht hσ k)) =
      (t.rationalRootSystem ht).coroot k := by
    rw [RootPairing.Equiv.coweightEquiv_apply, RootPairing.Hom.coroot_coweightMap_apply,
      diagramRootPerm, Equiv.symm_apply_apply]
  have h2 := congrArg (RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht)
    (t.rationalRootSystem ht) (rationalDiagramAut ht hσ)).symm h1
  rw [LinearEquiv.symm_apply_apply] at h2
  have h3 := DFunLike.congr_fun (rationalDiagramAut_coweightEquiv_symm ht hσ)
    ((t.rationalRootSystem ht).coroot k)
  ext j
  have h4 : (t.rationalRootSystem ht).coroot (diagramRootPerm ht hσ k) j =
      (t.rationalRootSystem ht).coroot k (σ.symm j) := by
    rw [h2]
    simpa only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply] using congrFun h3 j
  simpa only [coroot_rationalRootSystem, Int.cast_injective.eq_iff] using h4

/-! ## The automorphism of the pinned integral datum -/

/-- The two coordinate permutations are transpose to one another against the dot-product pairing of
the pinned datum. -/
private theorem funCongrLeft_dualMap_comp_toPerfPair :
    (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap.dualMap ∘ₗ
        (t.simplyConnectedRootDatum ht).flip.toPerfPair =
      (t.simplyConnectedRootDatum ht).flip.toPerfPair ∘ₗ
        (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap := by
  refine LinearMap.ext fun y => LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.dualMap_apply,
    LinearMap.toPerfPair_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, RootPairing.flip_toLinearMap, LinearMap.flip_apply,
    toLinearMap_simplyConnectedRootDatum, dotProduct]
  exact (Equiv.sum_comp σ fun i => x (σ.symm i) * y i).symm.trans
    (Finset.sum_congr rfl fun i _ => by rw [Equiv.symm_apply_apply])

/-- The permutation of the fundamental-weight coordinates carries the root enumeration along
`TauCeti.DynkinType.diagramRootPerm`. -/
private theorem funCongrLeft_comp_root (hσ : σ ∈ t.diagramSymmetry) :
    ⇑(LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap ∘ (t.simplyConnectedRootDatum ht).root =
      (t.simplyConnectedRootDatum ht).root ∘ diagramRootPerm ht hσ := by
  ext k j
  simpa only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply] using congrFun (root_diagramRootPerm ht hσ k) j |>.symm

/-- The permutation of the simple-coroot coordinates carries the coroot enumeration along the
inverse of `TauCeti.DynkinType.diagramRootPerm`. -/
private theorem funCongrLeft_comp_coroot (hσ : σ ∈ t.diagramSymmetry) :
    ⇑(LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap ∘ (t.simplyConnectedRootDatum ht).coroot =
      (t.simplyConnectedRootDatum ht).coroot ∘ (diagramRootPerm ht hσ).symm := by
  ext k j
  have h := congrFun (coroot_diagramRootPerm ht hσ ((diagramRootPerm ht hσ).symm k)) (σ j)
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  simpa only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply] using h

/-- **The diagram automorphism of the pinned simply connected root datum** attached to a symmetry of
the Bourbaki-numbered Cartan matrix. Both lattice maps are precompositions, the character one with
`σ⁻¹` and the cocharacter one, its transpose, with `σ`, and the root enumeration is permuted by
`TauCeti.DynkinType.diagramRootPerm`. -/
def diagramAut (hσ : σ ∈ t.diagramSymmetry) :
    (t.simplyConnectedRootDatum ht).Aut where
  weightMap := (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap
  coweightMap := (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap
  indexEquiv := diagramRootPerm ht hσ
  weight_coweight_transpose := funCongrLeft_dualMap_comp_toPerfPair ht
  root_weightMap := funCongrLeft_comp_root ht hσ
  coroot_coweightMap := funCongrLeft_comp_coroot ht hσ
  bijective_weightMap := (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).bijective
  bijective_coweightMap := (LinearEquiv.funCongrLeft ℤ ℤ σ).bijective

/-- The diagram automorphism acts on the root enumeration by
`TauCeti.DynkinType.diagramRootPerm`. -/
@[simp] theorem diagramAut_indexEquiv (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).indexEquiv = diagramRootPerm ht hσ :=
  (rfl)

/-- The weight map of the diagram automorphism is precomposition with `σ⁻¹`, so it permutes the
fundamental weights, the standard basis of the character lattice, by `σ`. -/
@[simp] theorem diagramAut_weightMap (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).toHom.weightMap = (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap :=
  (rfl)

/-- The coweight map of the diagram automorphism is precomposition with `σ`, the transpose of the
weight map, so it permutes the simple coroots by `σ⁻¹`. -/
@[simp] theorem diagramAut_coweightMap (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).toHom.coweightMap = (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap :=
  (rfl)

/-- **An automorphism of the pinned datum is the diagram automorphism as soon as its weight map is**
the coordinate permutation, since an automorphism of a root pairing is determined by that map. -/
theorem eq_diagramAut {g : (t.simplyConnectedRootDatum ht).Aut} (hσ : σ ∈ t.diagramSymmetry)
    (hg : g.toHom.weightMap = (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap) :
    g = diagramAut ht hσ := by
  apply RootPairing.Equiv.weightHom_injective (t.simplyConnectedRootDatum ht)
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext fun x => ?_
  simp only [RootPairing.Equiv.weightHom_apply, LinearEquiv.coe_coe,
    RootPairing.Equiv.weightEquiv_apply, diagramAut_weightMap]
  exact LinearMap.congr_fun hg x

/-! ## Multiplicativity -/

/-- The diagram automorphism attached to the identity node permutation is the identity. -/
@[simp] theorem diagramAut_one : diagramAut ht t.diagramSymmetry.one_mem = 1 := by
  apply RootPairing.Equiv.weightHom_injective (t.simplyConnectedRootDatum ht)
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext fun x => funext fun j => ?_
  simp [Equiv.Perm.one_def]

/-- The construction is multiplicative in the node permutation. -/
@[simp] theorem diagramAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    diagramAut ht (t.diagramSymmetry.mul_mem hσ hτ) = diagramAut ht hσ * diagramAut ht hτ := by
  apply RootPairing.Equiv.weightHom_injective (t.simplyConnectedRootDatum ht)
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext fun x => funext fun j => ?_
  simp [RootPairing.Equiv.mul_eq_comp, Equiv.Perm.mul_def]

/-- The induced permutation of the root enumeration is the index component of the diagram
automorphism, so it inherits multiplicativity from `TauCeti.DynkinType.diagramAut_mul`. -/
@[simp] theorem diagramRootPerm_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    diagramRootPerm ht (t.diagramSymmetry.mul_mem hσ hτ) =
      diagramRootPerm ht hσ * diagramRootPerm ht hτ := by
  have h := congrArg ⇑(RootPairing.Equiv.indexHom (t.simplyConnectedRootDatum ht))
    (diagramAut_mul ht hσ hτ)
  rw [map_mul] at h
  exact h

/-- The identity node permutation induces the identity permutation of the root enumeration. -/
@[simp] theorem diagramRootPerm_one : diagramRootPerm ht t.diagramSymmetry.one_mem = 1 := by
  have h := congrArg ⇑(RootPairing.Equiv.indexHom (t.simplyConnectedRootDatum ht))
    (diagramAut_one ht)
  rw [map_one] at h
  exact h

/-- **The diagram automorphisms of the pinned datum, as a homomorphism** out of the symmetry group
of the Bourbaki-numbered Cartan matrix. This is what converts a relation satisfied by a node
permutation into the same relation for the automorphism it induces. -/
def diagramAutHom : t.diagramSymmetry →* (t.simplyConnectedRootDatum ht).Aut where
  toFun g := diagramAut ht g.2
  map_one' := diagramAut_one ht
  map_mul' g₁ g₂ := diagramAut_mul ht g₁.2 g₂.2

@[simp] theorem diagramAutHom_apply (g : t.diagramSymmetry) :
    diagramAutHom ht g = diagramAut ht g.2 :=
  (rfl)

/-- The diagram automorphism attached to the inverse node permutation is the inverse
automorphism. -/
@[simp] theorem diagramAut_inv (hσ : σ ∈ t.diagramSymmetry) :
    diagramAut ht (t.diagramSymmetry.inv_mem hσ) = (diagramAut ht hσ)⁻¹ :=
  map_inv (diagramAutHom ht) ⟨σ, hσ⟩

/-- **A node permutation of finite order induces an automorphism satisfying the same relation.**
This is the source of `γ ^ 2 = 1` for the order-two diagram symmetries of `Aₙ`, `Dₙ` and `E₆`, and
of `γ ^ 3 = 1` for the triality of `D₄`. -/
theorem diagramAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry) {n : ℕ} (hn : σ ^ n = 1) :
    diagramAut ht hσ ^ n = 1 := by
  have h : (⟨σ, hσ⟩ : t.diagramSymmetry) ^ n = 1 := Subtype.ext (by simpa using hn)
  calc diagramAut ht hσ ^ n = diagramAutHom ht (⟨σ, hσ⟩ ^ n) := by
        rw [map_pow, diagramAutHom_apply]
    _ = 1 := by rw [h, map_one]

end

end TauCeti.DynkinType
