/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Diagram automorphisms of the pinned simply connected root datum

A symmetry of the Bourbaki-numbered Dynkin diagram of a valid `TauCeti.DynkinType` is a permutation
`σ` of `Fin t.rank` preserving the Cartan matrix. This file turns each such permutation into an
automorphism of the pinned simply connected root datum
`TauCeti.DynkinType.simplyConnectedRootDatum`, multiplicatively in `σ`.

On both pinned lattices the automorphism is the permutation of coordinates by `σ`: the character
lattice carries the fundamental weights as its standard basis and the cocharacter lattice carries
the simple coroots, and `σ` permutes each of those two bases. What is not visible from the
coordinates is the accompanying permutation of the root enumeration `Fin t.numRoots`, since the
non-simple roots are stored as explicit coordinate tables per family. That permutation is obtained
here from Mathlib's `RootPairing.Base.equivOfCartanMatrixEq` applied to the rational root system
`TauCeti.DynkinType.rationalRootSystem`, which is where the roots span and a base therefore
determines an isomorphism; the resulting equations transport back to `ℤ` because the base change is
the coordinatewise cast.

The multiplicativity is the point rather than a bonus. A Steinberg endomorphism of a graph-twisted
finite group of Lie type composes the field Frobenius with the graph automorphism attached to a
diagram symmetry of order two or three, and the relation `γ ^ 2 = 1` or `γ ^ 3 = 1` it needs is the
image of the corresponding relation on `σ` under the homomorphism
`TauCeti.DynkinType.diagramAutHom` built below.

## Main definitions

* `TauCeti.DynkinType.diagramSymmetry`: the group of node permutations preserving the Cartan matrix.
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

open _root_.Matrix

/-! ## Symmetries of the Bourbaki-numbered Cartan matrix -/

/-- **The symmetry group of a Bourbaki-numbered Dynkin diagram**: the permutations of the nodes
which preserve the Cartan matrix. -/
def diagramSymmetry (t : DynkinType) : Subgroup (Equiv.Perm (Fin t.rank)) where
  carrier := {σ | ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j}
  one_mem' _ _ := rfl
  mul_mem' {σ τ} hσ hτ i j := by
    simpa only [Equiv.Perm.mul_apply] using (hσ (τ i) (τ j)).trans (hτ i j)
  inv_mem' {σ} hσ i j := by
    simp only [Equiv.Perm.inv_def]
    have h := hσ (σ.symm i) (σ.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm

variable {t : DynkinType} {σ τ : Equiv.Perm (Fin t.rank)}

/-- The entrywise form of membership in `TauCeti.DynkinType.diagramSymmetry`. -/
theorem mem_diagramSymmetry_iff :
    σ ∈ t.diagramSymmetry ↔ ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j :=
  Iff.rfl

/-- The matrix form of membership in `TauCeti.DynkinType.diagramSymmetry`. This is the shape in
which `TauCeti.serreDiagramAut` takes a Cartan-matrix symmetry. -/
theorem mem_diagramSymmetry_iff_submatrix :
    σ ∈ t.diagramSymmetry ↔ t.cartanMatrix.submatrix σ σ = t.cartanMatrix :=
  ⟨fun h => by ext i j; exact h i j, fun h i j => congrFun₂ h i j⟩

/-! ## The induced permutation of the pinned root enumeration -/

noncomputable section

variable (t) (ht : t.Valid)

/-- The self-equivalence of the support of the pinned base induced by a node permutation, read
through the Bourbaki numbering. -/
private def supportPerm (σ : Equiv.Perm (Fin t.rank)) :
    Equiv.Perm ((t.rationalBase ht).support) :=
  ((t.simpleSupportEquiv ht).symm.trans σ).trans (t.simpleSupportEquiv ht)

private theorem supportPerm_apply (σ : Equiv.Perm (Fin t.rank)) (i : Fin t.rank) :
    supportPerm t ht σ (t.simpleSupportEquiv ht i) = t.simpleSupportEquiv ht (σ i) := by
  simp [supportPerm]

variable {t}

private theorem cartanMatrix_supportPerm (hσ : σ ∈ t.diagramSymmetry)
    (i j : (t.rationalBase ht).support) :
    (t.rationalBase ht).cartanMatrix (supportPerm t ht σ i) (supportPerm t ht σ j) =
      (t.rationalBase ht).cartanMatrix i j := by
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  obtain ⟨j, rfl⟩ := (t.simpleSupportEquiv ht).surjective j
  rw [supportPerm_apply, supportPerm_apply, cartanMatrix_rationalBase, cartanMatrix_rationalBase]
  exact hσ i j

/-- **The automorphism of the rational root system** attached to a symmetry of the Bourbaki-numbered
Cartan matrix. Over `ℚ` the roots span, so a self-map of the base which preserves the Cartan matrix
extends to the whole root system, by Mathlib's rigidity theorem. -/
def rationalDiagramAut (hσ : σ ∈ t.diagramSymmetry) : (t.rationalRootSystem ht).Aut :=
  (t.rationalBase ht).equivOfCartanMatrixEq (t.rationalBase ht) (supportPerm t ht σ)
    (cartanMatrix_supportPerm ht hσ)

/-- **The permutation of the pinned root enumeration** realized by a symmetry of the Cartan
matrix. -/
def diagramRootPerm (hσ : σ ∈ t.diagramSymmetry) : Equiv.Perm (Fin t.numRoots) :=
  (rationalDiagramAut ht hσ).indexEquiv

private theorem indexEquiv_rationalDiagramAut (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).indexEquiv = diagramRootPerm ht hσ :=
  rfl

/-- The rational diagram automorphism acts on the root enumeration by
`TauCeti.DynkinType.diagramRootPerm`. -/
@[simp] theorem rationalDiagramAut_indexEquiv (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).indexEquiv = diagramRootPerm ht hσ :=
  indexEquiv_rationalDiagramAut ht hσ

/-- The induced permutation of the root enumeration extends the node permutation along the Bourbaki
numbering of the simple roots. -/
@[simp] theorem diagramRootPerm_simpleIndex (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    diagramRootPerm ht hσ (t.simpleIndex ht i) = t.simpleIndex ht (σ i) := by
  have h := equivOfCartanMatrixEq_indexEquiv_apply (t.rationalBase ht) (t.rationalBase ht)
    (supportPerm t ht σ) (cartanMatrix_supportPerm ht hσ) (t.simpleSupportEquiv ht i)
  rw [diagramRootPerm, rationalDiagramAut, ← coe_simpleSupportEquiv, h, supportPerm_apply,
    coe_simpleSupportEquiv]

/-! ## The coordinates are permuted by the node permutation -/

/-- The weight map of the rational automorphism is the permutation of the fundamental-weight
coordinates. -/
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
  exact congrArg _ (by simpa using hσ i (σ.symm k))

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

/-- The inverse coweight map of the rational automorphism is the permutation of the simple-coroot
coordinates. -/
@[simp] theorem rationalDiagramAut_coweightEquiv_symm (hσ : σ ∈ t.diagramSymmetry) :
    ((RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht) (t.rationalRootSystem ht)
        (rationalDiagramAut ht hσ)).symm : _ →ₗ[ℚ] _) =
      (LinearEquiv.funCongrLeft ℚ ℚ σ.symm).toLinearMap := by
  apply (t.rationalBase ht).toCoweightBasis.ext
  intro i
  obtain ⟨i, rfl⟩ := (t.simpleSupportEquiv ht).surjective i
  rw [RootPairing.Base.toCoweightBasis_apply]
  -- `equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot` is stated for the `LinearEquiv` itself,
  -- whereas `RootPairing.Base.toCoweightBasis.ext` leaves the goal phrased against the underlying
  -- `LinearMap`. The two applications are definitionally equal, so restating the lemma at the
  -- coerced type is all that is needed to rewrite with it.
  have hcoroot : ((RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht)
        (t.rationalRootSystem ht) (rationalDiagramAut ht hσ)).symm : _ →ₗ[ℚ] _)
      ((t.rationalRootSystem ht).coroot (t.simpleSupportEquiv ht i : Fin t.numRoots)) =
      (t.rationalRootSystem ht).coroot (supportPerm t ht σ (t.simpleSupportEquiv ht i)) :=
    equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot (t.rationalBase ht) (t.rationalBase ht)
      (supportPerm t ht σ) (cartanMatrix_supportPerm ht hσ) (t.simpleSupportEquiv ht i)
  rw [hcoroot]
  ext k
  rw [supportPerm_apply, coe_simpleSupportEquiv, coe_simpleSupportEquiv]
  simp only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    coroot_rationalRootSystem, coroot_simpleIndex, Pi.single_apply]
  rcases eq_or_ne k (σ i) with h | h
  · subst h
    simp
  · have h' : ¬ (σ.symm k = i) := fun hc => h (by rw [← hc, Equiv.apply_symm_apply])
    simp [h, h']

/-- The coweight map of the rational automorphism is the permutation of the simple-coroot
coordinates. -/
@[simp] theorem rationalDiagramAut_coweightMap (hσ : σ ∈ t.diagramSymmetry) :
    (rationalDiagramAut ht hσ).toHom.coweightMap =
      (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [← RootPairing.Equiv.coweightEquiv_apply]
  apply (RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht)
    (t.rationalRootSystem ht) (rationalDiagramAut ht hσ)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change x = ((RootPairing.Equiv.coweightEquiv (t.rationalRootSystem ht)
    (t.rationalRootSystem ht) (rationalDiagramAut ht hσ)).symm : _ →ₗ[ℚ] _)
      ((LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap x)
  rw [rationalDiagramAut_coweightEquiv_symm]
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
  have h3 := LinearMap.congr_fun (rationalDiagramAut_coweightEquiv_symm ht hσ)
    ((t.rationalRootSystem ht).coroot k)
  ext j
  have h4 : (t.rationalRootSystem ht).coroot (diagramRootPerm ht hσ k) j =
      (t.rationalRootSystem ht).coroot k (σ.symm j) := by
    rw [h2]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      using congrFun h3 j
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
the Bourbaki-numbered Cartan matrix. Both lattice maps permute coordinates, and the root enumeration
is permuted by `TauCeti.DynkinType.diagramRootPerm`. -/
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

@[simp] theorem diagramAut_indexEquiv (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).indexEquiv = diagramRootPerm ht hσ :=
  (rfl)

/-- The weight map of the diagram automorphism permutes the fundamental-weight coordinates. -/
@[simp] theorem diagramAut_weightMap (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).toHom.weightMap = (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap :=
  (rfl)

/-- The coweight map of the diagram automorphism permutes the simple-coroot coordinates. -/
@[simp] theorem diagramAut_coweightMap (hσ : σ ∈ t.diagramSymmetry) :
    (diagramAut ht hσ).toHom.coweightMap = (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap :=
  (rfl)

/-! ## Multiplicativity -/

/-- The induced permutation of the root enumeration is determined by its effect on coordinates, so
the construction is multiplicative in the node permutation. -/
theorem diagramRootPerm_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    diagramRootPerm ht (t.diagramSymmetry.mul_mem hσ hτ) =
      diagramRootPerm ht hσ * diagramRootPerm ht hτ := by
  refine Equiv.ext fun k =>
    (t.simplyConnectedRootDatum ht).root.injective (funext fun j => ?_)
  rw [Equiv.Perm.mul_apply,
    congrFun (root_diagramRootPerm ht (t.diagramSymmetry.mul_mem hσ hτ) k) j,
    congrFun (root_diagramRootPerm ht hσ (diagramRootPerm ht hτ k)) j,
    congrFun (root_diagramRootPerm ht hτ k) (σ.symm j)]
  simp [Equiv.Perm.mul_def]

theorem diagramRootPerm_one :
    diagramRootPerm ht t.diagramSymmetry.one_mem = 1 := by
  refine Equiv.ext fun k =>
    (t.simplyConnectedRootDatum ht).root.injective (funext fun j => ?_)
  rw [congrFun (root_diagramRootPerm ht t.diagramSymmetry.one_mem k) j]
  rfl

/-- An automorphism of a root pairing is determined by its map of weight spaces: the index
permutation is read off the roots, which the weight map moves, and the coweight map is its inverse
transpose. This is Mathlib's `RootPairing.Hom.weightHom_injective` for the automorphism group. -/
private theorem aut_eq_of_weightMap_eq {ι' R' M' N' : Type*} [CommRing R'] [AddCommGroup M']
    [Module R' M'] [AddCommGroup N'] [Module R' N'] {P : RootPairing ι' R' M' N'} {f g : P.Aut}
    (h : f.toHom.weightMap = g.toHom.weightMap) : f = g := by
  have hfg : f.toHom = g.toHom := RootPairing.Hom.weightHom_injective P h
  exact RootPairing.Equiv.ext (congrArg RootPairing.Hom.weightMap hfg)
    (congrArg RootPairing.Hom.coweightMap hfg) (congrArg RootPairing.Hom.indexEquiv hfg)

/-- The diagram automorphism attached to the identity node permutation is the identity. -/
theorem diagramAut_one : diagramAut ht t.diagramSymmetry.one_mem = 1 := by
  refine aut_eq_of_weightMap_eq (LinearMap.ext fun x => funext fun j => ?_)
  simp only [diagramAut_weightMap, RootPairing.Equiv.toHom_one, RootPairing.Hom.weightMap_one,
    LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    LinearMap.id_coe, id_eq]
  rfl

/-- The construction is multiplicative in the node permutation. -/
theorem diagramAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    diagramAut ht (t.diagramSymmetry.mul_mem hσ hτ) = diagramAut ht hσ * diagramAut ht hτ := by
  refine aut_eq_of_weightMap_eq (LinearMap.ext fun x => funext fun j => ?_)
  simp [RootPairing.Equiv.mul_eq_comp, Equiv.Perm.mul_def]

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
