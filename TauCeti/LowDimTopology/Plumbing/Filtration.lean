/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.LowDimTopology.Plumbing.ChainComplex
public import TauCeti.LowDimTopology.Plumbing.Cube.Sublevel

/-!
# The weight filtration on the lattice chain complex

For a characteristic covector `k` and an integer `N`, this file restricts Némethi's lattice
chain complex to the plumbing cubes whose characteristic cube weight is at most `N`. The lower
and upper faces of such a cube have no larger weight, so the weighted lattice differential
preserves this submodule. Restricting in every cubical degree therefore gives a chain complex
`latticeWeightSublevelComplex P k N`.

When the plumbing form is negative definite, every weight sublevel contains only finitely many
cubes. Indeed, a cube's base point is one of its vertices and hence has weight at most the cube
weight; the possible base points are finite by the properness theorem for the characteristic
weight, and the possible direction sets form the finite type `Finset V`. Consequently every
chain group of the restricted complex is a finitely generated `𝔽₂[U]`-module.

The inclusions for `N ≤ M` make these complexes the filtered system whose direct limit is the
untruncated lattice complex. Constructing that direct limit and identifying its homology with
Némethi's `ℍ⁻` are subsequent steps.

## Main definitions

* `TauCeti.PlumbingGraph.characteristicCubeWeightSublevel`: cubes of weight at most `N`.
* `TauCeti.PlumbingChain.supportedCharacteristicWeightSublevel`: chains supported on those cubes.
* `TauCeti.PlumbingChain.characteristicWeightDegreePart`: the weight-`≤ N`,
  cubical-degree-`q` chain group.
* `TauCeti.PlumbingGraph.latticeDifferentialWeightDegree`: the restricted differential.
* `TauCeti.PlumbingGraph.latticeWeightSublevelComplex`: the filtered chain complex at level `N`.
* `TauCeti.PlumbingGraph.latticeWeightSublevelInclusion`: the inclusion between filtration levels.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions. The filtration by the
sublevel cubical complexes is the construction in A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory

namespace PlumbingChain

variable {V : Type*} [DecidableEq V] [Fintype V]

private theorem fg_supported_of_finite {R α : Type*} [Semiring R] (s : Set α)
    (hs : s.Finite) : (Finsupp.supported R R s).FG := by
  rw [Finsupp.supported_eq_span_single]
  exact Submodule.fg_span (hs.image fun a ↦ Finsupp.single a 1)

/-- The `𝔽₂[U]`-submodule of plumbing chains supported on cubes of weight at most `N`. -/
noncomputable def supportedCharacteristicWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    Submodule PlumbingCoefficient (PlumbingChain V) :=
  Finsupp.supported PlumbingCoefficient PlumbingCoefficient (P.characteristicCubeWeightSublevel k N)

private theorem supportedCharacteristicWeightSublevel_def_private (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    supportedCharacteristicWeightSublevel P k N =
      Finsupp.supported PlumbingCoefficient PlumbingCoefficient
        (P.characteristicCubeWeightSublevel k N) :=
  rfl

/-- The chain-level characteristic-weight sublevel is the submodule supported on the
corresponding cube sublevel. -/
theorem supportedCharacteristicWeightSublevel_def (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    supportedCharacteristicWeightSublevel P k N =
      Finsupp.supported PlumbingCoefficient PlumbingCoefficient
        (P.characteristicCubeWeightSublevel k N) :=
  supportedCharacteristicWeightSublevel_def_private P k N

/-- A chain belongs to the weight sublevel exactly when every cube in its support has weight at
most the level. -/
@[simp]
theorem mem_supportedCharacteristicWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (c : PlumbingChain V) :
    c ∈ supportedCharacteristicWeightSublevel P k N ↔
      ∀ C ∈ c.support, C.characteristicWeight P k ≤ N := by
  rw [supportedCharacteristicWeightSublevel_def, Finsupp.mem_supported]
  simp only [Set.subset_def, Finset.mem_coe, P.mem_characteristicCubeWeightSublevel]

/-- A single cube of weight at most `N`, with any coefficient, belongs to the weight sublevel. -/
theorem single_mem_supportedCharacteristicWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (C : PlumbingCube V) (a : PlumbingCoefficient)
    (hC : C.characteristicWeight P k ≤ N) :
    Finsupp.single C a ∈ supportedCharacteristicWeightSublevel P k N := by
  rw [supportedCharacteristicWeightSublevel_def]
  exact Finsupp.single_mem_supported PlumbingCoefficient a
    ((P.mem_characteristicCubeWeightSublevel k N C).mpr hC)

/-- The chain-level weight submodules increase with the level. -/
theorem supportedCharacteristicWeightSublevel_mono (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) :
    supportedCharacteristicWeightSublevel P k N ≤ supportedCharacteristicWeightSublevel P k M :=
  Finsupp.supported_mono (P.characteristicCubeWeightSublevel_mono k hNM)

/-- Every plumbing chain belongs to some weight sublevel. -/
theorem exists_mem_supportedCharacteristicWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) (c : PlumbingChain V) :
    ∃ N : ℤ, c ∈ supportedCharacteristicWeightSublevel P k N := by
  obtain ⟨N, hN⟩ := Finset.exists_le (c.support.image fun C ↦ C.characteristicWeight P k)
  refine ⟨N, (mem_supportedCharacteristicWeightSublevel P k N c).mpr fun C hC ↦ ?_⟩
  exact hN _ (Finset.mem_image_of_mem _ hC)

/-- The weight filtration exhausts the full plumbing chain module. -/
theorem iSup_supportedCharacteristicWeightSublevel_eq_top (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    ⨆ N : ℤ, supportedCharacteristicWeightSublevel P k N = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨N, hc⟩ := exists_mem_supportedCharacteristicWeightSublevel P k c
  exact Submodule.mem_iSup_of_mem N hc

/-- On a negative-definite plumbing, each chain-level weight submodule is finitely generated over
`𝔽₂[U]`. -/
theorem supportedCharacteristicWeightSublevel_fg (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) (N : ℤ) :
    (supportedCharacteristicWeightSublevel P k N).FG := by
  rw [supportedCharacteristicWeightSublevel_def]
  exact fg_supported_of_finite _ (P.finite_characteristicCubeWeightSublevel h k N)

/-- The chains simultaneously lying in cubical degree `q` and weight at most `N`. -/
noncomputable def characteristicWeightDegreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    Submodule PlumbingCoefficient (PlumbingChain V) :=
  degreePart V q ⊓ supportedCharacteristicWeightSublevel P k N

private theorem characteristicWeightDegreePart_def_private (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    characteristicWeightDegreePart P k N q =
      degreePart V q ⊓ supportedCharacteristicWeightSublevel P k N :=
  rfl

/-- The filtered degree part is the intersection of the cubical-degree part and the
chain-level characteristic-weight sublevel. -/
theorem characteristicWeightDegreePart_def (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    characteristicWeightDegreePart P k N q =
      degreePart V q ⊓ supportedCharacteristicWeightSublevel P k N :=
  characteristicWeightDegreePart_def_private P k N q

/-- A filtered degree part lies in the corresponding unfiltered cubical-degree part. -/
theorem characteristicWeightDegreePart_le_degreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    characteristicWeightDegreePart P k N q ≤ degreePart V q :=
  inf_le_left

/-- A filtered degree part lies in the corresponding chain-level characteristic-weight
sublevel. -/
theorem characteristicWeightDegreePart_le_supportedCharacteristicWeightSublevel
    (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    characteristicWeightDegreePart P k N q ≤ supportedCharacteristicWeightSublevel P k N :=
  inf_le_right

/-- Membership in a weight-graded chain group means that every support cube has the specified
cubical dimension and weight at most the level. -/
@[simp]
theorem mem_characteristicWeightDegreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors)
    (N : ℤ) (q : ℕ) (c : PlumbingChain V) :
    c ∈ characteristicWeightDegreePart P k N q ↔
      ∀ C ∈ c.support, C.dimension = q ∧ C.characteristicWeight P k ≤ N := by
  rw [characteristicWeightDegreePart_def, Submodule.mem_inf, mem_degreePart,
    mem_supportedCharacteristicWeightSublevel]
  aesop

/-- A filtered degree part is the submodule supported on cubes having the prescribed dimension
and characteristic-weight bound. -/
theorem characteristicWeightDegreePart_eq_supported (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    characteristicWeightDegreePart P k N q =
      Finsupp.supported PlumbingCoefficient PlumbingCoefficient
        {C | C.dimension = q ∧ C.characteristicWeight P k ≤ N} := by
  have hdegree : degreePart V q =
      Finsupp.supported PlumbingCoefficient PlumbingCoefficient {C | C.dimension = q} := by
    ext c
    rw [mem_degreePart, Finsupp.mem_supported]
    simp only [Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  rw [characteristicWeightDegreePart_def, hdegree,
    supportedCharacteristicWeightSublevel_def, ← Finsupp.supported_inter]
  congr 1
  ext C
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, P.mem_characteristicCubeWeightSublevel]

/-- A basis cube of dimension `q` and weight at most `N` belongs to the corresponding filtered
chain group. -/
theorem single_mem_characteristicWeightDegreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) (C : PlumbingCube V)
    (a : PlumbingCoefficient)
    (hdim : C.dimension = q) (hweight : C.characteristicWeight P k ≤ N) :
    Finsupp.single C a ∈ characteristicWeightDegreePart P k N q :=
  ⟨single_mem_degreePart V C a hdim,
    single_mem_supportedCharacteristicWeightSublevel P k N C a hweight⟩

/-- Filtered cubical-degree chain groups increase with the weight level. -/
theorem characteristicWeightDegreePart_mono (P : PlumbingGraph V)
    (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) (q : ℕ) :
    characteristicWeightDegreePart P k N q ≤ characteristicWeightDegreePart P k M q :=
  inf_le_inf_left _ (supportedCharacteristicWeightSublevel_mono P k hNM)

/-- In a fixed cubical degree, the weight filtration exhausts the full degree submodule. -/
theorem iSup_characteristicWeightDegreePart_eq_degreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    ⨆ N : ℤ, characteristicWeightDegreePart P k N q = degreePart V q := by
  apply le_antisymm
  · exact iSup_le fun _ => inf_le_left
  · intro c hc
    obtain ⟨N, hN⟩ := exists_mem_supportedCharacteristicWeightSublevel P k c
    exact Submodule.mem_iSup_of_mem N ⟨hc, hN⟩

/-- On a negative-definite plumbing, every filtered cubical-degree chain group is finitely
generated over `𝔽₂[U]`. -/
theorem characteristicWeightDegreePart_fg (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (characteristicWeightDegreePart P k N q).FG := by
  have hfinite : {C : PlumbingCube V |
      C.dimension = q ∧ C.characteristicWeight P k ≤ N}.Finite :=
    (P.finite_characteristicCubeWeightSublevel h k N).subset fun C hC =>
      (P.mem_characteristicCubeWeightSublevel k N C).mpr hC.2
  rw [characteristicWeightDegreePart_eq_supported]
  exact fg_supported_of_finite _ hfinite

end PlumbingChain

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The differential of a cube in a weight sublevel is supported in the same sublevel. -/
theorem latticeDifferentialOnGenerator_mem_supportedCharacteristicWeightSublevel
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} (C : PlumbingCube V)
    (hC : C.characteristicWeight P k ≤ N) :
    P.latticeDifferentialOnGenerator k C ∈
      PlumbingChain.supportedCharacteristicWeightSublevel P k N := by
  classical
  rw [latticeDifferentialOnGenerator_def]
  apply Submodule.sum_mem
  intro v _
  apply Submodule.add_mem
  · exact PlumbingChain.single_mem_supportedCharacteristicWeightSublevel P k N _ _
      ((P.mem_characteristicCubeWeightSublevel k N _).mp
        (P.lowerFace_mem_characteristicCubeWeightSublevel k
          ((P.mem_characteristicCubeWeightSublevel k N C).mpr hC) v.property))
  · exact PlumbingChain.single_mem_supportedCharacteristicWeightSublevel P k N _ _
      ((P.mem_characteristicCubeWeightSublevel k N _).mp
        (P.upperFace_mem_characteristicCubeWeightSublevel k
          ((P.mem_characteristicCubeWeightSublevel k N C).mpr hC) v.property))

/-- The lattice differential preserves every chain-level weight submodule. -/
theorem latticeDifferential_mem_supportedCharacteristicWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.supportedCharacteristicWeightSublevel P k N) :
    P.latticeDifferential k c ∈ PlumbingChain.supportedCharacteristicWeightSublevel P k N := by
  rw [PlumbingChain.supportedCharacteristicWeightSublevel_def,
    Finsupp.supported_eq_span_single] at hc
  refine Submodule.span_induction
    (p := fun c _ =>
      P.latticeDifferential k c ∈ PlumbingChain.supportedCharacteristicWeightSublevel P k N)
    ?_ (by rw [map_zero]; exact Submodule.zero_mem _) ?_ ?_ hc
  · rintro _ ⟨C, hC, rfl⟩
    rw [latticeDifferential_single]
    exact Submodule.smul_mem _ _
      (P.latticeDifferentialOnGenerator_mem_supportedCharacteristicWeightSublevel k C
        ((P.mem_characteristicCubeWeightSublevel k N C).mp hC))
  · intro x y _ _ hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- The lattice differential sends filtered chains of cubical degree `q + 1` to filtered chains
of cubical degree `q`. -/
theorem latticeDifferential_mem_characteristicWeightDegreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {q : ℕ} {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.characteristicWeightDegreePart P k N (q + 1)) :
    P.latticeDifferential k c ∈ PlumbingChain.characteristicWeightDegreePart P k N q :=
  ⟨P.latticeDifferential_mem_degreePart k hc.1,
    P.latticeDifferential_mem_supportedCharacteristicWeightSublevel k hc.2⟩

/-- The lattice differential restricted to consecutive cubical degrees inside one weight
sublevel. -/
noncomputable def latticeDifferentialWeightDegree (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    PlumbingChain.characteristicWeightDegreePart P k N (q + 1) →ₗ[PlumbingCoefficient]
      PlumbingChain.characteristicWeightDegreePart P k N q :=
  ((P.latticeDifferential k).domRestrict
    (PlumbingChain.characteristicWeightDegreePart P k N (q + 1))).codRestrict
      (PlumbingChain.characteristicWeightDegreePart P k N q) fun c =>
        P.latticeDifferential_mem_characteristicWeightDegreePart k c.property

/-- Forgetting the submodule wrappers, the filtered differential is the total lattice
differential. -/
@[simp]
theorem latticeDifferentialWeightDegree_apply (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ)
    (c : PlumbingChain.characteristicWeightDegreePart P k N (q + 1)) :
    (P.latticeDifferentialWeightDegree k N q c : PlumbingChain V) =
      P.latticeDifferential k c :=
  (rfl)

/-- Two consecutive differentials in a weight sublevel compose to zero. -/
theorem latticeDifferentialWeightDegree_comp (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (P.latticeDifferentialWeightDegree k N q).comp
        (P.latticeDifferentialWeightDegree k N (q + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  simp only [LinearMap.comp_apply, latticeDifferentialWeightDegree_apply, LinearMap.zero_apply]
  exact LinearMap.congr_fun (P.latticeDifferential_comp_self k) (c : PlumbingChain V)

/-- Increasing the weight level commutes with the restricted lattice differential. -/
theorem latticeDifferentialWeightDegree_comp_inclusion (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) (q : ℕ) :
    (P.latticeDifferentialWeightDegree k M q).comp
        (Submodule.inclusion
          (PlumbingChain.characteristicWeightDegreePart_mono P k hNM (q + 1))) =
      (Submodule.inclusion (PlumbingChain.characteristicWeightDegreePart_mono P k hNM q)).comp
        (P.latticeDifferentialWeightDegree k N q) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  simp only [LinearMap.comp_apply, Submodule.coe_inclusion,
    latticeDifferentialWeightDegree_apply]

/-- The cubically graded lattice chain complex restricted to cubes of characteristic weight at
most `N`. -/
noncomputable def latticeWeightSublevelComplex (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) : ChainComplex (ModuleCat PlumbingCoefficient) ℕ :=
  ChainComplex.of
    (fun q => ModuleCat.of PlumbingCoefficient
      (PlumbingChain.characteristicWeightDegreePart P k N q))
    (fun q => ModuleCat.ofHom (R := PlumbingCoefficient)
      (P.latticeDifferentialWeightDegree k N q))
    fun q => by
      rw [← ModuleCat.ofHom_comp, P.latticeDifferentialWeightDegree_comp k N q,
        ModuleCat.ofHom_zero]

/-- The degree-`q` object of the weight-sublevel complex is the corresponding filtered
cubical-degree chain group. -/
@[simp]
theorem latticeWeightSublevelComplex_X (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (P.latticeWeightSublevelComplex k N).X q =
      ModuleCat.of PlumbingCoefficient (PlumbingChain.characteristicWeightDegreePart P k N q) := by
  unfold latticeWeightSublevelComplex
  exact congrFun (ChainComplex.of_X _ _ _) q

-- `ChainComplex.of_X` identifies definitionally equal objects; proof irrelevance normalizes its
-- equality proof so that the explicit transports in the public differential formula reduce.
private theorem latticeWeightSublevelComplex_X_proof_eq_rfl (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    P.latticeWeightSublevelComplex_X k N q = rfl :=
  Subsingleton.elim _ _

/-- The differential of the weight-sublevel complex is the restricted lattice differential. -/
@[simp]
theorem latticeWeightSublevelComplex_d (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (P.latticeWeightSublevelComplex k N).d (q + 1) q =
      eqToHom (P.latticeWeightSublevelComplex_X k N (q + 1)) ≫
        ModuleCat.ofHom (P.latticeDifferentialWeightDegree k N q) ≫
          eqToHom (P.latticeWeightSublevelComplex_X k N q).symm := by
  rw [P.latticeWeightSublevelComplex_X_proof_eq_rfl k N (q + 1),
    P.latticeWeightSublevelComplex_X_proof_eq_rfl k N q]
  unfold latticeWeightSublevelComplex
  simp only [ChainComplex.of_d, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The chain-complex inclusion from weight level `N` to a larger level `M`. -/
noncomputable def latticeWeightSublevelInclusion (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) :
    P.latticeWeightSublevelComplex k N ⟶ P.latticeWeightSublevelComplex k M :=
  ChainComplex.ofHom
    (fun q ↦ ModuleCat.ofHom (Submodule.inclusion
      (PlumbingChain.characteristicWeightDegreePart_mono P k hNM q)))
    (fun q ↦ by
      simp only [latticeWeightSublevelComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp]
      exact congrArg ModuleCat.ofHom
        (P.latticeDifferentialWeightDegree_comp_inclusion k hNM q))

/-- The component of a weight-sublevel inclusion is the corresponding submodule inclusion of
filtered degree parts. -/
theorem latticeWeightSublevelInclusion_f (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) (q : ℕ) :
    (P.latticeWeightSublevelInclusion k hNM).f q =
      eqToHom (P.latticeWeightSublevelComplex_X k N q) ≫
        ModuleCat.ofHom (Submodule.inclusion
          (PlumbingChain.characteristicWeightDegreePart_mono P k hNM q)) ≫
          eqToHom (P.latticeWeightSublevelComplex_X k M q).symm := by
  unfold latticeWeightSublevelInclusion latticeWeightSublevelComplex
  rfl

/-- A weight-sublevel complex inclusion does not change the underlying filtered chain. -/
@[simp]
theorem latticeWeightSublevelInclusion_apply (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) (q : ℕ)
    (c : (P.latticeWeightSublevelComplex k N).X q) :
    eqToHom (P.latticeWeightSublevelComplex_X k M q)
        ((P.latticeWeightSublevelInclusion k hNM).f q c) =
      ModuleCat.ofHom (Submodule.inclusion
        (PlumbingChain.characteristicWeightDegreePart_mono P k hNM q))
          (eqToHom (P.latticeWeightSublevelComplex_X k N q) c) := by
  rw [← CategoryTheory.comp_apply, latticeWeightSublevelInclusion_f]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    CategoryTheory.comp_apply]

/-- The weight-sublevel inclusion from a level to itself is the identity chain map. -/
@[simp]
theorem latticeWeightSublevelInclusion_id (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    P.latticeWeightSublevelInclusion k (le_refl N) =
      𝟙 (P.latticeWeightSublevelComplex k N) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply (cancel_mono (eqToHom (P.latticeWeightSublevelComplex_X k N q))).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [CategoryTheory.comp_apply, latticeWeightSublevelInclusion_apply,
    HomologicalComplex.id_f, CategoryTheory.comp_apply, id_apply]
  apply Subtype.ext
  rfl

/-- Weight-sublevel inclusions compose to the inclusion between the outer levels. -/
@[simp]
theorem latticeWeightSublevelInclusion_comp (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M L : ℤ} (hNM : N ≤ M) (hML : M ≤ L) :
    P.latticeWeightSublevelInclusion k hNM ≫ P.latticeWeightSublevelInclusion k hML =
      P.latticeWeightSublevelInclusion k (hNM.trans hML) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply (cancel_mono (eqToHom (P.latticeWeightSublevelComplex_X k L q))).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [CategoryTheory.comp_apply, HomologicalComplex.comp_f, CategoryTheory.comp_apply,
    latticeWeightSublevelInclusion_apply, latticeWeightSublevelInclusion_apply,
    CategoryTheory.comp_apply, latticeWeightSublevelInclusion_apply]
  apply Subtype.ext
  rfl

/-- The characteristic-weight sublevel complexes and their canonical inclusions, as a filtered
diagram indexed by the ordered set of integers. -/
noncomputable def latticeWeightSublevelFunctor (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    CategoryTheory.Functor ℤ (ChainComplex (ModuleCat PlumbingCoefficient) ℕ) where
  obj N := P.latticeWeightSublevelComplex k N
  map f := P.latticeWeightSublevelInclusion k (leOfHom f)
  map_id N := P.latticeWeightSublevelInclusion_id k N
  map_comp f g := (P.latticeWeightSublevelInclusion_comp k (leOfHom f) (leOfHom g)).symm

private theorem latticeWeightSublevelFunctor_obj_private (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    (P.latticeWeightSublevelFunctor k).obj N = P.latticeWeightSublevelComplex k N :=
  rfl

/-- The object at level `N` in the characteristic-weight filtration diagram is the
corresponding weight-sublevel complex. -/
@[simp]
theorem latticeWeightSublevelFunctor_obj (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    (P.latticeWeightSublevelFunctor k).obj N = P.latticeWeightSublevelComplex k N :=
  P.latticeWeightSublevelFunctor_obj_private k N

-- The functor's object field is definitionally the sublevel complex; normalize the proof used by
-- the transported map formula below without exposing the functor's implementation.
private theorem latticeWeightSublevelFunctor_obj_proof_eq_rfl (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    P.latticeWeightSublevelFunctor_obj k N = rfl :=
  Subsingleton.elim _ _

/-- The map in the characteristic-weight filtration diagram is the canonical inclusion
between the corresponding weight-sublevel complexes. -/
@[simp]
theorem latticeWeightSublevelFunctor_map (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (f : N ⟶ M) :
    eqToHom (P.latticeWeightSublevelFunctor_obj k N).symm ≫
        (P.latticeWeightSublevelFunctor k).map f ≫
      eqToHom (P.latticeWeightSublevelFunctor_obj k M) =
        P.latticeWeightSublevelInclusion k (leOfHom f) := by
  rw [P.latticeWeightSublevelFunctor_obj_proof_eq_rfl k N,
    P.latticeWeightSublevelFunctor_obj_proof_eq_rfl k M]
  unfold latticeWeightSublevelFunctor
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end PlumbingGraph

end TauCeti
