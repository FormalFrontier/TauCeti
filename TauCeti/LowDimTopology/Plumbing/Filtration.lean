/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.LowDimTopology.Plumbing.ChainComplex
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

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

* `TauCeti.PlumbingGraph.cubeWeightSublevel`: cubes of weight at most `N`.
* `TauCeti.PlumbingChain.weightSublevel`: chains supported on those cubes.
* `TauCeti.PlumbingChain.weightDegreePart`: the weight-`≤ N`, cubical-degree-`q` chain group.
* `TauCeti.PlumbingGraph.latticeDifferentialWeightDegree`: the restricted differential.
* `TauCeti.PlumbingGraph.latticeWeightSublevelComplex`: the filtered chain complex at level `N`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions. The filtration by the
sublevel cubical complexes is the construction in A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The set of plumbing cubes whose characteristic weight is at most `N`. -/
def cubeWeightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ) :
    Set (PlumbingCube V) :=
  {C | C.characteristicWeight P k ≤ N}

/-- Membership in a cube-weight sublevel set is the corresponding weight inequality. -/
@[simp]
theorem mem_cubeWeightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ)
    (C : PlumbingCube V) :
    C ∈ P.cubeWeightSublevel k N ↔ C.characteristicWeight P k ≤ N :=
  Iff.rfl

/-- Cube-weight sublevel sets increase with the level. -/
theorem cubeWeightSublevel_mono (P : PlumbingGraph V) (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) : P.cubeWeightSublevel k N ⊆ P.cubeWeightSublevel k M :=
  fun _ hC => hC.trans hNM

/-- The lower face of a cube in a weight sublevel remains in that sublevel. -/
theorem lowerFace_mem_cubeWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {C : PlumbingCube V}
    (hC : C ∈ P.cubeWeightSublevel k N) {v : V} (hv : v ∈ C.directions) :
    C.lowerFace v hv ∈ P.cubeWeightSublevel k N :=
  (PlumbingCube.characteristicWeight_lowerFace_le P k C hv).trans hC

/-- The upper face of a cube in a weight sublevel remains in that sublevel. -/
theorem upperFace_mem_cubeWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {C : PlumbingCube V}
    (hC : C ∈ P.cubeWeightSublevel k N) {v : V} (hv : v ∈ C.directions) :
    C.upperFace v hv ∈ P.cubeWeightSublevel k N :=
  (PlumbingCube.characteristicWeight_upperFace_le P k C hv).trans hC

/-- On a negative-definite plumbing every cube-weight sublevel set is finite.

A cube in the sublevel has its base point in the point-weight sublevel, while its direction set
belongs to the finite type `Finset V`. The pair of these data determines the cube. -/
theorem finite_cubeWeightSublevel (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (N : ℤ) : (P.cubeWeightSublevel k N).Finite := by
  let encode : PlumbingCube V → (V → ℤ) × Finset V := fun C => (C.base, C.directions)
  have hencode : Function.Injective encode := by
    intro C D hCD
    exact PlumbingCube.ext (congrArg Prod.fst hCD) (congrArg Prod.snd hCD)
  have hproduct :
      ({x : V → ℤ | P.characteristicWeight k x ≤ N} ×ˢ
        (Set.univ : Set (Finset V))).Finite :=
    (P.finite_setOfPred_characteristicWeight_le h k N).prod Set.finite_univ
  refine (hproduct.preimage hencode.injOn).subset ?_
  intro C hC
  refine ⟨?_, Set.mem_univ C.directions⟩
  have hbase := P.characteristicWeight_le_characteristicCubeWeight_base
    k C.base C.directions
  rw [← PlumbingCube.characteristicWeight_mk] at hbase
  exact hbase.trans ((P.mem_cubeWeightSublevel k N C).mp hC)

end PlumbingGraph

namespace PlumbingChain

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The `𝔽₂[U]`-submodule of plumbing chains supported on cubes of weight at most `N`. -/
noncomputable def weightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ) :
    Submodule PlumbingCoefficient (PlumbingChain V) :=
  Finsupp.supported PlumbingCoefficient PlumbingCoefficient (P.cubeWeightSublevel k N)

/-- A chain belongs to the weight sublevel exactly when every cube in its support has weight at
most the level. -/
@[simp]
theorem mem_weightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ)
    (c : PlumbingChain V) :
    c ∈ weightSublevel P k N ↔
      ∀ C ∈ c.support, C.characteristicWeight P k ≤ N := by
  rw [weightSublevel, Finsupp.mem_supported]
  rfl

/-- A single cube of weight at most `N`, with any coefficient, belongs to the weight sublevel. -/
theorem single_mem_weightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors) (N : ℤ)
    (C : PlumbingCube V) (a : PlumbingCoefficient)
    (hC : C.characteristicWeight P k ≤ N) :
    Finsupp.single C a ∈ weightSublevel P k N :=
  Finsupp.single_mem_supported PlumbingCoefficient a hC

/-- The chain-level weight submodules increase with the level. -/
theorem weightSublevel_mono (P : PlumbingGraph V) (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) : weightSublevel P k N ≤ weightSublevel P k M :=
  Finsupp.supported_mono (P.cubeWeightSublevel_mono k hNM)

/-- Every plumbing chain belongs to some weight sublevel. -/
theorem exists_mem_weightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors)
    (c : PlumbingChain V) : ∃ N : ℤ, c ∈ weightSublevel P k N := by
  by_cases hc : c = 0
  · exact ⟨0, hc ▸ Submodule.zero_mem _⟩
  · have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hc
    let weights := c.support.image fun C => C.characteristicWeight P k
    have hweights : weights.Nonempty := hs.image _
    let N := weights.max' hweights
    refine ⟨N, (mem_weightSublevel P k N c).mpr fun C hC => ?_⟩
    exact Finset.le_max' weights _ (Finset.mem_image_of_mem _ hC)

/-- The weight filtration exhausts the full plumbing chain module. -/
theorem iSup_weightSublevel_eq_top (P : PlumbingGraph V) (k : P.characteristicVectors) :
    ⨆ N : ℤ, weightSublevel P k N = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨N, hc⟩ := exists_mem_weightSublevel P k c
  exact Submodule.mem_iSup_of_mem N hc

/-- On a negative-definite plumbing, each chain-level weight submodule is finitely generated over
`𝔽₂[U]`. -/
theorem weightSublevel_fg (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (N : ℤ) : (weightSublevel P k N).FG := by
  rw [weightSublevel, Finsupp.supported_eq_span_single]
  exact Submodule.fg_span ((P.finite_cubeWeightSublevel h k N).image fun C => Finsupp.single C 1)

/-- The chains simultaneously lying in cubical degree `q` and weight at most `N`. -/
noncomputable def weightDegreePart (P : PlumbingGraph V) (k : P.characteristicVectors)
    (N : ℤ) (q : ℕ) :
    Submodule PlumbingCoefficient (PlumbingChain V) :=
  degreePart V q ⊓ weightSublevel P k N

/-- Membership in a weight-graded chain group means that every support cube has the specified
cubical dimension and weight at most the level. -/
@[simp]
theorem mem_weightDegreePart (P : PlumbingGraph V) (k : P.characteristicVectors)
    (N : ℤ) (q : ℕ) (c : PlumbingChain V) :
    c ∈ weightDegreePart P k N q ↔
      ∀ C ∈ c.support, C.dimension = q ∧ C.characteristicWeight P k ≤ N := by
  rw [weightDegreePart, Submodule.mem_inf, mem_degreePart, mem_weightSublevel]
  aesop

/-- A basis cube of dimension `q` and weight at most `N` belongs to the corresponding filtered
chain group. -/
theorem single_mem_weightDegreePart (P : PlumbingGraph V) (k : P.characteristicVectors)
    (N : ℤ) (q : ℕ) (C : PlumbingCube V) (a : PlumbingCoefficient)
    (hdim : C.dimension = q) (hweight : C.characteristicWeight P k ≤ N) :
    Finsupp.single C a ∈ weightDegreePart P k N q :=
  ⟨single_mem_degreePart V C a hdim, single_mem_weightSublevel P k N C a hweight⟩

/-- Filtered cubical-degree chain groups increase with the weight level. -/
theorem weightDegreePart_mono (P : PlumbingGraph V) (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) (q : ℕ) :
    weightDegreePart P k N q ≤ weightDegreePart P k M q :=
  inf_le_inf_left _ (weightSublevel_mono P k hNM)

/-- In a fixed cubical degree, the weight filtration exhausts the full degree submodule. -/
theorem iSup_weightDegreePart_eq_degreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    ⨆ N : ℤ, weightDegreePart P k N q = degreePart V q := by
  apply le_antisymm
  · exact iSup_le fun _ => inf_le_left
  · intro c hc
    obtain ⟨N, hN⟩ := exists_mem_weightSublevel P k c
    exact Submodule.mem_iSup_of_mem N ⟨hc, hN⟩

/-- The canonical inclusion from the filtered degree-`q` chains at level `N` to those at a
larger level `M`. -/
noncomputable def weightDegreeInclusion (P : PlumbingGraph V) (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) (q : ℕ) :
    weightDegreePart P k N q →ₗ[PlumbingCoefficient] weightDegreePart P k M q :=
  Submodule.inclusion (weightDegreePart_mono P k hNM q)

/-- A filtered-degree inclusion does not change the underlying plumbing chain. -/
@[simp]
theorem weightDegreeInclusion_apply (P : PlumbingGraph V) (k : P.characteristicVectors)
    {N M : ℤ} (hNM : N ≤ M) (q : ℕ) (c : weightDegreePart P k N q) :
    (weightDegreeInclusion P k hNM q c : PlumbingChain V) = c :=
  (rfl)

/-- On a negative-definite plumbing, every filtered cubical-degree chain group is finitely
generated over `𝔽₂[U]`. -/
theorem weightDegreePart_fg (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (weightDegreePart P k N q).FG := by
  have hsupport : weightDegreePart P k N q =
      Finsupp.supported PlumbingCoefficient PlumbingCoefficient
        {C | C.dimension = q ∧ C.characteristicWeight P k ≤ N} := by
    ext c
    rw [mem_weightDegreePart, Finsupp.mem_supported]
    rfl
  have hfinite : {C : PlumbingCube V |
      C.dimension = q ∧ C.characteristicWeight P k ≤ N}.Finite :=
    (P.finite_cubeWeightSublevel h k N).subset fun _ hC => hC.2
  rw [hsupport, Finsupp.supported_eq_span_single]
  exact Submodule.fg_span (hfinite.image fun C => Finsupp.single C 1)

end PlumbingChain

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The differential of a cube in a weight sublevel is supported in the same sublevel. -/
theorem latticeDifferentialOnGenerator_mem_weightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} (C : PlumbingCube V)
    (hC : C.characteristicWeight P k ≤ N) :
    P.latticeDifferentialOnGenerator k C ∈ PlumbingChain.weightSublevel P k N := by
  classical
  rw [latticeDifferentialOnGenerator_def]
  apply Submodule.sum_mem
  intro v _
  apply Submodule.add_mem
  · exact PlumbingChain.single_mem_weightSublevel P k N _ _
      ((PlumbingCube.characteristicWeight_lowerFace_le P k C v.property).trans hC)
  · exact PlumbingChain.single_mem_weightSublevel P k N _ _
      ((PlumbingCube.characteristicWeight_upperFace_le P k C v.property).trans hC)

/-- The lattice differential preserves every chain-level weight submodule. -/
theorem latticeDifferential_mem_weightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.weightSublevel P k N) :
    P.latticeDifferential k c ∈ PlumbingChain.weightSublevel P k N := by
  rw [PlumbingChain.weightSublevel, Finsupp.supported_eq_span_single] at hc
  refine Submodule.span_induction
    (p := fun c _ => P.latticeDifferential k c ∈ PlumbingChain.weightSublevel P k N)
    ?_ (by rw [map_zero]; exact Submodule.zero_mem _) ?_ ?_ hc
  · rintro _ ⟨C, hC, rfl⟩
    rw [latticeDifferential_single]
    exact Submodule.smul_mem _ _ (P.latticeDifferentialOnGenerator_mem_weightSublevel k C hC)
  · intro x y _ _ hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- The lattice differential sends filtered chains of cubical degree `q + 1` to filtered chains
of cubical degree `q`. -/
theorem latticeDifferential_mem_weightDegreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {q : ℕ} {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.weightDegreePart P k N (q + 1)) :
    P.latticeDifferential k c ∈ PlumbingChain.weightDegreePart P k N q :=
  ⟨P.latticeDifferential_mem_degreePart k hc.1,
    P.latticeDifferential_mem_weightSublevel k hc.2⟩

/-- The lattice differential restricted to consecutive cubical degrees inside one weight
sublevel. -/
noncomputable def latticeDifferentialWeightDegree (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    PlumbingChain.weightDegreePart P k N (q + 1) →ₗ[PlumbingCoefficient]
      PlumbingChain.weightDegreePart P k N q :=
  ((P.latticeDifferential k).domRestrict
    (PlumbingChain.weightDegreePart P k N (q + 1))).codRestrict
      (PlumbingChain.weightDegreePart P k N q) fun c =>
        P.latticeDifferential_mem_weightDegreePart k c.property

/-- Forgetting the submodule wrappers, the filtered differential is the total lattice
differential. -/
@[simp]
theorem latticeDifferentialWeightDegree_apply (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ)
    (c : PlumbingChain.weightDegreePart P k N (q + 1)) :
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
        (PlumbingChain.weightDegreeInclusion P k hNM (q + 1)) =
      (PlumbingChain.weightDegreeInclusion P k hNM q).comp
        (P.latticeDifferentialWeightDegree k N q) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  simp only [LinearMap.comp_apply, PlumbingChain.weightDegreeInclusion_apply,
    latticeDifferentialWeightDegree_apply]

/-- The cubically graded lattice chain complex restricted to cubes of characteristic weight at
most `N`. -/
noncomputable def latticeWeightSublevelComplex (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) : ChainComplex (ModuleCat PlumbingCoefficient) ℕ :=
  ChainComplex.of
    (fun q => ModuleCat.of PlumbingCoefficient (PlumbingChain.weightDegreePart P k N q))
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
      ModuleCat.of PlumbingCoefficient (PlumbingChain.weightDegreePart P k N q) := by
  unfold latticeWeightSublevelComplex
  exact congrFun (ChainComplex.of_X _ _ _) q

/-- The differential of the weight-sublevel complex is the restricted lattice differential. -/
@[simp]
theorem latticeWeightSublevelComplex_d (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    HEq ((P.latticeWeightSublevelComplex k N).d (q + 1) q)
      (ModuleCat.ofHom (P.latticeDifferentialWeightDegree k N q) :
        ModuleCat.of PlumbingCoefficient (PlumbingChain.weightDegreePart P k N (q + 1)) ⟶
          ModuleCat.of PlumbingCoefficient (PlumbingChain.weightDegreePart P k N q)) := by
  rw [latticeWeightSublevelComplex]
  exact heq_of_eq (ChainComplex.of_d
    (fun r => ModuleCat.of PlumbingCoefficient (PlumbingChain.weightDegreePart P k N r))
    (fun r => ModuleCat.ofHom (R := PlumbingCoefficient)
      (P.latticeDifferentialWeightDegree k N r)) q)

end PlumbingGraph

end TauCeti
