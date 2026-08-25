/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Bounded
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The lattice complex has no homology in top cubical degree

`Bounded.lean` locates Némethi's lattice homology below the number of plumbing vertices only
because the chain groups themselves vanish there. This file removes the remaining top degree,
where the chain group is as large as it ever gets: the lattice differential is *injective* on
chains all of whose cubes carry the same nonempty direction set, and the top-degree chain group
`C_{card V}` is exactly such a piece. So `ℍ_q` vanishes for every `q ≥ Fintype.card V` as soon as
the plumbing has a vertex, and a one-vertex plumbing has its whole lattice homology concentrated
in cubical degree zero.

The mechanism is a maximal-coordinate argument, not a weight argument, so it needs no
negative-definiteness and no properness of the characteristic weight. Fix a direction `v` and a
cube `C₀` in the support whose base point has the largest `v`-coordinate. Its upper face
`(x₀ + E_v, S \ v)` in the direction `v` can be reached by only two cubes with direction set `S`:
as the upper face of `(x₀, S)` and as the lower face of `(x₀ + E_v, S)`. The second is barred by
maximality, so the coefficient of that face in the differential is a single power of `U` times the
coefficient of `C₀`, and multiplying by a power of `U` annihilates no nonzero polynomial. The
argument really does use a common direction set, and so does not run in lower degrees: there a
single codimension-one face is shared by cubes of different direction sets, and their
contributions can cancel.

## Main results

* `TauCeti.PlumbingGraph.latticeDifferentialOnGenerator_apply`: the coefficient of the weighted
  face sum of a cube at another cube.
* `TauCeti.PlumbingGraph.latticeDifferential_ne_zero_of_directions_eq`: the lattice differential
  does not annihilate a nonzero chain whose cubes share a nonempty direction set, so it is
  injective on those chains.
* `TauCeti.PlumbingGraph.latticeDifferentialDegree_injective_of_succ_eq_card`: in the top cubical
  degree the graded lattice differential is injective.
* `TauCeti.PlumbingGraph.exactAt_latticeChainComplex_of_card_le` and
  `TauCeti.PlumbingGraph.isZero_latticeChainHomology_of_card_le`: the complex is exact, and
  lattice homology vanishes, in every cubical degree at least the number of plumbing vertices,
  provided there is one.

That vanishing is not vacuous, and it is a statement about the differential rather than about the
chain groups: `isZero_latticeChainComplex_X_iff_card_lt` read at `q = Fintype.card V` says the
chain group in the top degree is nonzero. Read at `Fintype.card V = 1`,
`isZero_latticeChainHomology_of_card_le` says the whole lattice homology of a one-vertex plumbing
sits in cubical degree zero.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
which asks for Némethi's lattice homology together with computations for explicit plumbings: the
degrees in which the invariant can be nonzero have to be known before any of them is computed.
The cubical complex and its face conventions follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory Limits

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The coefficient of the weighted face sum of a cube `C` at a cube `D`: each direction of `C`
contributes its lower-face and upper-face powers of `U`, and only when that face is `D`. -/
theorem latticeDifferentialOnGenerator_apply [DecidableEq (PlumbingCube V)]
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C D : PlumbingCube V) :
    P.latticeDifferentialOnGenerator k C D =
      ∑ v ∈ C.directions.attach,
        ((if C.lowerFace v.1 v.2 = D then
            Polynomial.X ^ PlumbingCube.characteristicLowerFaceExponent P k C v.1 else 0) +
          if C.upperFace v.1 v.2 = D then
            Polynomial.X ^ PlumbingCube.characteristicUpperFaceExponent P k C v.2 else 0) := by
  rw [latticeDifferentialOnGenerator_def, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun v _ => by simp [Finsupp.add_apply, Finsupp.single_apply]

/-! ### The cubes that can reach a fixed upper face -/

variable {T : Finset V} {v : V}

omit [Fintype V] in
/-- A lower face never reaches the upper face of a cube whose base point is at least as far
along the chosen direction: the lower face keeps its own base point, while the upper face has
moved one step further. -/
private theorem lowerFace_ne_upperFace {C C₀ : PlumbingCube V} {w : V}
    (hw : w ∈ C.directions) (hvC₀ : v ∈ C₀.directions) (hle : C.base v ≤ C₀.base v) :
    C.lowerFace w hw ≠ C₀.upperFace v hvC₀ := by
  intro hface
  have hbase : C.base = C₀.base + Pi.single v (1 : ℤ) := by
    simpa using congrArg PlumbingCube.base hface
  have hval := congrFun hbase v
  simp only [Pi.add_apply, Pi.single_eq_same] at hval
  omega

omit [Fintype V] in
/-- The upper face of a cube in a direction `w` is the upper face of `C₀` in the direction `v`
only for the same direction and the same cube, once both cubes carry the direction set `T`. -/
private theorem eq_of_upperFace_eq {C C₀ : PlumbingCube V} {w : V}
    (hCdir : C.directions = T) (hC₀dir : C₀.directions = T) (hv : v ∈ T)
    (hw : w ∈ C.directions) (hvC₀ : v ∈ C₀.directions)
    (hface : C.upperFace w hw = C₀.upperFace v hvC₀) : w = v ∧ C = C₀ := by
  have hdir : T.erase w = T.erase v := by
    have := congrArg PlumbingCube.directions hface
    simpa [hCdir, hC₀dir] using this
  have hwv : w = v := ((Finset.erase_inj T hv).mp hdir.symm).symm
  subst hwv
  have hbase : C.base + Pi.single w (1 : ℤ) = C₀.base + Pi.single w (1 : ℤ) := by
    simpa using congrArg PlumbingCube.base hface
  exact ⟨rfl, PlumbingCube.ext (by simpa using hbase) (hCdir.trans hC₀dir.symm)⟩

/-! ### Injectivity on a fixed direction set -/

/-- The lattice differential does not annihilate a nonzero chain all of whose cubes carry the same
nonempty direction set.

Choosing a cube `C₀` in the support whose base point is furthest along a direction `v` of that
set, the coefficient of the upper face of `C₀` in the direction `v` is a single power of `U`
times the coefficient of `C₀`. -/
theorem latticeDifferential_ne_zero_of_directions_eq
    (P : PlumbingGraph V) (k : P.characteristicVectors) (hv : v ∈ T)
    {c : PlumbingChain V} (hdir : ∀ C ∈ c.support, C.directions = T) (hc : c ≠ 0) :
    P.latticeDifferential k c ≠ 0 := by
  classical
  obtain ⟨C₀, hC₀mem, hC₀max⟩ :=
    c.support.exists_max_image (fun C => C.base v) (Finsupp.support_nonempty_iff.mpr hc)
  have hvC₀ : v ∈ C₀.directions := by rw [hdir C₀ hC₀mem]; exact hv
  set F := C₀.upperFace v hvC₀
  -- Every cube in the support other than `C₀` misses the face `F` entirely.
  have hother : ∀ C ∈ c.support, C ≠ C₀ → P.latticeDifferentialOnGenerator k C F = 0 := by
    intro C hCmem hCne
    rw [latticeDifferentialOnGenerator_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [ite_eq_right (lowerFace_ne_upperFace w.2 hvC₀ (hC₀max C hCmem)),
      ite_eq_right fun hface => hCne (eq_of_upperFace_eq (hdir C hCmem) (hdir C₀ hC₀mem) hv w.2 hvC₀
        hface).2]
    exact add_zero 0
  -- The cube `C₀` itself contributes exactly one power of `U`.
  have hself : P.latticeDifferentialOnGenerator k C₀ F =
      Polynomial.X ^ PlumbingCube.characteristicUpperFaceExponent P k C₀ hvC₀ := by
    rw [latticeDifferentialOnGenerator_apply]
    refine (Finset.sum_eq_single_of_mem ⟨v, hvC₀⟩ (Finset.mem_attach _ _) ?_).trans ?_
    · intro w _ hwv
      rw [ite_eq_right (lowerFace_ne_upperFace w.2 hvC₀ le_rfl),
        ite_eq_right fun hface => hwv (Subtype.ext
          (eq_of_upperFace_eq (hdir C₀ hC₀mem) (hdir C₀ hC₀mem) hv w.2 hvC₀ hface).1)]
      exact add_zero 0
    · rw [ite_eq_right (lowerFace_ne_upperFace hvC₀ hvC₀ le_rfl), ite_eq_left rfl]
      exact zero_add _
  -- Hence the differential has a nonzero coefficient at `F`.
  intro hzero
  have hval : (P.latticeDifferential k c) F = 0 := by rw [hzero]; rfl
  rw [latticeDifferential_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem C₀ hC₀mem
      (fun C hCmem hCne => by rw [Finsupp.smul_apply, hother C hCmem hCne, smul_zero]),
    Finsupp.smul_apply, hself, smul_eq_mul] at hval
  exact Finsupp.mem_support_iff.mp hC₀mem (Polynomial.mul_X_pow_eq_zero hval)

/-- In the top cubical degree the graded lattice differential is injective: every chain there is
supported on cubes with the full direction set. -/
theorem latticeDifferentialDegree_injective_of_succ_eq_card
    (P : PlumbingGraph V) (k : P.characteristicVectors) {q : ℕ}
    (hq : q + 1 = Fintype.card V) :
    Function.Injective (P.latticeDifferentialDegree k q) := by
  classical
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, ← hq]
    exact Nat.succ_pos q
  obtain ⟨v, hv⟩ := hne
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hcne
  refine P.latticeDifferential_ne_zero_of_directions_eq k hv
    (c := (c : PlumbingChain V)) (fun C hC => ?_) (fun h => hcne (Subtype.ext h)) ?_
  · have hdim := (PlumbingChain.mem_degreePart V (q + 1) c).mp c.property C hC
    exact Finset.eq_univ_of_card C.directions (by rw [← hq]; exact hdim)
  · rw [← P.latticeDifferentialDegree_apply k q c, hc]
    exact ZeroMemClass.coe_zero _

/-- The cubically graded lattice complex is exact in the top cubical degree of a plumbing graph
with at least one vertex. -/
private theorem exactAt_latticeChainComplex_card [Nonempty V]
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.latticeChainComplex k).ExactAt (Fintype.card V) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 :=
    ⟨Fintype.card V - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have hmono : Mono ((P.latticeChainComplex k).d (m + 1) m) := by
    rw [P.latticeChainComplex_d k m]
    refine mono_comp' inferInstance (mono_comp' ?_ inferInstance)
    rw [ModuleCat.mono_iff_injective]
    simpa using P.latticeDifferentialDegree_injective_of_succ_eq_card k hm.symm
  rw [hm, HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (ChainComplex.prev ℕ (m + 1))
      (ChainComplex.next_nat_succ m), ShortComplex.exact_iff_mono]
  · exact hmono
  · refine IsZero.eq_zero_of_src ?_ _
    exact (P.isZero_latticeChainComplex_X_iff_card_lt k (m + 2)).mpr (by omega)

/-- The cubically graded lattice complex is exact in every cubical degree at least the number of
vertices of a plumbing graph with at least one vertex. -/
theorem exactAt_latticeChainComplex_of_card_le [Nonempty V]
    (P : PlumbingGraph V) (k : P.characteristicVectors) {q : ℕ}
    (hq : Fintype.card V ≤ q) :
    (P.latticeChainComplex k).ExactAt q := by
  rcases eq_or_lt_of_le hq with hq' | hq'
  · rw [← hq']
    exact P.exactAt_latticeChainComplex_card k
  · exact P.exactAt_latticeChainComplex_of_card_lt k q hq'

/-- Lattice homology vanishes in every cubical degree at least the number of vertices of a
plumbing graph with at least one vertex. This is sharp in the sense that the chain group in the
top degree `Fintype.card V` is nonzero: the vanishing is a statement about the differential,
not about the chain groups. -/
theorem isZero_latticeChainHomology_of_card_le [Nonempty V]
    (P : PlumbingGraph V) (k : P.characteristicVectors) {q : ℕ}
    (hq : Fintype.card V ≤ q) :
    IsZero (P.latticeChainHomology k q) := by
  rw [P.latticeChainHomology_def k q]
  exact (P.exactAt_latticeChainComplex_of_card_le k hq).isZero_homology

end PlumbingGraph

end TauCeti
