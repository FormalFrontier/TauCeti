/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Tower
import TauCeti.LowDimTopology.Plumbing.Cube.Weight.Recursion
import TauCeti.LowDimTopology.Plumbing.DiagonalDominance
import TauCeti.LowDimTopology.Plumbing.TopDegree
import TauCeti.LowDimTopology.Plumbing.Weight.Polarization

/-!
# The lattice homology of a one-vertex plumbing

Némethi's lattice homology of a plumbing graph `P` with a characteristic covector `k` is the
homology of the free `𝔽₂[U]`-module on the cubes of the lattice `V → ℤ`, each codimension-one
face in the differential weighted by the drop in the characteristic cube weight. This file
computes the total, ungraded homology of that complex when `P` has a single vertex of negative
framing, the smallest plumbing whose differential is not forced to vanish: the answer is a single
`U`-tower,

`ℍ(P, k) ≅ 𝔽₂[U]`,

for every characteristic covector, hence for every spin^c structure. A one-vertex plumbing with
framing `w < 0` is the disc bundle over the sphere with Euler number `w`, whose boundary is the
lens space `L(-w, 1)`, and one tower per spin^c structure agrees with the lens-space computation
of Ozsváth–Szabó, [arXiv:math/0203265](https://arxiv.org/abs/math/0203265). Up to now the only
computed lattice homology was that of the zero-vertex plumbing, where the differential vanishes
for lack of directions.

Two facts drive the computation. First, the lattice is `ℤ`, so the only cubes are lattice points
and edges; the lattice differential is injective on chains of edges, so every cycle is a chain of
lattice points. Second, the characteristic weight is a convex quadratic in the single lattice
coordinate: its first difference `χ_k(x + E) - χ_k(x) = -(k_v + w) / 2 - w x` increases with `x`
because `w < 0`, so from a minimizer `x₀` the weight is nondecreasing to the right and
nonincreasing to the left. An edge therefore relates its two endpoints by
`[x'] = U ^ (χ_k(x') - χ_k(x)) [x]` with `x` the lighter endpoint, and inducting in both
directions along the lattice writes every lattice point as `U ^ (χ_k(x) - min χ_k)` times `[x₀]`.
So the class of `x₀` generates lattice homology, and the augmentation already used for the
`U`-tower shows it generates freely.

## Main definitions

* `TauCeti.PlumbingGraph.coefficientEquivLatticeHomologyOfUnique`: the lattice homology of a
  one-vertex negative-definite plumbing, identified with `𝔽₂[U]` using a specified
  augmentation-one cycle.
* `TauCeti.oneVertexPlumbing`: the plumbing graph with a single vertex of a given framing.

## Main results

* `TauCeti.PlumbingGraph.directions_eq_empty_of_latticeDifferential_eq_zero_of_unique`: on a
  rank-one lattice every cycle is a chain of lattice points.
* `TauCeti.PlumbingGraph.single_sub_smul_single_mem_range_of_unique`: every lattice point of a
  rank-one negative-definite plumbing lattice is a `U`-multiple of a minimal-weight one, modulo
  boundaries.
* `TauCeti.PlumbingGraph.latticeHomologyCycleMap_bijective_of_unique`: for a rank-one
  negative-definite plumbing, the cycle map of any augmentation-one cycle is an isomorphism
  `𝔽₂[U] ≅ ℍ(P, k)`.
* `TauCeti.coefficientEquivOneVertexPlumbingLatticeHomology`: that isomorphism for the explicit
  one-vertex plumbing of negative framing.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose acceptance criterion asks for the lattice homology of a concrete negative-definite plumbing,
matched against the literature. The complex and its weights follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3. The comparison computation for
`HF⁻` of lens spaces is due to P. Ozsváth and Z. Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

universe u

namespace PlumbingChain

variable {V : Type u}

/-- Telescoping one step: comparing `a` with a multiple of `c` splits into the comparison of `a`
with a multiple of an intermediate chain `b` and that comparison for `b` and `c`. -/
private theorem sub_mul_smul (r s : PlumbingCoefficient) (a b c : PlumbingChain V) :
    a - (r * s) • c = (a - r • b) + r • (b - s • c) := by
  rw [smul_sub, smul_smul]
  abel

end PlumbingChain

namespace PlumbingGraph

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ### The rank-one lattice -/

section Unique

variable [Unique V] (P : PlumbingGraph V) (k : P.characteristicVectors)

/-- On a rank-one lattice the first difference of the characteristic weight along the unique basis
direction is an affine function of the lattice coordinate, with slope the negative of the
framing. -/
private theorem characteristicWeight_add_single_sub (x : V → ℤ) :
    P.characteristicWeight k (x + Pi.single default 1) - P.characteristicWeight k x =
      -((k.val default + P.weight default) / 2) - x default * P.weight default := by
  have hsum : (∑ i, x i * P.intersectionMatrix i default) = x default * P.weight default := by
    rw [Finset.univ_unique, Finset.sum_singleton, intersectionMatrix_diag]
  rw [characteristicWeight_add_single, hsum]
  ring

/-- The first difference of the characteristic weight is monotone along the lattice, since the
framing of a negative-definite plumbing is negative. -/
private theorem characteristicWeight_add_single_sub_le (hw : P.weight default < 0) (x y : V → ℤ)
    (hxy : x default ≤ y default) :
    P.characteristicWeight k (x + Pi.single default 1) - P.characteristicWeight k x ≤
      P.characteristicWeight k (y + Pi.single default 1) - P.characteristicWeight k y := by
  rw [characteristicWeight_add_single_sub, characteristicWeight_add_single_sub]
  have h1 : (0 : ℤ) ≤ y default - x default := by omega
  have h2 : (0 : ℤ) < -P.weight default := by omega
  nlinarith

variable {x₀ : V → ℤ}
  (hmin : ∀ y : V → ℤ, P.characteristicWeight k x₀ ≤ P.characteristicWeight k y)

include hmin in
/-- Beyond a minimizer the characteristic weight is nondecreasing. -/
private theorem characteristicWeight_le_add_single (hw : P.weight default < 0) {x : V → ℤ}
    (hle : x₀ default ≤ x default) :
    P.characteristicWeight k x ≤ P.characteristicWeight k (x + Pi.single default 1) := by
  have h0 : 0 ≤ P.characteristicWeight k (x₀ + Pi.single default 1) -
      P.characteristicWeight k x₀ := sub_nonneg.mpr (hmin _)
  have := characteristicWeight_add_single_sub_le P k hw x₀ x hle
  linarith

include hmin in
/-- Before a minimizer the characteristic weight is nonincreasing. -/
private theorem characteristicWeight_add_single_le (hw : P.weight default < 0) {x : V → ℤ}
    (hlt : x default < x₀ default) :
    P.characteristicWeight k (x + Pi.single default 1) ≤ P.characteristicWeight k x := by
  have hz : (x₀ - Pi.single default (1 : ℤ)) + Pi.single default 1 = x₀ := sub_add_cancel _ _
  have hzd : (x₀ - Pi.single default (1 : ℤ) : V → ℤ) default = x₀ default - 1 := by simp
  have h0 : P.characteristicWeight k ((x₀ - Pi.single default (1 : ℤ)) + Pi.single default 1) -
      P.characteristicWeight k (x₀ - Pi.single default (1 : ℤ)) ≤ 0 := by
    rw [hz]
    linarith [hmin (x₀ - Pi.single default (1 : ℤ))]
  have := characteristicWeight_add_single_sub_le P k hw x (x₀ - Pi.single default (1 : ℤ))
    (by omega)
  linarith

omit [Unique V] in
/-- Compose two congruences modulo lattice boundaries. -/
private theorem sub_smul_mem_range_trans {r s : PlumbingCoefficient} {a b c : PlumbingChain V}
    (h₁ : a - r • b ∈ LinearMap.range (P.latticeDifferential k))
    (h₂ : b - s • c ∈ LinearMap.range (P.latticeDifferential k)) :
    a - (r * s) • c ∈ LinearMap.range (P.latticeDifferential k) := by
  rw [PlumbingChain.sub_mul_smul]
  exact Submodule.add_mem _ h₁ (Submodule.smul_mem _ r h₂)

/-- Powers of `U` telescope when the three exponents come from an ordered triple of weights. -/
private theorem X_pow_sub_mul_X_pow_sub {a b c : ℤ} (hcb : c ≤ b) (hba : b ≤ a) :
    (Polynomial.X : PlumbingCoefficient) ^ (a - b).toNat *
        Polynomial.X ^ (b - c).toNat = Polynomial.X ^ (a - c).toNat := by
  rw [← pow_add]
  congr 1
  omega

include hmin in
/-- The lattice-point generation statement, as an induction on the lattice coordinate: from a
minimizer the characteristic weight increases monotonically in both directions, so each step
across an edge multiplies the class of the previous point by the intervening `U`-power. -/
private theorem single_sub_smul_single_mem_range_aux (hw : P.weight default < 0) :
    ∀ n : ℤ, ∀ y : V → ℤ, y default = n →
      Finsupp.single (⟨y, ∅⟩ : PlumbingCube V) 1 -
          (Polynomial.X : PlumbingCoefficient) ^
              (P.characteristicWeight k y - P.characteristicWeight k x₀).toNat •
            Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 ∈
        LinearMap.range (P.latticeDifferential k) := by
  have hbase : ∀ y : V → ℤ, y default = x₀ default →
      Finsupp.single (⟨y, ∅⟩ : PlumbingCube V) 1 -
          (Polynomial.X : PlumbingCoefficient) ^
              (P.characteristicWeight k y - P.characteristicWeight k x₀).toNat •
            Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 ∈
        LinearMap.range (P.latticeDifferential k) := by
    intro y hy
    have hyx : y = x₀ := funext fun i => by rw [Subsingleton.elim i default]; exact hy
    rw [hyx, sub_self, Int.toNat_zero, pow_zero, one_smul, sub_self]
    exact Submodule.zero_mem _
  intro n
  rcases le_total (x₀ default) n with hle | hle
  · induction n, hle using Int.leInduction with
    | base => exact hbase
    | succ n hn ih =>
      intro y hy
      have hzd : (y - Pi.single default (1 : ℤ) : V → ℤ) default = n := by simp [hy]
      have hzy : y - Pi.single default (1 : ℤ) + Pi.single default 1 = y := sub_add_cancel _ _
      have hle' : P.characteristicWeight k (y - Pi.single default (1 : ℤ)) ≤
          P.characteristicWeight k (y - Pi.single default (1 : ℤ) + Pi.single default 1) :=
        characteristicWeight_le_add_single P k hmin hw (by rw [hzd]; exact hn)
      have hminz := hmin (y - Pi.single default (1 : ℤ))
      have hstep :=
        single_add_sub_smul_single_mem_range P k (y - Pi.single default (1 : ℤ)) default hle'
      have hind := ih (y - Pi.single default (1 : ℤ)) hzd
      have hsum := sub_smul_mem_range_trans P k hstep hind
      rw [X_pow_sub_mul_X_pow_sub hminz hle'] at hsum
      rwa [hzy] at hsum
  · induction n, hle using Int.leInductionDown with
    | base => exact hbase
    | pred n hn ih =>
      intro y hy
      have hyd : (y + Pi.single default (1 : ℤ) : V → ℤ) default = n := by simp [hy]
      have hle' : P.characteristicWeight k (y + Pi.single default 1) ≤
          P.characteristicWeight k y :=
        characteristicWeight_add_single_le P k hmin hw (by omega)
      have hminz := hmin (y + Pi.single default (1 : ℤ))
      have hstep := single_sub_smul_single_add_mem_range P k y default hle'
      have hind := ih (y + Pi.single default (1 : ℤ)) hyd
      have hsum := sub_smul_mem_range_trans P k hstep hind
      rwa [X_pow_sub_mul_X_pow_sub hminz hle'] at hsum

include hmin in
/-- Modulo boundaries, a chain of lattice points is its augmentation times a fixed minimal-weight
lattice point. -/
private theorem sub_augmentation_smul_single_mem_range_aux (hw : P.weight default < 0)
    (hx₀ : P.characteristicWeight k x₀ = P.sInfCharacteristicWeight k) {c : PlumbingChain V}
    (hc : ∀ C ∈ c.support, C.directions = ∅) :
    c - P.latticeAugmentation k c • Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 ∈
      LinearMap.range (P.latticeDifferential k) := by
  classical
  set F : PlumbingChain V →ₗ[PlumbingCoefficient] PlumbingChain V :=
    LinearMap.id - (LinearMap.toSpanSingleton PlumbingCoefficient (PlumbingChain V)
      (Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1)).comp (P.latticeAugmentation k) with hF
  have hFapply : ∀ z : PlumbingChain V,
      F z = z - P.latticeAugmentation k z •
        Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 := by
    intro z
    rw [hF]
    rfl
  have hcsum : F c = c.sum fun C a => F (Finsupp.single C a) := by
    rw [← map_finsuppSum, Finsupp.sum_single]
  rw [← hFapply c, hcsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun C hC => ?_
  rw [← Finsupp.smul_single_one C (c C), map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [hFapply, latticeAugmentation_single,
    P.latticeAugmentationCoefficient_of_directions_eq_empty k (hc C hC), one_mul]
  have hbase := single_sub_smul_single_mem_range_aux P k hmin hw (C.base default) C.base rfl
  rw [hx₀, ← (PlumbingCube.ext rfl (hc C hC) : C = ⟨C.base, ∅⟩)] at hbase
  exact hbase

end Unique

/-! ### Cycles of a rank-one lattice -/

/-- On a rank-one plumbing lattice every cycle is a chain of lattice points: the only cubes of
positive dimension are the edges, and the lattice differential is injective on chains of edges. -/
theorem directions_eq_empty_of_latticeDifferential_eq_zero_of_unique [Unique V]
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {c : PlumbingChain V} (hc : P.latticeDifferential k c = 0)
    {C : PlumbingCube V} (hC : C ∈ c.support) : C.directions = ∅ := by
  classical
  by_contra hne
  set p : PlumbingCube V → Prop := fun D => D.directions = ∅
  have hzero : P.latticeDifferential k (c.filter p) = 0 := by
    refine P.latticeDifferential_eq_zero_of_forall_directions_eq_empty k fun D hD => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hD
    exact hD.2
  have hdir : ∀ D ∈ (c.filter fun D => ¬ p D).support, D.directions = (Finset.univ : Finset V) := by
    intro D hD
    rw [Finsupp.support_filter, Finset.mem_filter] at hD
    rw [Finset.univ_unique]
    refine (Finset.subset_singleton_iff.mp ?_).resolve_left hD.2
    rw [← Finset.univ_unique]
    exact Finset.subset_univ D.directions
  have hne' : (c.filter fun D => ¬ p D) ≠ 0 := by
    intro h0
    have : C ∈ (c.filter fun D => ¬ p D).support := by
      rw [Finsupp.support_filter, Finset.mem_filter]
      exact ⟨hC, hne⟩
    rw [h0] at this
    simp at this
  refine P.latticeDifferential_ne_zero_of_directions_eq k (Finset.mem_univ (default : V))
    hdir hne' ?_
  have hsum := Finsupp.filter_add_filter_not c p
  rw [← hsum, map_add, hzero, zero_add] at hc
  exact hc

/-! ### The lattice homology of a one-vertex plumbing -/

section Homology

variable [Unique V] (P : PlumbingGraph V) (k : P.characteristicVectors)

omit [Unique V] in
/-- A lattice point realizing the infimum of the characteristic weight is a minimizer. -/
private theorem characteristicWeight_le_of_eq_sInf (h : P.IsNegativeDefinite) {x₀ : V → ℤ}
    (hx₀ : P.characteristicWeight k x₀ = P.sInfCharacteristicWeight k) (y : V → ℤ) :
    P.characteristicWeight k x₀ ≤ P.characteristicWeight k y := by
  rw [hx₀]
  exact P.sInfCharacteristicWeight_le h k y

/-- Every lattice point of a rank-one negative-definite plumbing lattice is, modulo boundaries,
`U ^ (χ_k(x) - min χ_k)` times a fixed lattice point of minimal weight. -/
theorem single_sub_smul_single_mem_range_of_unique (h : P.IsNegativeDefinite) {x₀ : V → ℤ}
    (hx₀ : P.characteristicWeight k x₀ = P.sInfCharacteristicWeight k) (x : V → ℤ) :
    Finsupp.single (⟨x, ∅⟩ : PlumbingCube V) 1 -
        (Polynomial.X : PlumbingCoefficient) ^
            (P.characteristicWeight k x - P.sInfCharacteristicWeight k).toNat •
          Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 ∈
      LinearMap.range (P.latticeDifferential k) := by
  have hmin := characteristicWeight_le_of_eq_sInf P k h hx₀
  have hbase := single_sub_smul_single_mem_range_aux P k hmin
    (IsNegativeDefinite.weight_neg P h default) (x default) x rfl
  rwa [hx₀] at hbase

/-- On a rank-one negative-definite plumbing every cycle differs from a multiple of a fixed
minimal-weight lattice point by a boundary: cycles are chains of lattice points, and each lattice
point is a `U`-multiple of the minimal one. -/
theorem sub_augmentation_smul_single_mem_range_of_unique (h : P.IsNegativeDefinite)
    {x₀ : V → ℤ}
    (hx₀ : P.characteristicWeight k x₀ = P.sInfCharacteristicWeight k) {c : PlumbingChain V}
    (hc : P.latticeDifferential k c = 0) :
    c - P.latticeAugmentation k c • Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1 ∈
      LinearMap.range (P.latticeDifferential k) := by
  have hmin := characteristicWeight_le_of_eq_sInf P k h hx₀
  exact sub_augmentation_smul_single_mem_range_aux P k hmin
    (IsNegativeDefinite.weight_neg P h default) hx₀
    fun C hC => P.directions_eq_empty_of_latticeDifferential_eq_zero_of_unique k hc hC

/-- **The lattice homology of a one-vertex negative-definite plumbing is a single `U`-tower.**
Any cycle of augmentation one has bijective cycle map: injectivity is the tower of
`latticeHomologyCycleMap_injective`, and surjectivity holds because every cycle is a chain of
lattice points and every lattice point is a `U`-multiple of a minimal-weight one. -/
theorem latticeHomologyCycleMap_bijective_of_unique (h : P.IsNegativeDefinite)
    (c : PlumbingChain V)
    (hc : P.latticeDifferential k c = 0) (hone : P.latticeAugmentation k c = 1) :
    Function.Bijective (P.latticeHomologyCycleMap k c hc) := by
  obtain ⟨x₀, hx₀⟩ := P.exists_characteristicWeight_eq_sInfCharacteristicWeight h k
  refine ⟨P.latticeHomologyCycleMap_injective h k c hc hone,
    P.latticeHomologyCycleMap_surjective k c hc fun z hz => ⟨P.latticeAugmentation k z, ?_⟩⟩
  have hz₀ := sub_augmentation_smul_single_mem_range_of_unique P k h hx₀ hz
  have hc₀ := sub_augmentation_smul_single_mem_range_of_unique P k h hx₀ hc
  rw [hone, one_smul] at hc₀
  have hsplit : z - P.latticeAugmentation k z • c =
      (z - P.latticeAugmentation k z • Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1) -
        P.latticeAugmentation k z •
          (c - Finsupp.single (⟨x₀, ∅⟩ : PlumbingCube V) 1) := by
    rw [smul_sub]
    abel
  rw [hsplit]
  exact Submodule.sub_mem _ hz₀ (Submodule.smul_mem _ _ hc₀)

/-- The class of a specified augmentation-one cycle identifies `𝔽₂[U]` with the lattice
homology of a rank-one negative-definite plumbing. -/
noncomputable def coefficientEquivLatticeHomologyOfUnique (h : P.IsNegativeDefinite)
    (c : PlumbingChain V) (hc : P.latticeDifferential k c = 0)
    (hone : P.latticeAugmentation k c = 1) :
    PlumbingCoefficient ≃ₗ[PlumbingCoefficient] P.latticeHomology k :=
  LinearEquiv.ofBijective
    (P.latticeHomologyCycleMap k c hc)
    (latticeHomologyCycleMap_bijective_of_unique P k h c hc hone)

/-- The equivalence specified by an augmentation-one cycle sends a coefficient to the homology
class of its multiple of that cycle. -/
@[simp]
theorem coefficientEquivLatticeHomologyOfUnique_apply (h : P.IsNegativeDefinite)
    (c : PlumbingChain V) (hc : P.latticeDifferential k c = 0)
    (hone : P.latticeAugmentation k c = 1) (a : PlumbingCoefficient) :
    coefficientEquivLatticeHomologyOfUnique P k h c hc hone a =
      P.latticeHomologyCycleMap k c hc a := by
  rw [coefficientEquivLatticeHomologyOfUnique]
  rfl

end Homology

end PlumbingGraph

/-! ### The one-vertex plumbings -/

/-- The one-vertex plumbing with framing `w`: a single sphere of self-intersection `w`. For
`w < 0` its boundary three-manifold is the lens space `L(-w, 1)`. -/
def oneVertexPlumbing (w : ℤ) : PlumbingGraph (Fin 1) where
  toSimpleGraph := ⊥
  decidableAdj := inferInstance
  weight := fun _ => w

/-- Every vertex of the one-vertex plumbing has the specified framing. -/
@[simp]
theorem oneVertexPlumbing_weight (w : ℤ) (i : Fin 1) :
    (oneVertexPlumbing w).weight i = w := by
  simp [oneVertexPlumbing]

/-- The one-vertex plumbing has no graph edges. -/
@[simp]
theorem oneVertexPlumbing_toSimpleGraph (w : ℤ) :
    (oneVertexPlumbing w).toSimpleGraph = ⊥ := by
  simp [oneVertexPlumbing]

/-- The intersection matrix of a one-vertex plumbing is its framing. -/
theorem oneVertexPlumbing_intersectionMatrix (w : ℤ) :
    (oneVertexPlumbing w).intersectionMatrix = !![w] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneVertexPlumbing]

/-- A one-vertex plumbing with negative framing is negative definite. -/
theorem oneVertexPlumbing_isNegativeDefinite {w : ℤ} (hw : w < 0) :
    (oneVertexPlumbing w).IsNegativeDefinite := by
  refine PlumbingGraph.isNegativeDefinite_of_degree_lt_neg_weight _ fun i => ?_
  have hdeg : (oneVertexPlumbing w).toSimpleGraph.degree i = 0 := by
    unfold oneVertexPlumbing
    exact SimpleGraph.bot_degree i
  rw [hdeg, oneVertexPlumbing_weight]
  omega

/-- The lattice homology of the one-vertex plumbing with negative framing `w` is, in every
spin^c structure, a free `𝔽₂[U]`-module of rank one: exactly one `U`-tower, agreeing with
the lens-space computation of Ozsváth–Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265). -/
noncomputable def coefficientEquivOneVertexPlumbingLatticeHomology {w : ℤ} (hw : w < 0)
    (k : (oneVertexPlumbing w).characteristicVectors) :
    PlumbingCoefficient ≃ₗ[PlumbingCoefficient] (oneVertexPlumbing w).latticeHomology k :=
  let h := oneVertexPlumbing_isNegativeDefinite hw
  let e := (oneVertexPlumbing w).exists_cycle_latticeAugmentation_eq_one h k
  PlumbingGraph.coefficientEquivLatticeHomologyOfUnique _ k h e.choose e.choose_spec.1
    e.choose_spec.2

end TauCeti
