/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Weight.Basic
public import TauCeti.LowDimTopology.Plumbing.Weight.Polarization

/-!
# The coordinate weight of a plumbing-lattice cube vertex

Némethi's lattice-homology cube weight `characteristicCubeWeight k x S` is the maximum of the
point weights `χ_k` over the `2 ^ |S|` vertices `cubeVertex x T`, `T ⊆ S`, of the cube with base
point `x` and directions `S` (`CubeWeight.lean`). Computing such a cube weight on a concrete
plumbing needs the value of `χ_k` at each vertex, and the cube-weight files so far record only the
inequality bounds between a vertex weight and the ambient cube weight, never a closed form for the
vertex weight itself.

This file supplies that closed form. Writing the vertex `cubeVertex x S = x + ∑ v ∈ S, E_v` as a
lattice step off the base point and feeding it through the polarization identity
`characteristicWeight_add` (`WeightPolarization.lean`) expresses the vertex weight through the base
weight, the weight of the pure sphere sum `∑ v ∈ S, E_v`, and the linear pairings of the base point
against the moving spheres:

`χ_k(cubeVertex x S) = χ_k(x) + χ_k(∑ v ∈ S, E_v) - ∑ v ∈ S, ⟨x, E_v⟩`.

At the level of the (always integer) weight numerator `⟨k, ·⟩ + · · ·` there is no division to
discharge, so the numerator admits a fully explicit coordinate formula in the intersection-matrix
entries,

`num_k(cubeVertex x S) = num_k(x) + ∑ v ∈ S, k v + ∑ v ∈ S, ∑ w ∈ S, A v w
    + 2 ∑ v ∈ S, ∑ i, x i * A i v`,

which is exactly what a `decide`/`norm_num` computation of a concrete cube weight evaluates. The
`A₂` plumbing top vertex `E₀ + E₁` of the origin `2`-cube is checked against it.

## Main results

* `TauCeti.PlumbingGraph.characteristicWeight_cubeVertex`: the cube-vertex weight through the base
  weight, the sphere-sum weight, and the base pairings.
* `TauCeti.PlumbingGraph.characteristicWeightNumerator_cubeVertex`: the fully explicit coordinate
  formula for the cube-vertex weight numerator.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose cube weights are the maxima of the point weights `χ_k` over the cube
vertices and whose acceptance criterion asks for `ℍ` of concrete negative-definite plumbings. The
coordinate weight formula is the standard evaluation of Némethi's weight function; see Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- The characteristic covector paired against a finite sum of basis spheres selects the covector
coordinates in the chosen directions. -/
private theorem sum_mul_sum_single (k : V → ℤ) (S : Finset V) :
    (∑ w, k w * (∑ v ∈ S, Pi.single v (1 : ℤ)) w) = ∑ w ∈ S, k w := by
  have h : ∀ w, (∑ v ∈ S, Pi.single v (1 : ℤ)) w = if w ∈ S then 1 else 0 := fun w => by
    rw [Finset.sum_apply]; exact Finset.sum_pi_single w (fun _ => 1) S
  simp_rw [h, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The cube-vertex weight numerator in coordinates.** The weight numerator at the vertex
`cubeVertex x S = x + ∑ v ∈ S, E_v` of a plumbing cube is the base numerator, plus the covector
coordinates in the chosen directions, plus the intersection double sum of those directions, plus
twice the pairings of the base point against them. As the numerator carries no division, this is
the formula a concrete cube-weight computation evaluates. -/
theorem characteristicWeightNumerator_cubeVertex (k x : V → ℤ) (S : Finset V) :
    P.characteristicWeightNumerator k (cubeVertex x S) =
      P.characteristicWeightNumerator k x + (∑ v ∈ S, k v) +
        (∑ v ∈ S, ∑ w ∈ S, P.intersectionMatrix v w) +
        2 * ∑ v ∈ S, ∑ i, x i * P.intersectionMatrix i v := by
  have hnum : P.characteristicWeightNumerator k (∑ v ∈ S, Pi.single v 1) =
      (∑ v ∈ S, k v) + ∑ v ∈ S, ∑ w ∈ S, P.intersectionMatrix v w := by
    rw [characteristicWeightNumerator_def, sum_mul_sum_single k S,
      P.intersectionForm_sum_single_self S]
  rw [cubeVertex_def, characteristicWeightNumerator_add_right, hnum,
    P.intersectionForm_sum_single_right x S]
  ring

/-- **The cube-vertex weight through the base point.** The weight at the vertex
`cubeVertex x S = x + ∑ v ∈ S, E_v` splits, by the polarization identity, into the base weight, the
weight of the pure sphere sum `∑ v ∈ S, E_v`, and the linear pairings of the base point against the
moving spheres. -/
theorem characteristicWeight_cubeVertex (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    P.characteristicWeight k (cubeVertex x S) =
      P.characteristicWeight k x + P.characteristicWeight k (∑ v ∈ S, Pi.single v 1) -
        ∑ v ∈ S, ∑ i, x i * P.intersectionMatrix i v := by
  rw [cubeVertex_def, characteristicWeight_add, P.intersectionForm_sum_single_right x S]

end PlumbingGraph

/-- A self-validating check on the `A₂` plumbing through the explicit coordinate formula: the
weight numerator of the top vertex `E₀ + E₁` of the `2`-cube based at the origin, taken with the
zero covector, is the intersection double sum `A₀₀ + A₀₁ + A₁₀ + A₁₁ = -2 + 1 + 1 - 2 = -2`. -/
example : a2Plumbing.characteristicWeightNumerator (fun _ => 0)
    (PlumbingGraph.cubeVertex (0 : Fin 2 → ℤ) Finset.univ) = -2 := by
  rw [PlumbingGraph.characteristicWeightNumerator_cubeVertex]
  simp only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
    PlumbingGraph.characteristicWeightNumerator_def, PlumbingGraph.intersectionForm_apply]
  rw [a2Plumbing_intersectionMatrix]
  norm_num [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- A self-validating check on the `A₂` plumbing through the base-point reduction: the top vertex
`E₀ + E₁` of the origin `2`-cube has characteristic weight `1` for the canonical covector, since
`χ(E₀) = χ(E₁) = 1` and the single adjacency contributes `A₀₁ = 1`. -/
example : a2Plumbing.characteristicWeight
    ⟨a2Plumbing.canonicalCharacteristic, a2Plumbing.isCharacteristicVector_canonicalCharacteristic⟩
    (PlumbingGraph.cubeVertex (0 : Fin 2 → ℤ) Finset.univ) = 1 := by
  rw [PlumbingGraph.characteristicWeight_cubeVertex, PlumbingGraph.characteristicWeight_zero]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, zero_add]
  rw [show (∑ v : Fin 2, Pi.single v (1 : ℤ)) = Pi.single 0 1 + Pi.single 1 1 from by
    rw [Fin.sum_univ_two], PlumbingGraph.characteristicWeight_single_add_single,
    PlumbingGraph.characteristicWeight_canonical_single,
    PlumbingGraph.characteristicWeight_canonical_single, a2Plumbing_intersectionMatrix]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end TauCeti
