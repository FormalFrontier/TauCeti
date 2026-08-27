/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Lie actions on exterior powers

An endomorphism of a module acts infinitesimally on an exterior power by applying the
endomorphism to one factor at a time. This construction is linear in the endomorphism and carries
commutators to commutators, hence defines a Lie algebra representation.

## Main definitions

* `exteriorPower.lieMap`: the natural Lie action of `Module.End K V` on `⋀[K]^d V`.

## Main results

* `exteriorPower.lieMap_apply_ιMulti`: the action on a decomposable wedge is the sum of the terms
  obtained by applying the endomorphism to one factor.

## References

* [Highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 8, where the Vinberg model of `E₈` uses the `sl₉` action on `⋀³(K⁹)`.
-/

public section

open scoped BigOperators

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]

private noncomputable def actionMultilinear (d : ℕ) (f : Module.End K V) :
    MultilinearMap K (fun _ : Fin d => V) (⋀[K]^d V) :=
  ∑ i : Fin d, (ιMulti K d).toMultilinearMap.compLinearMap
    (Function.update (fun _ => LinearMap.id) i f)

private theorem actionMultilinear_apply (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionMultilinear d f v =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  simp only [actionMultilinear, sum_apply, MultilinearMap.compLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (ιMulti K d)
  funext j
  by_cases hji : j = i <;> simp [hji]

private theorem actionMultilinear_map_eq_zero_of_eq (d : ℕ) (f : Module.End K V)
    (v : Fin d → V) (i j : Fin d) (hv : v i = v j) (hij : i ≠ j) :
    actionMultilinear d f v = 0 := by
  rw [actionMultilinear_apply]
  let term : Fin d → ⋀[K]^d V := fun k => ιMulti K d (Function.update v k (f (v k)))
  have hpair : term i + term j = 0 := by
    dsimp only [term]
    have hfun : Function.update v j (f (v j)) =
        Function.update v i (f (v i)) ∘ Equiv.swap i j := by
      funext k
      by_cases hki : k = i
      · subst k
        simpa [Function.update_apply, hij, Ne.symm hij] using hv
      · by_cases hkj : k = j
        · subst k
          simpa [Function.update_apply, hij, Ne.symm hij] using congrArg f hv.symm
        · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]
    rw [hfun]
    exact (ιMulti K d).map_add_swap _ hij
  -- The swap pairs the `i` and `j` terms; every remaining term vanishes by alternation.
  apply Finset.sum_involution (s := Finset.univ) (f := term)
      (fun k _ => Equiv.swap i j k)
  · intro k _
    by_cases hki : k = i
    · subst k
      rw [Equiv.swap_apply_left]
      exact hpair
    · by_cases hkj : k = j
      · subst k
        rw [Equiv.swap_apply_right]
        rw [add_comm]
        exact hpair
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        have hzero : term k = 0 := by
          apply (ιMulti K d).map_eq_zero_of_eq _ _ hij
          simp [Function.update_of_ne (Ne.symm hki),
            Function.update_of_ne (Ne.symm hkj), hv]
        simp [hzero]
  · intro k _ hk
    exact (Equiv.swap_apply_ne_self_iff.mpr
      ⟨hij, by
        by_contra h
        have hki : k ≠ i := fun hki => h (Or.inl hki)
        have hkj : k ≠ j := fun hkj => h (Or.inr hkj)
        apply hk
        apply (ιMulti K d).map_eq_zero_of_eq _ _ hij
        simp [Function.update_of_ne (Ne.symm hki),
          Function.update_of_ne (Ne.symm hkj), hv]⟩)
  · intro k _
    exact Finset.mem_univ _
  · intro k _
    exact Equiv.swap_apply_self i j k

private noncomputable def actionAlternating (d : ℕ) (f : Module.End K V) :
    V [⋀^Fin d]→ₗ[K] (⋀[K]^d V) where
  toMultilinearMap := actionMultilinear d f
  map_eq_zero_of_eq' v i j hv hij :=
    actionMultilinear_map_eq_zero_of_eq d f v i j hv hij

@[simp]
private theorem actionAlternating_apply (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionAlternating d f v =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) :=
  by
    -- The alternating-map constructor has no application lemma for its multilinear projection.
    rw [show actionAlternating d f v = actionMultilinear d f v from rfl]
    exact actionMultilinear_apply d f v

private noncomputable def actionLinear (d : ℕ) :
    Module.End K V →ₗ[K] Module.End K (⋀[K]^d V) where
  toFun f := alternatingMapLinearEquiv (actionAlternating d f)
  map_add' f g := by
    apply linearMap_ext
    ext v
    simp [actionAlternating_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    apply linearMap_ext
    ext v
    simp [actionAlternating_apply, Finset.smul_sum]

@[simp]
private theorem actionLinear_apply_ιMulti (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    actionLinear d f (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) := by
  simp [actionLinear, actionAlternating_apply]

private def actionTerm (d : ℕ) (f g : Module.End K V) (v : Fin d → V)
    (i j : Fin d) : ⋀[K]^d V :=
  ιMulti K d (Function.update (Function.update v i (g (v i))) j
    (f (Function.update v i (g (v i)) j)))

@[simp]
private theorem actionTerm_same (d : ℕ) (f g : Module.End K V) (v : Fin d → V)
    (i : Fin d) :
    actionTerm d f g v i i = ιMulti K d (Function.update v i (f (g (v i)))) := by
  simp [actionTerm]

private theorem actionTerm_swap (d : ℕ) (f g : Module.End K V) (v : Fin d → V)
    {i j : Fin d} (hij : i ≠ j) :
    actionTerm d f g v i j = actionTerm d g f v j i := by
  apply congrArg (ιMulti K d)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem actionLinear_comp_apply_ιMulti (d : ℕ) (f g : Module.End K V)
    (v : Fin d → V) :
    actionLinear d f (actionLinear d g (ιMulti K d v)) =
      (∑ i : Fin d, actionTerm d f g v i i) +
        ∑ i : Fin d, ∑ j ∈ Finset.univ.erase i, actionTerm d f g v i j := by
  rw [actionLinear_apply_ιMulti]
  simp only [map_sum, actionLinear_apply_ιMulti]
  simp only [actionTerm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]

private theorem actionTerm_offdiag_sum_comm (d : ℕ) (f g : Module.End K V)
    (v : Fin d → V) :
    (∑ i : Fin d, ∑ j ∈ Finset.univ.erase i, actionTerm d f g v i j) =
      ∑ i : Fin d, ∑ j ∈ Finset.univ.erase i, actionTerm d g f v i j := by
  rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.univ.erase i)
    (t' := Finset.univ) (s' := fun j => Finset.univ.erase j) (by simp [ne_comm])]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  exact actionTerm_swap d f g v (Finset.ne_of_mem_erase hj)

private theorem actionLinear_map_lie (d : ℕ) (f g : Module.End K V) :
    actionLinear d ⁅f, g⁆ = ⁅actionLinear d f, actionLinear d g⁆ := by
  apply linearMap_ext
  apply AlternatingMap.ext
  intro v
  -- Extensionality leaves reducible alternating-map and endomorphism-bracket wrappers; this
  -- reshaping exposes the associative commutators used by the explicit calculation below.
  change actionLinear d (f * g - g * f) (ιMulti K d v) =
    actionLinear d f (actionLinear d g (ιMulti K d v)) -
      actionLinear d g (actionLinear d f (ιMulti K d v))
  rw [map_sub, LinearMap.sub_apply, actionLinear_apply_ιMulti,
    actionLinear_comp_apply_ιMulti, actionLinear_comp_apply_ιMulti,
    actionTerm_offdiag_sum_comm d f g v]
  rw [actionLinear_apply_ιMulti]
  simp only [Module.End.mul_apply, actionTerm_same]
  abel

/-- The infinitesimal action of endomorphisms on an exterior power. -/
noncomputable def lieMap (d : ℕ) :
    Module.End K V →ₗ⁅K⁆ Module.End K (⋀[K]^d V) :=
  { actionLinear d with map_lie' := fun {f g} => actionLinear_map_lie d f g }

/-- An endomorphism acts on a decomposable wedge by acting on one factor at a time. -/
@[simp]
theorem lieMap_apply_ιMulti (d : ℕ) (f : Module.End K V) (v : Fin d → V) :
    lieMap d f (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (f (v i))) :=
  by
    -- The Lie-hom constructor has no application lemma for its underlying linear map.
    rw [show lieMap d f = actionLinear d f from rfl]
    exact actionLinear_apply_ιMulti d f v

end exteriorPower
