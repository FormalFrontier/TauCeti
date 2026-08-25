/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Matrix
public import TauCeti.RingTheory.Huber.OpenMapping
public import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# Dense submodules of a module-finite complete Tate-module

A dense submodule of a module-finite, complete, metrisable module over a complete Tate ring is
the whole module. This is Bosch–Güntzer–Remmert §3.7.2/1 in its intrinsic form, and it is the
step that makes finitely generated submodules closed on the route to Wedhorn 6.17/6.18.

The argument is the open mapping theorem followed by Nakayama. A finite spanning family presents
`V` as an *open* quotient of `Aⁿ`
(`TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`), so the image of a neighbourhood of zero
consisting of topologically nilpotent scalars is a neighbourhood of zero in `V`. Density writes
each generator as `gᵥ = mᵥ + ∑ⱼ aᵥⱼ • gⱼ` with `mᵥ` in the submodule and every `aᵥⱼ` topologically
nilpotent, and matrix Nakayama in the quotient
(`TauCeti.Huber.eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul`) forces every
generator into the submodule.

The neighbourhood of topologically nilpotent scalars is `A°°` itself, which is open
(`TauCeti.Huber.isOpen_setOf_isTopologicallyNilpotent`) and contains zero, so neither an ideal of
definition nor a pseudouniformiser has to be chosen.

## Main results

* `TauCeti.Huber.eq_top_of_dense_of_module_finite`: a dense submodule of a module-finite complete
  Tate-module is everything.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert], §3.7.2/1.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Propositions 6.17–6.18.

Adapted from the AINTLIB development (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/adic-spaces` at commit `37bbdaeb9ad9`, file
`projects/AdicSpaces/Adic spaces/WedhornBanachTheorem.lean`, where the same statement is
`eq_top_of_dense_of_finite`. The argument is AINTLIB's; three things differ. The target is
separated by `T0Space` rather than `T2Space`. The neighbourhood of topologically nilpotent
scalars is `A°°` itself rather than `ϖ • A⁰` for a chosen pseudouniformiser, so no unit has to
be produced. And the open presentation is the named
`TauCeti.Huber.IsTateRing.isOpenMap_linearCombination` rather than a locally built linear map.
-/

open Filter Topology
open scoped Uniformity

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T2Space A] [IsTopologicalRing A] [IsTateRing A]
  {V : Type*} [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] [CompleteSpace V]
  [(𝓤 V).IsCountablyGenerated] [T0Space V] [Module A V] [ContinuousSMul A V]

/-- **A dense submodule of a module-finite complete Tate-module is everything**
(Bosch–Güntzer–Remmert §3.7.2/1).

`N` is a submodule of `V` whose closure is all of `V`; the conclusion is that `N` was already all
of `V`. The hypotheses are carried by the ambient instances: `A` is a complete Hausdorff Tate
ring, `V` is a complete `T0` topological `A`-module with countably generated uniformity and
continuous scalar action, and `V` is *module-finite* over `A`. Module-finiteness is what makes
the statement true — a dense submodule of an infinite-dimensional complete module need not be
everything.

The proof is the open mapping theorem followed by matrix Nakayama; see the module docstring. -/
theorem eq_top_of_dense_of_module_finite [Module.Finite A V] (N : Submodule A V)
    (hN : Dense (N : Set V)) : N = ⊤ := by
  classical
  -- Derivable, so it is not asked of the caller (it is not found by instance search).
  let _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := V)
  set W : Set A := {a : A | IsTopologicallyNilpotent a}
  have hW_nhds : W ∈ nhds (0 : A) :=
    isOpen_setOf_isTopologicallyNilpotent.mem_nhds IsTopologicallyNilpotent.zero
  have hW_tn : ∀ a ∈ W, IsTopologicallyNilpotent a := fun _ ha ↦ ha
  have hopen : IsOpenMap (Fintype.linearCombination A g : (Fin n → A) → V) :=
    IsTateRing.isOpenMap_linearCombination g hspan
  have hWpi_nhds : Set.univ.pi (fun _ : Fin n ↦ W) ∈ nhds (0 : Fin n → A) :=
    set_pi_mem_nhds Set.finite_univ fun i _ ↦ by simpa using hW_nhds
  have hΩ_nhds :
      (Fintype.linearCombination A g) '' Set.univ.pi (fun _ : Fin n ↦ W) ∈ nhds (0 : V) := by
    have := hopen.image_mem_nhds (x := (0 : Fin n → A)) hWpi_nhds
    rwa [map_zero] at this
  -- Density writes each generator as an `N`-element plus a topologically nilpotent combination.
  have hextract : ∀ v : Fin n, ∃ a : Fin n → A, (∀ j, a j ∈ W) ∧
      ∃ m ∈ N, g v = m + ∑ j, a j • g j := by
    intro v
    have hnb : (fun z : V ↦ g v - z) ⁻¹'
        ((Fintype.linearCombination A g) '' Set.univ.pi (fun _ : Fin n ↦ W)) ∈ nhds (g v) := by
      refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hΩ_nhds
    obtain ⟨w, hwU, hwN⟩ := mem_closure_iff_nhds.mp (hN (g v)) _ hnb
    obtain ⟨a, haW, ha_eq⟩ := hwU
    refine ⟨a, fun j ↦ Set.mem_univ_pi.mp haW j, w, hwN, ?_⟩
    have hpa : (∑ j, a j • g j) = g v - w := by
      rw [← Fintype.linearCombination_apply]; exact ha_eq
    rw [hpa]; abel
  choose a haW m hmN hrel using hextract
  -- Matrix Nakayama in `V ⧸ N`.
  have hy : ∀ v, N.mkQ (g v) = ∑ j, Matrix.of a v j • N.mkQ (g j) := by
    intro v
    have hq0 : N.mkQ (m v) = 0 := (Submodule.Quotient.mk_eq_zero N).2 (hmN v)
    simp only [Matrix.of_apply]
    rw [hrel v, map_add, hq0, map_sum, zero_add]
    simp only [map_smul]
  have hzero := eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul
    (B := Matrix.of a)
    (fun i j ↦ hW_tn _ (haW i j)) hy
  refine eq_top_iff.2 ?_
  rw [← hspan]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun v ↦
    (Submodule.Quotient.mk_eq_zero N).1 (by simpa using congrFun hzero v))

end TauCeti.Huber
