/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.FirstCountable
public import TauCeti.Topology.Algebra.OpenMapping.Complete

/-!
# An open map of nonarchimedean groups stays open, and an open surjection stays surjective

For a continuous **open** homomorphism `f : G → H` of nonarchimedean additive groups with `G`
first countable, the induced map on separated completions is again open; if `f` is moreover
surjective then so is that map. Openness is what the statements turn on: a continuous surjection
alone gives only a dense image in the completion of `H`.

## Main results

* `UniformSpace.Completion.isOpenMap_completion`: the induced map on completions is open.
* `UniformSpace.Completion.surjective_completion`: it is surjective when `f` is.
-/

public section

open Filter Topology

namespace UniformSpace.Completion

variable {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
variable {H : Type*} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]

/-- The image under the induced map of the first term of a basis of closures is a neighbourhood
of zero in the completion of `H`. -/
private theorem image_closure_image_coe_mem_nhds {f : G →+ H} (hf : Continuous f)
    (hopen : IsOpenMap f) {V : ℕ → OpenAddSubgroup G}
    (hV : (𝓝 (0 : G)).HasAntitoneBasis fun n ↦ (V n : Set G)) :
    f.completion hf '' closure (((↑) : G → Completion G) '' (V 0 : Set G))
      ∈ 𝓝 (0 : Completion H) := by
  set F := f.completion hf with hF
  set W : ℕ → AddSubgroup (Completion G) := fun n ↦
    (((V n : AddSubgroup G).map (toCompl : G →+ Completion G)).topologicalClosure) with hW
  have hWcoe : ∀ n, (W n : Set (Completion G))
      = closure (((↑) : G → Completion G) '' (V n : Set G)) := fun n ↦ by
    rw [hW, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map,
      Set.image_congr' toCompl_apply, OpenAddSubgroup.coe_toAddSubgroup]
  have hWbasis : (𝓝 (0 : Completion G)).HasAntitoneBasis fun n ↦ (W n : Set (Completion G)) :=
    ⟨by simpa only [hWcoe] using hasBasis_nhds_zero_closure_image hV.toHasBasis,
      fun _ _ hmn ↦ by simpa only [hWcoe] using closure_mono (Set.image_mono (hV.antitone hmn))⟩
  -- `f` open makes each `f '' V n` an open subgroup of `H`, so the closure of its image is a
  -- neighbourhood of zero in the completion of `H`
  have himg : ∀ n, closure (((↑) : H → Completion H) '' ((V n : AddSubgroup G).map f : Set H))
      ∈ 𝓝 (0 : Completion H) := fun n ↦
    (isOpen_closure_image_coe
        (by simpa [AddSubgroup.coe_map] using hopen _ (V n).isOpen)).mem_nhds
      (subset_closure ⟨0, ⟨0, (V n).zero_mem, map_zero f⟩, coe_zero⟩)
  have hsub : ∀ n, ((↑) : H → Completion H) '' ((V n : AddSubgroup G).map f : Set H)
      ⊆ F '' (W n : Set (Completion G)) := by
    rintro n _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : Completion G), by rw [hWcoe]; exact subset_closure ⟨x, hx, rfl⟩,
      by rw [hF, AddMonoidHom.completion_coe]⟩
  rw [← hWcoe 0]
  exact Filter.mem_of_superset (himg 0) fun _ hy ↦
    TauCeti.mem_image_of_mem_closure_image F
      (AddMonoidHom.continuous_completion f hf).continuousAt hWbasis
      (fun n ↦ Filter.mem_of_superset (himg (n + 1)) (closure_mono (hsub (n + 1))))
      (closure_mono (hsub 0) hy)

/-- **A continuous open homomorphism of nonarchimedean groups induces an open map on the separated
completions**, the source being first countable. -/
theorem isOpenMap_completion [NonarchimedeanAddGroup G] [(𝓝 (0 : G)).IsCountablyGenerated]
    {f : G →+ H} (hf : Continuous f) (hopen : IsOpenMap f) :
    IsOpenMap (f.completion hf) := by
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup (G := G)
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro S hS
  obtain ⟨n, -, hn⟩ := (hasBasis_nhds_zero_closure_image hV.toHasBasis).mem_iff.mp hS
  exact Filter.mem_of_superset
    (image_closure_image_coe_mem_nhds hf hopen
      (hV.comp_strictMono fun a b hab ↦ Nat.add_lt_add_left hab n))
    ((Set.image_mono hn).trans (Set.image_preimage_subset _ _))

/-- **A continuous open surjection of nonarchimedean groups induces a surjection on the separated
completions**, the source being first countable. -/
theorem surjective_completion [NonarchimedeanAddGroup G] [(𝓝 (0 : G)).IsCountablyGenerated]
    {f : G →+ H} (hf : Continuous f) (hsurj : Function.Surjective f) (hopen : IsOpenMap f) :
    Function.Surjective (f.completion hf) := by
  set F := f.completion hf with hF
  -- the range is an open subgroup, hence closed, and it is dense because `f` is onto
  have hcl : IsClosed ((F.range : AddSubgroup (Completion H)) : Set (Completion H)) :=
    AddSubgroup.isClosed_of_isOpen F.range (isOpenMap_completion hf hopen).isOpen_range
  have hdense : Dense ((F.range : AddSubgroup (Completion H)) : Set (Completion H)) := by
    refine Dense.mono (fun y hy ↦ ?_) (denseRange_coe (α := H))
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := hsurj x
    exact ⟨(g : Completion G), by rw [hF, AddMonoidHom.completion_coe]⟩
  intro y
  have huniv : ((F.range : AddSubgroup (Completion H)) : Set (Completion H)) = Set.univ :=
    hcl.closure_eq.symm.trans hdense.closure_eq
  have hy : y ∈ ((F.range : AddSubgroup (Completion H)) : Set (Completion H)) := by
    rw [huniv]; exact Set.mem_univ y
  exact AddMonoidHom.mem_range.mp hy

end UniformSpace.Completion

end
