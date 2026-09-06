/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Topology.Algebra.Nonarchimedean.Completion
public import TauCeti.Topology.Algebra.Nonarchimedean.FirstCountable
public import TauCeti.Topology.Algebra.OpenMapping.Complete

/-!
# An open surjection induces a surjection on completions

For nonarchimedean additive groups, a continuous **open** surjection `f : G → H` stays surjective
after separated completion. Openness is what the statement turns on: a continuous surjection alone
gives only a dense image in `Ĥ`.

The two halves are separated because they need different hypotheses. Openness alone puts a
*neighbourhood of zero* inside the range: the closures of the images of an antitone basis of open
subgroups of `G` are such a basis in `Ĝ`, their images under the induced map have closures that are
neighbourhoods of zero in `Ĥ` — this is where `f` being open is used — and
`TauCeti.mem_image_of_mem_closure_image` removes the closure, which is where completeness of `Ĝ`
and first countability of `G` are used. Surjectivity of `f` is then needed only to make the range
*dense*; a subgroup that is both dense and open is everything.

## Main results

* `UniformSpace.Completion.hasBasis_nhds_zero_closure_image`: the closures of the images of a
  neighbourhood basis of open subgroups are a neighbourhood basis of zero in the completion.
* `UniformSpace.Completion.surjective_completion`: the surjection itself.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 5.33, for the correspondence
  between the open subgroups of `A` and of `Â` that the basis result is the neighbourhood form of.
-/

public section

open Filter Topology

namespace UniformSpace.Completion

variable {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
variable {H : Type*} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]

/-- **The closures of the images of a neighbourhood basis of open subgroups are a neighbourhood
basis of zero in the completion.** -/
theorem hasBasis_nhds_zero_closure_image {ι : Sort*} {p : ι → Prop} {V : ι → OpenAddSubgroup G}
    (hV : (𝓝 (0 : G)).HasBasis p fun i ↦ (V i : Set G)) :
    (𝓝 (0 : Completion G)).HasBasis p
      fun i ↦ closure (((↑) : G → Completion G) '' (V i : Set G)) := by
  refine Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩
  · -- a closed neighbourhood inside `U` pulls back to one containing some `V i`, and taking
    -- closures of images stays inside it
    obtain ⟨C, ⟨hC, hCclosed⟩, hCU⟩ := (closed_nhds_basis (0 : Completion G)).mem_iff.mp hU
    have hpre : ((↑) : G → Completion G) ⁻¹' C ∈ 𝓝 (0 : G) :=
      (continuous_coe G).continuousAt.preimage_mem_nhds (by rwa [coe_zero])
    obtain ⟨i, hi, hn⟩ := hV.mem_iff.mp hpre
    refine ⟨i, hi, fun x hx ↦ hCU ?_⟩
    have hx' : x ∈ closure C := closure_mono (Set.image_subset_iff.mpr hn) hx
    rwa [hCclosed.closure_eq] at hx'
  · rintro ⟨i, hi, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_closure_image_coe (V i).isOpen).mem_nhds
        (subset_closure ⟨0, (V i).zero_mem, coe_zero⟩)) hn

/-- **Openness alone puts a neighbourhood of zero inside the range.** Surjectivity of `f` is not
used; it is what `surjective_completion` adds to turn this into surjectivity.

Private because it is one half of that theorem rather than a statement a consumer wants: the range
of a continuous open map being a neighbourhood of zero is only interesting as a step towards its
being everything. -/
private theorem mem_nhds_range_completion [NonarchimedeanAddGroup G]
    [(𝓝 (0 : G)).IsCountablyGenerated] [NonarchimedeanAddGroup H] {f : G →+ H}
    (hf : Continuous f) (hopen : IsOpenMap f) :
    (((f.completion hf).range : AddSubgroup (Completion H)) : Set (Completion H))
      ∈ 𝓝 (0 : Completion H) := by
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup (G := G)
  set F := f.completion hf with hF
  set W : ℕ → AddSubgroup (Completion G) := fun n ↦
    (((V n : AddSubgroup G).map (toCompl : G →+ Completion G)).topologicalClosure) with hW
  have hWcoe : ∀ n, (W n : Set (Completion G))
      = closure (((↑) : G → Completion G) '' (V n : Set G)) := fun n ↦ rfl
  have hWbasis : (𝓝 (0 : Completion G)).HasAntitoneBasis fun n ↦ (W n : Set (Completion G)) :=
    ⟨by simpa only [hWcoe] using hasBasis_nhds_zero_closure_image hV.toHasBasis,
      fun _ _ hmn ↦ by simpa only [hWcoe] using closure_mono (Set.image_mono (hV.antitone hmn))⟩
  -- `f` open makes each `f '' V n` an open subgroup of `H`, so the closure of its image is a
  -- neighbourhood of zero in `Ĥ`
  have himg : ∀ n, closure (((↑) : H → Completion H) '' ((V n : AddSubgroup G).map f : Set H))
      ∈ 𝓝 (0 : Completion H) := fun n ↦
    (isOpen_closure_image_coe
        (by simpa [AddSubgroup.coe_map] using hopen _ (V n).isOpen)).mem_nhds
      (subset_closure ⟨0, ⟨0, (V n).zero_mem, map_zero f⟩, coe_zero⟩)
  have hsub : ∀ n, ((↑) : H → Completion H) '' ((V n : AddSubgroup G).map f : Set H)
      ⊆ F '' (W n : Set (Completion G)) := by
    rintro n _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : Completion G), subset_closure ⟨x, hx, rfl⟩,
      by rw [hF, AddMonoidHom.completion_coe]⟩
  -- completeness removes the closure
  refine Filter.mem_of_superset (Filter.mem_of_superset (himg 0) fun _ hy ↦
    TauCeti.mem_image_of_mem_closure_image F
      (AddMonoidHom.continuous_completion f hf).continuousAt hWbasis
      (fun n ↦ Filter.mem_of_superset (himg (n + 1)) (closure_mono (hsub (n + 1))))
      (closure_mono (hsub 0) hy)) fun _ hx ↦ ?_
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩

/-- **A continuous open surjection of nonarchimedean groups induces a surjection on the separated
completions**, the source being first countable. -/
theorem surjective_completion [NonarchimedeanAddGroup G] [(𝓝 (0 : G)).IsCountablyGenerated]
    [NonarchimedeanAddGroup H] {f : G →+ H} (hf : Continuous f)
    (hsurj : Function.Surjective f) (hopen : IsOpenMap f) :
    Function.Surjective (f.completion hf) := by
  set F := f.completion hf with hF
  -- the range is an open subgroup, hence closed, and it is dense because `f` is onto
  have hcl : IsClosed ((F.range : AddSubgroup (Completion H)) : Set (Completion H)) :=
    AddSubgroup.isClosed_of_isOpen F.range
      (F.range.isOpen_of_mem_nhds (mem_nhds_range_completion hf hopen))
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
