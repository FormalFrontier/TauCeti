/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Link

/-!
# Stellar subdivision at a face

*Starring* a complex `K` at one of its faces `σ`, with a fresh vertex `v`, replaces the closed
star of `σ` by the cone with apex `v` on the boundary of that closed star. It is the combinatorial
model of the geometric move in which a new vertex placed in the interior of `σ` cones off the
boundary of the closed star; suitably realized, the source and the target of that move are
PL-homeomorphic, but nothing of the kind is asserted here, since the construction below supplies
no placement of `v` (see the paragraph on realizations).

This file builds that move for `PreAbstractSimplicialComplex`, Mathlib's downward-closed
collections of nonempty finite faces. The precomplex type is the right home: a starring changes
which vertices are used, since `σ` itself stops being a face while `v` becomes one.

The definition is the usual explicit description of the faces, split by whether the new vertex
occurs. A face is either

* a face of `K` that does *not* contain `σ` — that is, a face of the deletion `deletion K σ`; or
* `insert v ρ`, where `ρ` does not contain `σ` and `ρ ∪ σ` is a face of `K` — that is, `v` joined
  with a face of the boundary `∂σ ∗ link K σ` of the closed star.

Phrasing the second clause through `ρ ∪ σ ∈ K` rather than through an explicit join keeps the
whole construction on the original vertex type, so starrings can be iterated. The face collection
is downward closed with no hypothesis at all on `σ` or `v`; the hypotheses appear only in the
theorems, and they are always the same two: `σ` is a face, and `v` is *fresh*, meaning `{v}` is
not a face of `K` (equivalently, by `notMem_of_singleton_notMem`, that `v` occurs in no face).

Stellar subdivision is the combinatorial substitute for a general subdivision that layer 11 of the
geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`) needs before
combinatorial spheres and balls can be defined: those are complexes that are PL-homeomorphic,
*after subdivision*, to the boundary of the standard simplex, respectively to the standard
simplex, and the barycentric subdivision alone (`Subdivision.Basic`) is too rigid to serve, since
it cannot be applied at a single face. The definition and the standard-model computations follow
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2 (starring and stellar
moves).

No claim is made here that a starring preserves the geometric realization; that identification is
realization work, parallel to the corresponding open question for `Subdivision.Basic`. What *is*
proved is the combinatorial shadow of it: the dimension is unchanged, the part of the subdivision
away from the new vertex is exactly `deletion K σ`, and the link of the new vertex is exactly the
boundary `closedStar K σ ⊓ deletion K σ` of the closed star, so the subdivision is glued from the
same two pieces the geometric picture uses.

## Main definitions

* `PreAbstractSimplicialComplex.stellarSubdivision K σ v`: the complex obtained from `K` by
  starring the face `σ` at the fresh vertex `v`.

## Main results

* `PreAbstractSimplicialComplex.mem_stellarSubdivision_iff_of_notMem` and
  `insert_mem_stellarSubdivision_iff`: the two halves of the face description, one for faces
  missing the new vertex and one for faces containing it.
* `PreAbstractSimplicialComplex.singleton_mem_stellarSubdivision_iff`: the new vertex is a vertex
  of the subdivision exactly when `σ` was a face, and
  `PreAbstractSimplicialComplex.self_notMem_stellarSubdivision`: the starred face is destroyed,
  as long as the new vertex does not already lie in it.
* `PreAbstractSimplicialComplex.deletion_stellarSubdivision_singleton` and
  `link_stellarSubdivision_singleton`: away from the new vertex the subdivision is `deletion K σ`,
  and the link of the new vertex is the boundary `closedStar K σ ⊓ deletion K σ` of the closed
  star.
* `PreAbstractSimplicialComplex.dimension_stellarSubdivision`: starring preserves the dimension.
* `PreAbstractSimplicialComplex.finite_faces_stellarSubdivision`: starring preserves finiteness.
* `PreAbstractSimplicialComplex.isCone_stellarSubdivision`: starring a complex that is its own
  closed star at `σ` produces a cone with apex the new vertex; for a simplex this gives
  `PreAbstractSimplicialComplex.link_stellarSubdivision_simplex`, that the starred simplex is the
  cone on the simplex boundary, and hence
  `PreAbstractSimplicialComplex.collapsible_stellarSubdivision_simplex`.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {V σ τ ρ : Finset ι}
  {v : ι}

/-- The **stellar subdivision** (or *starring*) of `K` at the face `σ`, using the new vertex `v`.

Its faces are the faces of `K` not containing `σ`, together with the sets `insert v ρ` for which
`ρ` does not contain `σ` and `ρ ∪ σ` is a face of `K`. Equivalently, the closed star of `σ` is
removed and replaced by the cone with apex `v` on the boundary of that closed star.

The intended hypotheses are that `σ` is a face of `K` and that `v` is fresh, i.e. `{v} ∉ K`; they
are not part of the definition, and the degenerate values are pinned by
`stellarSubdivision_empty` and `stellarSubdivision_eq_self_of_notMem`. -/
def stellarSubdivision (K : PreAbstractSimplicialComplex ι) (σ : Finset ι) (v : ι) :
    PreAbstractSimplicialComplex ι where
  faces := {τ | (v ∉ τ ∧ τ ∈ K ∧ ¬ σ ⊆ τ) ∨ (v ∈ τ ∧ ¬ σ ⊆ τ.erase v ∧ τ.erase v ∪ σ ∈ K)}
  isRelLowerSet_faces := by
    rintro a (⟨hva, haK, haσ⟩ | ⟨hva, haσ, haK⟩)
    · refine ⟨(K.isRelLowerSet_faces haK).1, fun {b} hba hbne => Or.inl ⟨fun h => hva (hba h),
        (K.isRelLowerSet_faces haK).2 hba hbne, fun h => haσ (h.trans hba)⟩⟩
    · have hσne : σ.Nonempty :=
        Finset.nonempty_of_ne_empty fun h => haσ (h ▸ Finset.empty_subset _)
      refine ⟨⟨v, hva⟩, fun {b} hba hbne => ?_⟩
      by_cases hvb : v ∈ b
      · refine Or.inr ⟨hvb, fun h => haσ (h.trans (Finset.erase_subset_erase v hba)), ?_⟩
        exact (K.isRelLowerSet_faces haK).2
          (Finset.union_subset_union (Finset.erase_subset_erase v hba) Finset.Subset.rfl)
          (hσne.mono Finset.subset_union_right)
      · have hbsub : b ⊆ a.erase v := Finset.subset_erase.mpr ⟨hba, hvb⟩
        exact Or.inl ⟨hvb, (K.isRelLowerSet_faces haK).2
          (hbsub.trans Finset.subset_union_left) hbne, fun h => haσ (h.trans hbsub)⟩

/-- The defining description of the faces of a stellar subdivision, split by whether the new
vertex occurs. -/
theorem mem_stellarSubdivision_iff :
    τ ∈ stellarSubdivision K σ v ↔
      (v ∉ τ ∧ τ ∈ K ∧ ¬ σ ⊆ τ) ∨ (v ∈ τ ∧ ¬ σ ⊆ τ.erase v ∧ τ.erase v ∪ σ ∈ K) :=
  Iff.rfl

/-- A set missing the new vertex is a face of the stellar subdivision exactly when it is a face of
`K` not containing the starred face: these are precisely the faces of `deletion K σ`. -/
@[simp]
theorem mem_stellarSubdivision_iff_of_notMem (hvτ : v ∉ τ) :
    τ ∈ stellarSubdivision K σ v ↔ τ ∈ K ∧ ¬ σ ⊆ τ := by
  constructor
  · rintro (⟨-, hτK, hτσ⟩ | ⟨hvτ', -, -⟩)
    · exact ⟨hτK, hτσ⟩
    · exact absurd hvτ' hvτ
  · exact fun h => Or.inl ⟨hvτ, h.1, h.2⟩

/-- A set containing the new vertex is a face of the stellar subdivision exactly when the rest of
it is a face of the boundary of the closed star of `σ`: it must not contain `σ`, while its union
with `σ` must remain a face. -/
@[simp]
theorem insert_mem_stellarSubdivision_iff (hvρ : v ∉ ρ) :
    insert v ρ ∈ stellarSubdivision K σ v ↔ ¬ σ ⊆ ρ ∧ ρ ∪ σ ∈ K := by
  have herase : (insert v ρ).erase v = ρ := Finset.erase_insert hvρ
  constructor
  · rintro (⟨hv', -, -⟩ | ⟨-, h₁, h₂⟩)
    · exact absurd (Finset.mem_insert_self v ρ) hv'
    · rw [herase] at h₁ h₂
      exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact Or.inr ⟨Finset.mem_insert_self v ρ, by rwa [herase], by rwa [herase]⟩

/-- The new vertex becomes a vertex of the stellar subdivision exactly when the starred set was a
face to begin with. -/
@[simp]
theorem singleton_mem_stellarSubdivision_iff :
    ({v} : Finset ι) ∈ stellarSubdivision K σ v ↔ σ ∈ K := by
  have herase : ({v} : Finset ι).erase v = ∅ := Finset.erase_singleton v
  constructor
  · rintro (⟨hv', -, -⟩ | ⟨-, -, h₂⟩)
    · exact absurd (Finset.mem_singleton_self v) hv'
    · rwa [herase, Finset.empty_union] at h₂
  · intro h
    refine Or.inr ⟨Finset.mem_singleton_self v, ?_, by rwa [herase, Finset.empty_union]⟩
    rw [herase]
    exact fun hsub => ((K.isRelLowerSet_faces h).1).ne_empty (Finset.subset_empty.mp hsub)

/-- Starring destroys the starred face, as long as the new vertex does not already lie in `σ`:
every face of the subdivision either avoids `σ` or contains the new vertex, and in the latter case
avoids `σ` after erasing it. The hypothesis `v ∉ σ` is needed, since for `v ∈ σ` one has
`σ.erase v ∪ σ = σ`, so `σ` survives the starring whenever it was a face. -/
theorem self_notMem_stellarSubdivision (hvσ : v ∉ σ) : σ ∉ stellarSubdivision K σ v := by
  rw [mem_stellarSubdivision_iff_of_notMem hvσ]
  exact fun h => h.2 Finset.Subset.rfl

/-- Starring a genuine face at a fresh vertex genuinely changes the complex. -/
theorem stellarSubdivision_ne_self (hv : ({v} : Finset ι) ∉ K) (hσ : σ ∈ K) :
    stellarSubdivision K σ v ≠ K := by
  intro h
  exact self_notMem_stellarSubdivision (notMem_of_singleton_notMem hv hσ) (by rw [h]; exact hσ)

/-- Starring at the empty set leaves nothing: every set contains `∅`, so no face survives. -/
@[simp]
theorem stellarSubdivision_empty (K : PreAbstractSimplicialComplex ι) (v : ι) :
    stellarSubdivision K (∅ : Finset ι) v = ⊥ := by
  refine eq_bot_iff.mpr fun τ hτ => ?_
  rcases hτ with ⟨-, -, h⟩ | ⟨-, h, -⟩
  · exact absurd (Finset.empty_subset τ) h
  · exact absurd (Finset.empty_subset _) h

/-- Starring at a nonempty set that is *not* a face changes nothing, provided the new vertex is
fresh: no face of `K` can contain the starred set, and freshness makes the new vertex occur in no
face of `K` and in no face of the subdivision. Freshness is needed: without it, starring can
destroy the faces of `K` that contain `v`. -/
theorem stellarSubdivision_eq_self_of_notMem (hv : ({v} : Finset ι) ∉ K) (hσne : σ.Nonempty)
    (hσ : σ ∉ K) : stellarSubdivision K σ v = K := by
  refine SetLike.ext fun τ => ?_
  constructor
  · rintro (⟨-, hτK, -⟩ | ⟨-, -, h₂⟩)
    · exact hτK
    · exact absurd ((K.isRelLowerSet_faces h₂).2 Finset.subset_union_right hσne) hσ
  · intro hτK
    exact Or.inl ⟨notMem_of_singleton_notMem hv hτK, hτK,
      fun hsub => hσ ((K.isRelLowerSet_faces hτK).2 hsub hσne)⟩

/-! ### The two pieces glued by a starring

Away from the new vertex a stellar subdivision is the deletion `deletion K σ`, and the link of
the new vertex is the boundary `closedStar K σ ⊓ deletion K σ` of the closed star of `σ`. Together
with `closedStar_sup_deletion` these say that the subdivision is the union of `deletion K σ` and
the cone with apex `v` on that boundary, which is the geometric description of the move. -/

/-- The faces of a stellar subdivision missing the new vertex form exactly the deletion of the
starred face. -/
@[simp]
theorem deletion_stellarSubdivision_singleton (hv : ({v} : Finset ι) ∉ K) :
    deletion (stellarSubdivision K σ v) {v} = deletion K σ := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_deletion, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hτ, hvτ⟩
    exact (mem_stellarSubdivision_iff_of_notMem hvτ).mp hτ
  · rintro ⟨hτK, hτσ⟩
    have hvτ : v ∉ τ := notMem_of_singleton_notMem hv hτK
    exact ⟨(mem_stellarSubdivision_iff_of_notMem hvτ).mpr ⟨hτK, hτσ⟩, hvτ⟩

/-- The deletion of the starred face survives untouched inside the stellar subdivision. -/
theorem deletion_le_stellarSubdivision (hv : ({v} : Finset ι) ∉ K) :
    deletion K σ ≤ stellarSubdivision K σ v := by
  rw [← deletion_stellarSubdivision_singleton (σ := σ) hv]
  exact deletion_le

/-- **The link of the new vertex** in a stellar subdivision is the boundary of the closed star of
the starred face, namely `closedStar K σ ⊓ deletion K σ`: the faces `ρ` with `ρ ∪ σ` a face of `K`
that do not themselves contain `σ`. This is the combinatorial form of "`v` is coned off over
`∂σ ∗ link K σ`". -/
@[simp]
theorem link_stellarSubdivision_singleton (hv : ({v} : Finset ι) ∉ K) :
    link (stellarSubdivision K σ v) {v} = closedStar K σ ⊓ deletion K σ := by
  have hunion : ∀ ω : Finset ι, ω ∪ {v} = insert v ω := fun ω => by
    rw [Finset.union_comm, Finset.insert_eq]
  refine SetLike.ext fun ρ => ?_
  rw [mem_link_nonempty, mem_inf, mem_closedStar_nonempty, mem_deletion, hunion ρ]
  constructor
  · rintro ⟨hne, hdis, hmem⟩
    have hvρ : v ∉ ρ := Finset.disjoint_singleton_right.mp hdis
    obtain ⟨h₁, h₂⟩ := (insert_mem_stellarSubdivision_iff hvρ).mp hmem
    exact ⟨⟨hne, h₂⟩, (K.isRelLowerSet_faces h₂).2 Finset.subset_union_left hne, h₁⟩
  · rintro ⟨⟨hne, hstar⟩, hρK, hρσ⟩
    have hvρ : v ∉ ρ := notMem_of_singleton_notMem hv hρK
    exact ⟨hne, Finset.disjoint_singleton_right.mpr hvρ,
      (insert_mem_stellarSubdivision_iff hvρ).mpr ⟨hρσ, hstar⟩⟩

/-! ### Dimension and finiteness -/

/-- **Starring preserves the dimension.** A face containing the new vertex has at most as many
vertices as the face `τ.erase v ∪ σ` of `K` it comes from, because `σ` contributes a vertex
outside `τ.erase v`; conversely a face of `K` containing `σ` is matched by exchanging one vertex
of `σ` for the new vertex. -/
@[simp]
theorem dimension_stellarSubdivision (hv : ({v} : Finset ι) ∉ K) (hσ : σ ∈ K) :
    dimension (stellarSubdivision K σ v) = dimension K := by
  have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
  refine le_antisymm (dimension_le_iff.mpr ?_) (dimension_le_iff.mpr ?_)
  · rintro τ (⟨-, hτK, -⟩ | ⟨hvτ, hτσ, hτK⟩)
    · exact le_dimension hτK
    · obtain ⟨x, hxσ, hxτ⟩ := Finset.not_subset.mp hτσ
      have hpos : 1 ≤ τ.card := Finset.card_pos.mpr ⟨v, hvτ⟩
      have hcard : τ.card ≤ (τ.erase v ∪ σ).card := by
        refine le_trans (le_of_eq ?_)
          (Finset.card_le_card (Finset.insert_subset (Finset.mem_union_right _ hxσ)
            Finset.subset_union_left))
        rw [Finset.card_insert_of_notMem hxτ, Finset.card_erase_of_mem hvτ]
        omega
      refine le_trans ?_ (le_dimension hτK)
      exact_mod_cast Nat.sub_le_sub_right hcard 1
  · intro τ hτK
    have hvτ : v ∉ τ := notMem_of_singleton_notMem hv hτK
    by_cases hsub : σ ⊆ τ
    · obtain ⟨x, hxσ⟩ := hσne
      have hxτ : x ∈ τ := hsub hxσ
      have hvρ : v ∉ τ.erase x := fun h => hvτ (Finset.mem_of_mem_erase h)
      have hnotsub : ¬ σ ⊆ τ.erase x := fun h => Finset.notMem_erase x τ (h hxσ)
      have hunion : τ.erase x ∪ σ = τ := by
        refine Finset.Subset.antisymm (Finset.union_subset (Finset.erase_subset _ _) hsub)
          fun y hy => ?_
        by_cases hyx : y = x
        · exact Finset.mem_union_right _ (hyx ▸ hxσ)
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      have hmem : insert v (τ.erase x) ∈ stellarSubdivision K σ v :=
        (insert_mem_stellarSubdivision_iff hvρ).mpr ⟨hnotsub, by rw [hunion]; exact hτK⟩
      have hcard : (insert v (τ.erase x)).card = τ.card := by
        rw [Finset.card_insert_of_notMem hvρ, Finset.card_erase_of_mem hxτ]
        have hpos : 1 ≤ τ.card := Finset.card_pos.mpr ⟨x, hxτ⟩
        omega
      rw [← hcard]
      exact le_dimension hmem
    · exact le_dimension ((mem_stellarSubdivision_iff_of_notMem hvτ).mpr ⟨hτK, hsub⟩)

/-- Starring a complex with finitely many faces again gives finitely many faces: a face either is
a face of `K`, or is the new vertex adjoined to a subset of a face of `K`. -/
theorem finite_faces_stellarSubdivision (hfin : K.faces.Finite) :
    (stellarSubdivision K σ v).faces.Finite := by
  have hsub : (stellarSubdivision K σ v).faces ⊆
      K.faces ∪ ⋃ ω ∈ K.faces, (insert v '' (ω.powerset : Set (Finset ι))) := by
    rintro τ (⟨-, hτK, -⟩ | ⟨hvτ, -, hτK⟩)
    · exact Or.inl hτK
    · exact Or.inr (Set.mem_biUnion hτK ⟨τ.erase v,
        Finset.mem_coe.mpr (Finset.mem_powerset.mpr Finset.subset_union_left),
        Finset.insert_erase hvτ⟩)
  exact Set.Finite.subset (hfin.union (Set.Finite.biUnion hfin fun ω _ =>
    Set.Finite.image _ ω.powerset.finite_toSet)) hsub

/-! ### Starring a closed star, and the standard model

When `K` is its own closed star at `σ` — the case of a simplex starred at its top face — every
face can absorb the new vertex, so the subdivision is a cone with apex `v`. Since a finite cone
collapses to its apex, this exhibits the starred simplex as a collapsible complex, matching the
geometric fact that a subdivided ball is collapsible. -/

/-- Starring a complex that is its own closed star at `σ` produces a cone with apex the new
vertex. -/
theorem isCone_stellarSubdivision (hσ : σ ∈ K) (hstar : closedStar K σ = K) :
    IsCone (stellarSubdivision K σ v) v where
  apex_mem := singleton_mem_stellarSubdivision_iff.mpr hσ
  insert_mem τ hτ := by
    rcases hτ with ⟨hvτ, hτK, hτσ⟩ | ⟨hvτ, h₁, h₂⟩
    · refine (insert_mem_stellarSubdivision_iff hvτ).mpr ⟨hτσ, ?_⟩
      have hmem : τ ∈ closedStar K σ := by rw [hstar]; exact hτK
      exact (mem_closedStar.mp hmem).2
    · rw [Finset.insert_eq_self.mpr hvτ]
      exact Or.inr ⟨hvτ, h₁, h₂⟩

/-- Starring a simplex at its whole vertex set produces a cone with apex the new vertex. -/
theorem isCone_stellarSubdivision_simplex (hV : V.Nonempty) :
    IsCone (stellarSubdivision (simplex V) V v) v :=
  isCone_stellarSubdivision (self_mem_simplex.mpr hV) (closedStar_simplex Finset.Subset.rfl)

/-- **The starred simplex is the cone on the simplex boundary**: the link of the new vertex is
exactly `simplexBoundary V`. This is the standard model of the move, and pins the convention. -/
theorem link_stellarSubdivision_simplex (hv : v ∉ V) :
    link (stellarSubdivision (simplex V) V v) {v} = simplexBoundary V := by
  rw [link_stellarSubdivision_singleton fun h => hv (singleton_mem_simplex.mp h),
    closedStar_simplex Finset.Subset.rfl, deletion_simplex_self,
    inf_eq_right.mpr simplexBoundary_le_simplex]

/-- A starred simplex is collapsible: it is a finite cone with apex the new vertex. -/
theorem collapsible_stellarSubdivision_simplex (hV : V.Nonempty) :
    Collapsible (stellarSubdivision (simplex V) V v) :=
  (isCone_stellarSubdivision_simplex hV).collapsible
    (finite_faces_stellarSubdivision (finite_faces_simplex V))

/-- Starring a simplex at its whole vertex set leaves the dimension at `V.card - 1`. -/
theorem dimension_stellarSubdivision_simplex (hv : v ∉ V) (hV : V.Nonempty) :
    dimension (stellarSubdivision (simplex V) V v) = ((V.card - 1 : ℕ) : WithBot ℕ∞) := by
  rw [dimension_stellarSubdivision (fun h => hv (singleton_mem_simplex.mp h))
    (self_mem_simplex.mpr hV), dimension_simplex hV]

end PreAbstractSimplicialComplex
