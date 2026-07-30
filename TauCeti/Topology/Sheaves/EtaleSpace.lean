/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sheaves.EtaleSpace

/-!
# Local charts on the étalé space of a presheaf

This file supplies the local-homeomorphism API for the étalé space of a presheaf.  A section
over an open set determines a continuous section of the étalé projection, whose range consists
of its germs.  This range is open and gives a local chart.  Consequently, the projection from
the étalé space to its base is a local homeomorphism.

The construction extends the étalé-space topology and germ API in
`Mathlib.Topology.Sheaves.EtaleSpace`.  It is the topological prerequisite for applying
Mathlib's abstract `IsLocalHomeomorph.monodromy_theorem` to analytic continuation: the remaining
analytic input is separatedness of the projection, supplied by the identity theorem for
holomorphic functions.
-/

public section

open CategoryTheory Function Set TopologicalSpace

namespace TauCeti

namespace TopCat.Presheaf.EtaleSpace

universe v u w

variable {X : TopCat.{v}} {C : Type u} [Category.{v} C] {CC : C → Type v}
  {FC : C → C → Type w} [∀ A B, FunLike (FC A B) (CC A) (CC B)]
  [ConcreteCategory C FC] [Limits.HasColimits.{v} C]

variable {F : X.Presheaf C}

/-- A section of a presheaf, viewed as a section of the étalé projection. -/
@[expose]
noncomputable def germSection (F : X.Presheaf C) (U : Opens X)
    (s : ToType (F.obj (Opposite.op U))) :
    U → F.EtaleSpace :=
  fun x ↦ ⟨x, F.germ U x x.2 s⟩

@[simp]
theorem base_germSection (U : Opens X) (s : ToType (F.obj (Opposite.op U))) (x : U) :
    (germSection F U s x).base = x :=
  (rfl)

@[simp]
theorem germ_germSection (U : Opens X) (s : ToType (F.obj (Opposite.op U))) (x : U) :
    (germSection F U s x).germ = F.germ U x x.2 s :=
  (rfl)

/-- The open set in the étalé space swept out by the germs of a section. -/
def sectionRange (F : X.Presheaf C) (U : Opens X) (s : ToType (F.obj (Opposite.op U))) :
    Set F.EtaleSpace :=
  Set.range (germSection F U s)

/-- Membership in the range of a germ section means being the germ of that section at the
underlying base point. -/
@[simp]
theorem mem_sectionRange_iff {U : Opens X} {s : ToType (F.obj (Opposite.op U))}
    {g : F.EtaleSpace} :
    g ∈ sectionRange F U s ↔ ∃ h : g.base ∈ U, g.germ = F.germ U g.base h s := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, rfl⟩
  · rintro ⟨h, hg⟩
    refine ⟨⟨g.base, h⟩, ?_⟩
    cases g
    simp only [germSection, TopCat.Presheaf.EtaleSpace.mk.injEq]
    exact ⟨trivial, heq_of_eq hg.symm⟩

/-- The germs of a section form an open subset of the étalé space. -/
theorem isOpen_sectionRange (U : Opens X) (s : ToType (F.obj (Opposite.op U))) :
    IsOpen (sectionRange F U s) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨U, s, Set.ext fun g ↦ mem_sectionRange_iff.symm⟩

/-- A germ section is injective because the étalé projection recovers its argument. -/
theorem germSection_injective (U : Opens X) (s : ToType (F.obj (Opposite.op U))) :
    Function.Injective (germSection F U s) :=
  fun _ _ h ↦ Subtype.ext <| congr_arg TopCat.Presheaf.EtaleSpace.base h

variable [Limits.PreservesFilteredColimits (forget C)]

/-- The map taking a point to the germ of a fixed section there is continuous. -/
theorem continuous_germSection (U : Opens X) (s : ToType (F.obj (Opposite.op U))) :
    Continuous (germSection F U s) := by
  rw [continuous_generateFrom_iff]
  rintro _ ⟨V, t, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  rintro x ⟨hxV, hst⟩
  -- Expose the dependent stalk index so that `Presheaf.germ_eq` applies at the base point `x`.
  change F.germ U (x : X) x.2 s = F.germ V (x : X) hxV t at hst
  obtain ⟨W, hxW, iWU, iWV, heq⟩ :=
    F.germ_eq x x.2 hxV s t hst
  let WU : Set U := Subtype.val ⁻¹' W
  refine ⟨WU, ?_, ?_, ?_⟩
  · rintro y hy
    have hyW : (y : X) ∈ W := hy
    refine ⟨iWV.le hyW, ?_⟩
    -- As above, the target topology presents this equality with an implicit dependent index.
    change F.germ U (y : X) y.2 s = F.germ V (y : X) _ t
    exact F.germ_ext W hyW iWU iWV heq
  · exact W.isOpen.preimage continuous_subtype_val
  · exact hxW

/-- The local chart on the étalé space determined by a section of a presheaf.

On `sectionRange F U s`, the chart is the étalé projection to `U`; its inverse sends a point
to the germ of `s` at that point. -/
private noncomputable def sectionOpenPartialHomeomorph (F : X.Presheaf C) (U : Opens X)
    (s : ToType (F.obj (Opposite.op U))) (x₀ : U) :
    OpenPartialHomeomorph F.EtaleSpace X := by
  classical
  exact
    { toFun := TopCat.Presheaf.EtaleSpace.base
      invFun x := if hx : x ∈ U then germSection F U s ⟨x, hx⟩ else germSection F U s x₀
      source := sectionRange F U s
      target := U
      map_source' := by
        rintro g ⟨x, rfl⟩
        exact x.2
      map_target' := by
        intro x hx
        split
        · exact ⟨⟨x, hx⟩, rfl⟩
        · contradiction
      left_inv' := by
        rintro g ⟨x, rfl⟩
        split
        · rename_i h
          congr
        · rename_i h
          exact (h x.2).elim
      right_inv' := by
        intro x hx
        split
        · rfl
        · contradiction
      open_source := isOpen_sectionRange U s
      open_target := U.isOpen
      continuousOn_toFun := (TopCat.Presheaf.EtaleSpace.continuous_base F).continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        apply (continuous_germSection U s).congr
        intro x
        dsimp only [Set.restrict]
        split
        · congr
        · rename_i h
          exact (h x.2).elim }

/-- The projection from the étalé space of a presheaf to the base is a local homeomorphism. -/
theorem isLocalHomeomorph_base (F : X.Presheaf C) :
    IsLocalHomeomorph (TopCat.Presheaf.EtaleSpace.base (F := F)) := by
  apply IsLocalHomeomorph.mk
  intro g
  obtain ⟨U, hgU, s, hs⟩ := F.exists_germ_eq g.germ
  let e := sectionOpenPartialHomeomorph F U s ⟨g.base, hgU⟩
  refine ⟨e, ?_, fun _ _ ↦ rfl⟩
  -- Unfold the private chart only to expose its source as the range of the chosen germ section.
  change g ∈ sectionRange F U s
  rw [mem_sectionRange_iff]
  exact ⟨hgU, hs.symm⟩

/-- A germ section is an open embedding of its domain into the étalé space. -/
theorem isOpenEmbedding_germSection (U : Opens X) (s : ToType (F.obj (Opposite.op U))) :
    Topology.IsOpenEmbedding (germSection F U s) := by
  apply (isLocalHomeomorph_base F).isOpenEmbedding_of_comp
  · have hcomp :
        TopCat.Presheaf.EtaleSpace.base ∘ germSection F U s = (Subtype.val : U → X) := by
      funext x
      exact base_germSection U s x
    rw [hcomp]
    exact U.isOpen.isOpenEmbedding_subtypeVal
  · exact continuous_germSection U s

end TopCat.Presheaf.EtaleSpace

end TauCeti
