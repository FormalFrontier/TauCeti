/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Sub-Hodge structures and the strictness of Hodge morphisms

A subspace of the ambient complex vector space of a pure Hodge structure is a **sub-Hodge
structure** when it is stable under the conjugation and is spanned by its intersections with the
Hodge components. Such a subspace inherits a pure Hodge structure of the same weight, namely the
ambient filtration intersected with it: opposedness survives because the two complementary
ambient steps already cover the subspace componentwise.

The two conditions are equivalent to conjugation stability together with stability under the
Hodge projections, and that reformulation is what makes the subobjects of the theory easy to
recognise. It is used here to identify the kernel and the image of a morphism of pure Hodge
structures as sub-Hodge structures — and, dually, the quotient by a sub-Hodge structure as a pure
Hodge structure again, so that the cokernel of a morphism is one — and then to prove that a
morphism of pure Hodge structures is **strict**: its image meets every step of the target
filtration exactly in the image of that step,

`range f ⊓ F'^p = f (F^p)`,

and likewise componentwise, `range f ⊓ H'^{p,n-p} = f (H^{p,n-p})`. The mechanism is that a
morphism intertwines the Hodge projections of source and target, so it is a graded map for the
two Hodge decompositions; strictness is then bookkeeping on degrees.

Statements are given for the conjugation-parametric object `HodgeStructureOn` and for the
unbundled morphism predicate `TauCeti.Hodge.HodgeStructureOn.IsMorphism`. The bundled integral
morphisms of `TauCeti.Hodge.HodgeStructure.Hom` satisfy that predicate, so every result
specialises to them.

These are the subobject companions of Layers L0 and L1 of
`TauCetiRoadmap/HodgeStructures/README.md`: the kernel and image of a Hodge morphism are the
subobjects a categorical reading of the semisimplicity of polarizable rational Hodge structures
quantifies over, and strictness for a pure structure is the graded shadow of Deligne's strictness
theorem for mixed Hodge structures. Following Peters–Steenbrink, *Mixed Hodge Structures*, §2.1,
and Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.IsSubstructure`: a conjugation-stable subspace spanned by its
  intersections with the Hodge components.
* `TauCeti.Hodge.HodgeStructureOn.isSubstructure_iff_proj_mem`: equivalently, a conjugation-stable
  subspace stable under the Hodge projections.
* `TauCeti.Hodge.HodgeStructureOn.IsSubstructure.hodgeStructure`: the pure Hodge structure induced
  on a sub-Hodge structure, with components the intersections with the ambient components.
* `TauCeti.Hodge.HodgeStructureOn.IsSubstructure.quotient`: the pure Hodge structure induced on the
  quotient by a sub-Hodge structure, with components the images of the ambient components; applied
  to the image of a morphism it is the cokernel.
* `TauCeti.Hodge.HodgeStructureOn.IsMorphism.proj_comp`: a morphism of pure Hodge structures
  intertwines the Hodge projections.
* `TauCeti.Hodge.HodgeStructureOn.IsMorphism.isSubstructure_ker` and
  `…isSubstructure_range`: the kernel and the image of a morphism are sub-Hodge structures.
* `TauCeti.Hodge.HodgeStructureOn.IsMorphism.range_inf_F`: **strictness**, `range f ⊓ F'^p`
  is the image of `F^p`; `…range_inf_piece` and `…range_inf_conjF` are the componentwise and
  conjugate forms.
-/

public section

namespace TauCeti.Hodge

universe u v u' v'

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-! ### Sub-Hodge structures -/

/-- A **sub-Hodge structure** of a pure Hodge structure: a complex subspace stable under the
conjugation and spanned by its intersections with the Hodge components.

The reverse inequality `⨆ p, U ⊓ hs.piece p ≤ U` holds for any subspace, so the second field is
the whole of the spanning condition; see
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure.eq_iSup_inf_piece`. -/
structure IsSubstructure (hs : HodgeStructureOn W ω n) (U : Submodule ℂ W) : Prop where
  /-- The subspace is stable under the conjugation. -/
  conj_mem : ∀ x ∈ U, ω.toEquiv x ∈ U
  /-- The subspace is spanned by its intersections with the Hodge components. -/
  le_iSup_inf_piece : U ≤ ⨆ p, U ⊓ hs.piece p

variable {hs : HodgeStructureOn W ω n} {U : Submodule ℂ W}

/-- A conjugation-stable subspace stable under the Hodge projections is a sub-Hodge structure. -/
theorem isSubstructure_of_proj_mem (hconj : ∀ x ∈ U, ω.toEquiv x ∈ U)
    (hproj : ∀ p, ∀ x ∈ U, hs.proj p x ∈ U) : hs.IsSubstructure U where
  conj_mem := hconj
  le_iSup_inf_piece x hx :=
    hs.mem_iSup_of_proj_mem fun p ↦ Submodule.mem_inf.2 ⟨hproj p x hx, hs.proj_mem p x⟩

namespace IsSubstructure

/-- A sub-Hodge structure is the sum of its intersections with the Hodge components. -/
theorem eq_iSup_inf_piece (h : hs.IsSubstructure U) : U = ⨆ p, U ⊓ hs.piece p :=
  le_antisymm h.le_iSup_inf_piece (iSup_le fun _ ↦ inf_le_left)

/-- A sub-Hodge structure is stable under the Hodge projections. -/
theorem proj_mem (h : hs.IsSubstructure U) {x : W} (hx : x ∈ U) (p : ℤ) : hs.proj p x ∈ U :=
  hs.proj_mem_of_le_iSup_inf h.le_iSup_inf_piece hx p

/-- Conjugation maps a sub-Hodge structure onto itself. -/
theorem map_conj (h : hs.IsSubstructure U) : U.map ω.toEquiv.toLinearMap = U := by
  refine le_antisymm ?_ fun x hx ↦ ⟨ω.toEquiv x, h.conj_mem x hx, ω.apply_apply x⟩
  rintro _ ⟨x, hx, rfl⟩
  exact h.conj_mem x hx

/-- The conjugation induced on a sub-Hodge structure. -/
noncomputable def conjugation (h : hs.IsSubstructure U) : Conjugation U :=
  ω.restrict h.conj_mem

@[simp]
theorem conjugation_toEquiv_apply (h : hs.IsSubstructure U) (x : U) :
    (h.conjugation.toEquiv x : W) = ω.toEquiv x := by
  simp [conjugation]

/-- A filtration step and the complementary conjugate step cover a sub-Hodge structure: each of
its Hodge components lies in one of the two. -/
theorem le_inf_F_sup_inf_conjF (h : hs.IsSubstructure U) (p : ℤ) :
    U ≤ U ⊓ hs.F p ⊔ U ⊓ hs.conjF (n + 1 - p) := by
  conv_lhs => rw [h.eq_iSup_inf_piece]
  refine iSup_le fun q ↦ ?_
  rcases lt_or_ge q p with hq | hq
  · exact le_sup_of_le_right (inf_le_inf_left _ (hs.piece_le_conjF_of_lt hq))
  · exact le_sup_of_le_left (inf_le_inf_left _ ((hs.piece_le_F q).trans (hs.F_antitone hq)))

/-- The pure Hodge structure induced on a sub-Hodge structure: its filtration is the ambient
filtration intersected with the subspace, and it is opposed because the ambient components already
cover the subspace. -/
noncomputable def hodgeStructure (h : hs.IsSubstructure U) :
    HodgeStructureOn U h.conjugation n where
  F p := (hs.F p).comap U.subtype
  F_antitone _ _ hpq := Submodule.comap_mono (hs.F_antitone hpq)
  F_top := by
    obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p, by rw [hp, Submodule.comap_top]⟩
  opposed p := by
    rw [conjugation, Conjugation.map_restrict_comap_subtype, ← hs.conjF_def]
    exact TauCeti.Submodule.isCompl_comap_subtype (hs.isCompl_F_conjF p).disjoint
      (h.le_inf_F_sup_inf_conjF p)

/-- The induced Hodge filtration is the ambient filtration intersected with the subspace. -/
@[simp]
theorem hodgeStructure_F (h : hs.IsSubstructure U) (p : ℤ) :
    h.hodgeStructure.F p = (hs.F p).comap U.subtype :=
  (rfl)

/-- The induced conjugate filtration is the ambient conjugate filtration intersected with the
subspace. -/
@[simp]
theorem hodgeStructure_conjF (h : hs.IsSubstructure U) (p : ℤ) :
    h.hodgeStructure.conjF p = (hs.conjF p).comap U.subtype := by
  rw [HodgeStructureOn.conjF_def, hodgeStructure_F, conjugation,
    Conjugation.map_restrict_comap_subtype, ← hs.conjF_def]

/-- An induced Hodge component is the ambient component of the same degree intersected with the
subspace. -/
@[simp]
theorem hodgeStructure_piece (h : hs.IsSubstructure U) (p : ℤ) :
    h.hodgeStructure.piece p = (hs.piece p).comap U.subtype := by
  rw [HodgeStructureOn.piece_def, hodgeStructure_F, hodgeStructure_conjF, hs.piece_def,
    Submodule.comap_inf]

/-- The inclusion of a sub-Hodge structure into its ambient Hodge structure is a morphism. -/
theorem isMorphism_subtype (h : hs.IsSubstructure U) :
    IsMorphism h.hodgeStructure hs U.subtype where
  commutes_conj x := by simp
  map_F_le p := by
    rw [h.hodgeStructure_F]
    exact Submodule.map_comap_le U.subtype (hs.F p)

/-! #### Quotients by a sub-Hodge structure -/

/-- Conjugating in the quotient by a sub-Hodge structure is conjugating upstairs. -/
theorem map_quotient_conj_map_mkQ (h : hs.IsSubstructure U) (A : Submodule ℂ W) :
    (A.map U.mkQ).map (ω.quotient h.conj_mem).toEquiv.toLinearMap =
      (A.map ω.toEquiv.toLinearMap).map U.mkQ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨ω.toEquiv x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨U.mkQ x, ⟨x, hx, rfl⟩, by simp⟩

/-- A filtration step meets the sum of the complementary conjugate step with a sub-Hodge structure
inside that sub-Hodge structure: this is what makes opposedness descend to the quotient. -/
theorem F_inf_conjF_sup_le (h : hs.IsSubstructure U) (p : ℤ) :
    hs.F p ⊓ (hs.conjF (n + 1 - p) ⊔ U) ≤ U := by
  have hU : U = U ⊓ hs.F p ⊔ U ⊓ hs.conjF (n + 1 - p) :=
    le_antisymm (h.le_inf_F_sup_inf_conjF p) (sup_le inf_le_left inf_le_left)
  have h1 : hs.conjF (n + 1 - p) ⊔ U = U ⊓ hs.F p ⊔ hs.conjF (n + 1 - p) := by
    refine le_antisymm (sup_le le_sup_right ?_)
      (sup_le (le_sup_of_le_right inf_le_left) le_sup_left)
    calc U = U ⊓ hs.F p ⊔ U ⊓ hs.conjF (n + 1 - p) := hU
      _ ≤ U ⊓ hs.F p ⊔ hs.conjF (n + 1 - p) := sup_le_sup_left inf_le_right _
  rw [h1, inf_comm, sup_inf_assoc_of_le _ (inf_le_right : U ⊓ hs.F p ≤ hs.F p),
    inf_comm (hs.conjF (n + 1 - p)) (hs.F p),
    disjoint_iff.mp (hs.isCompl_F_conjF p).disjoint, sup_bot_eq]
  exact inf_le_left

/-- The pure Hodge structure induced on the quotient by a sub-Hodge structure: its filtration is
the image of the ambient filtration. Opposedness descends because the sub-Hodge structure is
itself split by the two complementary ambient steps. -/
noncomputable def quotient (h : hs.IsSubstructure U) :
    HodgeStructureOn (W ⧸ U) (ω.quotient h.conj_mem) n where
  F p := (hs.F p).map U.mkQ
  F_antitone _ _ hpq := Submodule.map_mono (hs.F_antitone hpq)
  F_top := by
    obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p, by rw [hp, Submodule.map_top, Submodule.range_mkQ]⟩
  opposed p := by
    rw [h.map_quotient_conj_map_mkQ, ← hs.conjF_def]
    constructor
    · rw [disjoint_iff, Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_mkQ,
        ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ,
        sup_comm]
      exact h.F_inf_conjF_sup_le p
    · rw [codisjoint_iff, ← Submodule.map_sup, (hs.isCompl_F_conjF p).sup_eq_top,
        Submodule.map_top, Submodule.range_mkQ]

/-- The filtration of the quotient Hodge structure is the image of the ambient filtration. -/
@[simp]
theorem quotient_F (h : hs.IsSubstructure U) (p : ℤ) :
    h.quotient.F p = (hs.F p).map U.mkQ :=
  (rfl)

/-- The conjugate filtration of the quotient Hodge structure is the image of the ambient conjugate
filtration. -/
@[simp]
theorem quotient_conjF (h : hs.IsSubstructure U) (p : ℤ) :
    h.quotient.conjF p = (hs.conjF p).map U.mkQ := by
  rw [HodgeStructureOn.conjF_def, quotient_F, h.map_quotient_conj_map_mkQ, ← hs.conjF_def]

variable {W' : Type v} [AddCommGroup W'] [Module ℂ W']
variable {ω' : Conjugation W'} {hs' : HodgeStructureOn W' ω' n} {g : W →ₗ[ℂ] W'}

/-- A morphism killing a sub-Hodge structure descends to a morphism from the quotient. -/
theorem isMorphism_liftQ (h : hs.IsSubstructure U) (hg : IsMorphism hs hs' g)
    (hU : U ≤ LinearMap.ker g) : IsMorphism h.quotient hs' (U.liftQ g hU) where
  commutes_conj x := by
    obtain ⟨x, rfl⟩ := U.mkQ_surjective x
    simp only [Submodule.mkQ_apply, Conjugation.quotient_toEquiv_mk, Submodule.liftQ_apply]
    exact hg.commutes_conj x
  map_F_le p := by
    rw [h.quotient_F, ← Submodule.map_comp, U.liftQ_mkQ]
    exact hg.map_F_le p

/-- The descended Hodge morphism is the unique one whose composite with the quotient map is the
original morphism. -/
theorem existsUnique_isMorphism_liftQ (h : hs.IsSubstructure U) (hg : IsMorphism hs hs' g)
    (hU : U ≤ LinearMap.ker g) :
    ∃! q : (W ⧸ U) →ₗ[ℂ] W',
      IsMorphism h.quotient hs' q ∧ q ∘ₗ U.mkQ = g := by
  refine ⟨U.liftQ g hU, ⟨h.isMorphism_liftQ hg hU, U.liftQ_mkQ g hU⟩, ?_⟩
  intro q hq
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := U.mkQ_surjective x
  calc
    q (U.mkQ y) = g y := DFunLike.congr_fun hq.2 y
    _ = U.liftQ g hU (U.mkQ y) := by
      simp only [Submodule.mkQ_apply, Submodule.liftQ_apply]

end IsSubstructure

/-- A subspace is a sub-Hodge structure exactly when it is stable under the conjugation and under
every Hodge projection. -/
theorem isSubstructure_iff_proj_mem :
    hs.IsSubstructure U ↔ (∀ x ∈ U, ω.toEquiv x ∈ U) ∧ ∀ p, ∀ x ∈ U, hs.proj p x ∈ U :=
  ⟨fun h ↦ ⟨h.conj_mem, fun p _ hx ↦ h.proj_mem hx p⟩, fun h ↦
    isSubstructure_of_proj_mem h.1 h.2⟩

@[simp]
theorem isSubstructure_bot : hs.IsSubstructure (⊥ : Submodule ℂ W) :=
  isSubstructure_of_proj_mem
    (fun x hx ↦ by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])
    (fun _ x hx ↦ by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])

@[simp]
theorem isSubstructure_top : hs.IsSubstructure (⊤ : Submodule ℂ W) :=
  isSubstructure_of_proj_mem (fun _ _ ↦ Submodule.mem_top) (fun _ _ _ ↦ Submodule.mem_top)

/-- Sub-Hodge structures are closed under intersection. -/
theorem IsSubstructure.inf {U U' : Submodule ℂ W} (h : hs.IsSubstructure U)
    (h' : hs.IsSubstructure U') : hs.IsSubstructure (U ⊓ U') :=
  isSubstructure_of_proj_mem
    (fun _ hx ↦ Submodule.mem_inf.2 ⟨h.conj_mem _ hx.1, h'.conj_mem _ hx.2⟩)
    (fun _ _ hx ↦ Submodule.mem_inf.2 ⟨h.proj_mem hx.1 _, h'.proj_mem hx.2 _⟩)

/-- Sub-Hodge structures are closed under sum. -/
theorem IsSubstructure.sup {U U' : Submodule ℂ W} (h : hs.IsSubstructure U)
    (h' : hs.IsSubstructure U') : hs.IsSubstructure (U ⊔ U') := by
  refine isSubstructure_of_proj_mem (fun x hx ↦ ?_) (fun p x hx ↦ ?_) <;>
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  · rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (h.conj_mem y hy))
      (Submodule.mem_sup_right (h'.conj_mem z hz))
  · rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (h.proj_mem hy p))
      (Submodule.mem_sup_right (h'.proj_mem hz p))

/-! ### Morphisms of pure Hodge structures -/

variable {W' : Type v} [AddCommGroup W'] [Module ℂ W']
variable {ω' : Conjugation W'} {hs' : HodgeStructureOn W' ω' n} {g : W →ₗ[ℂ] W'}

namespace IsMorphism

/-- **A morphism of pure Hodge structures is graded**: it intertwines the Hodge projections of the
source and of the target. -/
theorem proj_comp (h : IsMorphism hs hs' g) (p : ℤ) : hs'.proj p ∘ₗ g = g ∘ₗ hs.proj p := by
  refine hs.linearMap_ext_of_piece fun q x hx ↦ ?_
  have hgx : g x ∈ hs'.piece q := h.map_piece_le q ⟨x, hx, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rcases eq_or_ne q p with rfl | hqp
  · rw [hs.proj_apply_of_mem hx, hs'.proj_apply_of_mem hgx]
  · rw [hs.proj_apply_eq_zero_of_mem_of_ne hx hqp, hs'.proj_apply_eq_zero_of_mem_of_ne hgx hqp,
      map_zero]

/-- Elementwise form of gradedness: the `p`-th projection of an image is the image of the `p`-th
projection. -/
theorem proj_apply (h : IsMorphism hs hs' g) (p : ℤ) (x : W) :
    hs'.proj p (g x) = g (hs.proj p x) :=
  congrFun (congrArg DFunLike.coe (h.proj_comp p)) x

/-- **The kernel of a morphism of pure Hodge structures is a sub-Hodge structure.** -/
theorem isSubstructure_ker (h : IsMorphism hs hs' g) : hs.IsSubstructure (LinearMap.ker g) := by
  refine isSubstructure_of_proj_mem (fun x hx ↦ ?_) (fun p x hx ↦ ?_) <;>
    rw [LinearMap.mem_ker] at hx ⊢
  · rw [h.commutes_conj, hx, map_zero]
  · rw [← h.proj_apply, hx, map_zero]

/-- **The image of a morphism of pure Hodge structures is a sub-Hodge structure.** -/
theorem isSubstructure_range (h : IsMorphism hs hs' g) :
    hs'.IsSubstructure (LinearMap.range g) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨ω.toEquiv x, h.commutes_conj x⟩
  · rintro _ ⟨x, rfl⟩
    refine hs'.mem_iSup_of_proj_mem fun p ↦ Submodule.mem_inf.2 ?_
    rw [h.proj_apply]
    exact ⟨⟨hs.proj p x, rfl⟩, h.map_piece_le p ⟨_, hs.proj_mem p x, rfl⟩⟩

/-- **Componentwise strictness.** The image of a morphism meets a Hodge component of the target
exactly in the image of the corresponding component of the source. -/
theorem range_inf_piece (h : IsMorphism hs hs' g) (p : ℤ) :
    LinearMap.range g ⊓ hs'.piece p = (hs.piece p).map g := by
  refine le_antisymm ?_ (le_inf ?_ (h.map_piece_le p))
  · rintro y ⟨⟨x, rfl⟩, hy⟩
    rw [← hs'.proj_apply_of_mem hy, h.proj_apply]
    exact Submodule.mem_map_of_mem (hs.proj_mem p x)
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

/-- **Strictness of a morphism of pure Hodge structures.** The image meets a step of the target
Hodge filtration exactly in the image of that step of the source filtration. -/
theorem range_inf_F (h : IsMorphism hs hs' g) (p : ℤ) :
    LinearMap.range g ⊓ hs'.F p = (hs.F p).map g := by
  refine le_antisymm ?_ (le_inf ?_ (h.map_F_le p))
  · rintro y ⟨⟨x, rfl⟩, hy⟩
    refine hs'.mem_of_proj_mem fun q ↦ ?_
    rcases lt_or_ge q p with hq | hq
    · rw [hs'.proj_eq_zero_of_mem_F_of_lt hy hq]
      exact Submodule.zero_mem _
    · rw [h.proj_apply]
      exact Submodule.mem_map_of_mem
        ((hs.F_antitone hq) (hs.piece_le_F q (hs.proj_mem q x)))
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

/-- **Conjugate strictness.** The image meets a step of the conjugate target filtration exactly in
the image of the corresponding step of the source. -/
theorem range_inf_conjF (h : IsMorphism hs hs' g) (p : ℤ) :
    LinearMap.range g ⊓ hs'.conjF p = (hs.conjF p).map g := by
  have hmap : ((hs.F p).map g).map ω'.toEquiv.toLinearMap =
      ((hs.F p).map ω.toEquiv.toLinearMap).map g := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ω.toEquiv x, ⟨x, hx, rfl⟩, h.commutes_conj x⟩
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, (h.commutes_conj x).symm⟩
  calc
    LinearMap.range g ⊓ hs'.conjF p
        = (LinearMap.range g).map ω'.toEquiv.toLinearMap ⊓
            (hs'.F p).map ω'.toEquiv.toLinearMap := by
          rw [h.isSubstructure_range.map_conj, hs'.conjF_def]
    _ = (LinearMap.range g ⊓ hs'.F p).map ω'.toEquiv.toLinearMap :=
          (Submodule.map_inf _ ω'.toEquiv.injective).symm
    _ = ((hs.F p).map g).map ω'.toEquiv.toLinearMap := by rw [h.range_inf_F p]
    _ = (hs.conjF p).map g := by rw [hmap, ← hs.conjF_def]

end IsMorphism

/-- The quotient map onto the Hodge structure of a quotient by a sub-Hodge structure is a morphism
of pure Hodge structures. -/
theorem IsSubstructure.isMorphism_mkQ (h : hs.IsSubstructure U) :
    IsMorphism hs h.quotient U.mkQ where
  commutes_conj _ := by simp
  map_F_le p := le_of_eq (h.quotient_F p).symm

/-- The Hodge components of a quotient by a sub-Hodge structure are the images of the ambient
components: the quotient map is strict, so its componentwise strictness identifies them. -/
@[simp]
theorem IsSubstructure.quotient_piece (h : hs.IsSubstructure U) (p : ℤ) :
    h.quotient.piece p = (hs.piece p).map U.mkQ := by
  have hrange := h.isMorphism_mkQ.range_inf_piece p
  rwa [Submodule.range_mkQ, top_inf_eq] at hrange

end HodgeStructureOn

/-! ### Bundled integral morphisms -/

namespace HodgeStructure.Hom

variable {V₁ : Type u} {V₂ : Type u'} {W₁ : Type v} {W₂ : Type v'}
variable [AddCommGroup V₁] [AddCommGroup V₂]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂}
variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {n : ℤ}
variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}

/-- The kernel of an integral Hodge morphism is a sub-Hodge structure of the source. -/
theorem isSubstructure_ker (f : Hom source target) :
    source.IsSubstructure (LinearMap.ker f.toLinearMap) :=
  f.isMorphism.isSubstructure_ker

/-- The image of an integral Hodge morphism is a sub-Hodge structure of the target. -/
theorem isSubstructure_range (f : Hom source target) :
    target.IsSubstructure (LinearMap.range f.toLinearMap) :=
  f.isMorphism.isSubstructure_range

/-- **Strictness of an integral Hodge morphism.** -/
theorem range_inf_F (f : Hom source target) (p : ℤ) :
    LinearMap.range f.toLinearMap ⊓ target.F p = (source.F p).map f.toLinearMap :=
  f.isMorphism.range_inf_F p

/-- Componentwise strictness of an integral Hodge morphism. -/
theorem range_inf_piece (f : Hom source target) (p : ℤ) :
    LinearMap.range f.toLinearMap ⊓ target.piece p = (source.piece p).map f.toLinearMap :=
  f.isMorphism.range_inf_piece p

/-- Conjugate strictness of an integral Hodge morphism. -/
theorem range_inf_conjF (f : Hom source target) (p : ℤ) :
    LinearMap.range f.toLinearMap ⊓ target.conjF p = (source.conjF p).map f.toLinearMap :=
  f.isMorphism.range_inf_conjF p

end HodgeStructure.Hom

end TauCeti.Hodge
