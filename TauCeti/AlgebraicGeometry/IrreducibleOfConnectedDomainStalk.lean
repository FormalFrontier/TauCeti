/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module


public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Irreducibility of connected schemes with domain stalks

This file supplies a prerequisite for the **Standing hypotheses** target of the
Jacobian challenge roadmap (proving that a regular connected scheme is irreducible,
as regular stalks are integral domains).

We prove that a locally noetherian connected scheme whose stalks have unique
minimal primes is irreducible (`irreducibleSpace_of_connected_of_unique_minimalPrime_stalk`),
from which we deduce that such a scheme is irreducible if its stalks are
integral domains (`irreducibleSpace_of_connected_of_isDomain_stalk`).

The proof proceeds by showing that the irreducible components of such
a scheme are pairwise disjoint and open (hence clopen), so
connectedness forces a unique component.

Along the way we show that the minimal primes of the stalk at a point
and the irreducible components containing that point are in bijection.
-/

public section

open TopologicalSpace Set AlgebraicGeometry Topology CategoryTheory PrimeSpectrum

universe u

namespace TauCeti

namespace AlgebraicGeometry

/-- The closure of the image of an irreducible component under an open
embedding is an irreducible component. -/
private lemma closure_image_mem_irreducibleComponents {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsOpenEmbedding f) {c : Set α}
    (hc : c ∈ irreducibleComponents α) :
    closure (f '' c) ∈ irreducibleComponents β := by
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure (f '' c)) (isIrreducible_iff_closure.mpr (hc.1.image f hf.continuous.continuousOn))
  have h_nonempty : (C ∩ range f).Nonempty := by
    obtain ⟨x, hx⟩ := hc.1.nonempty
    have hxC : f x ∈ C := hsub (subset_closure (mem_image_of_mem f hx))
    exact ⟨f x, hxC, ⟨x, rfl⟩⟩
  have h_pre := preimage_mem_irreducibleComponents hC hf h_nonempty
  have h_eq : c = f ⁻¹' C := by
    have h_sub : c ⊆ f ⁻¹' C := fun x hx ↦ hsub (subset_closure (mem_image_of_mem f hx))
    exact h_sub.antisymm (hc.2 h_pre.1 h_sub)
  have hC_eq : C = closure (f '' c) := by
    rw [h_eq]
    have := closure_image_preimage_of_isPreirreducible f hf.isOpenMap C
      (by obtain ⟨_, hC_mem, ⟨x, rfl⟩⟩ := h_nonempty; exact ⟨x, hC_mem⟩) hC.1.2
      (isClosed_of_mem_irreducibleComponents C hC)
    exact this.symm
  rwa [← hC_eq]

/-- Given an open embedding, irreducible components containing a point `x` are
in bijection with irreducible components containing `f x`. -/
private def irreducibleComponents_containing_equiv_of_isOpenEmbedding
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsOpenEmbedding f) (x : α) :
    { c : irreducibleComponents α // x ∈ (c : Set α) } ≃
    { c : irreducibleComponents β // f x ∈ (c : Set β) } where
  toFun c := ⟨⟨closure (f '' c.val.val),
    closure_image_mem_irreducibleComponents hf c.val.property⟩, by
    dsimp
    exact subset_closure (mem_image_of_mem f c.property)⟩
  invFun c' :=
    have hNonempty : (c'.val.val ∩ range f).Nonempty := ⟨f x, c'.property, ⟨x, rfl⟩⟩
    ⟨⟨f ⁻¹' c'.val.val, preimage_mem_irreducibleComponents c'.val.property hf hNonempty⟩,
      c'.property⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact hf.isOpenMap.preimage_closure_image hf.injective hf.continuous c.val.val
      (isClosed_of_mem_irreducibleComponents c.val.val c.val.property)
  right_inv c' := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact closure_image_preimage_of_isPreirreducible f hf.isOpenMap c'.val.val
      ⟨x, c'.property⟩ c'.val.property.1.2
      (isClosed_of_mem_irreducibleComponents c'.val.val c'.val.property)

/-- Equivalence of irreducible components under homeomorphism. -/
private def _root_.Homeomorph.irreducibleComponentsEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) : irreducibleComponents X ≃ irreducibleComponents Y :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber h.symm h.symm.continuous h.symm.isOpenMap
    (fun _ ↦ (subsingleton_singleton.preimage h.symm.injective).isPreirreducible)
    h.symm.surjective).toEquiv


/-- A ring isomorphism induces an equivalence of minimal primes. -/
private noncomputable def minimalPrimes_equiv_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    minimalPrimes A ≃ minimalPrimes B :=
  let eC := Homeomorph.irreducibleComponentsEquiv
    (homeomorphOfRingEquiv e).symm
  let eC_dual : (irreducibleComponents (PrimeSpectrum A))ᵒᵈ ≃
      (irreducibleComponents (PrimeSpectrum B))ᵒᵈ :=
    OrderDual.toDual.symm.trans (eC.symm.trans OrderDual.toDual)
  (minimalPrimes.equivIrreducibleComponents A).toEquiv.trans
    (eC_dual.trans (minimalPrimes.equivIrreducibleComponents B).symm.toEquiv)

/-- The minimal primes of the localization `A` of a ring `R` at the prime complement of `p`
are in bijection with the minimal primes of `R` contained in `p`. -/
private def minimalPrimesEquivMinimalPrimesLe {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (hS : S = p.asIdeal.primeCompl) :
    minimalPrimes A ≃ { q : minimalPrimes R // q.val ≤ p.asIdeal } :=
  ((Equiv.subtypeSubtypeEquivSubtype
    (fun {I : Ideal A} (hI : I ∈ minimalPrimes A) ↦ hI.1.1)).symm.trans
    ((PrimeSpectrum.equivSubtype A).symm.subtypeEquiv (fun _ ↦ Iff.rfl))).trans
  ((Equiv.subtypeEquiv (p := fun x ↦ x.asIdeal ∈ minimalPrimes A)
    (q := fun y ↦ y.val.asIdeal ∈ minimalPrimes R)
    (IsLocalization.primeSpectrumOrderIso S A).toEquiv (by
      intro q
      have hMap : minimalPrimes A = Ideal.under R ⁻¹' minimalPrimes R := by
        have h := IsLocalization.minimalPrimes_map S A (⊥ : Ideal R)
        rwa [Ideal.map_bot] at h
      rw [hMap]
      rfl)).trans
  { toFun := fun q' ↦ ⟨⟨q'.val.val.asIdeal, q'.property⟩, by
      have hq_disj := q'.val.property
      have h1 : Disjoint (p.asIdeal.primeCompl : Set R) (q'.val.val.asIdeal : Set R) := by
        rwa [← hS]
      -- We change the definitional representation of `primeCompl` to `(p.asIdeal : Set R)ᶜ`
      -- so that `disjoint_compl_left_iff_subset` can be matched and applied.
      change Disjoint ((p.asIdeal : Set R)ᶜ) (q'.val.val.asIdeal : Set R) at h1
      rwa [disjoint_compl_left_iff_subset] at h1⟩,
    invFun := fun q ↦
      have hq_disj : Disjoint (S : Set R) (q.val.val : Set R) := by
        rw [hS]
        -- We change the definitional representation of `primeCompl` to `(p.asIdeal : Set R)ᶜ`
        -- so that `disjoint_compl_left_iff_subset` can be matched and applied.
        change Disjoint ((p.asIdeal : Set R)ᶜ) (q.val.val : Set R)
        exact disjoint_compl_left_iff_subset.mpr q.property
      ⟨⟨⟨q.val.val, q.val.property.1.1⟩, hq_disj⟩, q.val.property⟩,
    left_inv := fun _ ↦ rfl,
    right_inv := fun _ ↦ rfl })

/-- Value of the cast of an order isomorphism over subtypes. -/
private lemma val_mpr_orderIso {α : Type u} [LE α] {Y : Type u} [LE Y] {P Q : Y → Prop}
    (h : P = Q) (f : α ≃o (Subtype P)ᵒᵈ) (q : α) :
    Subtype.val (OrderDual.ofDual
      (Eq.mpr (congrArg (fun T ↦ α ≃o (Subtype T)ᵒᵈ) h.symm) f q)) =
      Subtype.val (OrderDual.ofDual (f q)) := by
  subst h
  rfl

/-- Evaluating the `equivIrreducibleComponents` bijection on a minimal prime
yields its `zeroLocus`. -/
private theorem val_equivIrreducibleComponents (R : Type*) [CommRing R]
    (q : minimalPrimes R) :
    (OrderDual.ofDual ((minimalPrimes.equivIrreducibleComponents R).toEquiv q)).val =
      zeroLocus q.val := by
  unfold minimalPrimes.equivIrreducibleComponents
  have h_eq : (fun s ↦ s ∈ irreducibleComponents (PrimeSpectrum R)) =
      (fun s ↦ Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) s) :=
    irreducibleComponents_eq_maximals_closed (PrimeSpectrum R)
  have h_cast := val_mpr_orderIso (α := minimalPrimes R) (Y := Set (PrimeSpectrum R))
    (P := fun s ↦ Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) s)
    (Q := fun s ↦ s ∈ irreducibleComponents (PrimeSpectrum R))
    h_eq.symm
  erw [h_cast]
  dsimp [OrderIso.setOfPredMinimalIsoSetOfPredMaximal, OrderIso.trans]
  dsimp [PrimeSpectrum.pointsEquivIrreducibleCloseds]
  exact PrimeSpectrum.closure_singleton ⟨q.val, q.property.1.1⟩

/-- Irreducible components of `Spec R` containing a point `p`
are in bijection with minimal primes of `R` contained in `p`. -/
private noncomputable def
    irreducibleComponentsContainingEquivMinimalPrimesLe
    (R : Type*) [CommRing R] (p : PrimeSpectrum R) :
    { c : irreducibleComponents (PrimeSpectrum R) // p ∈ c.val } ≃
    { q : minimalPrimes R // q.val ≤ p.asIdeal } := by
  let e := (minimalPrimes.equivIrreducibleComponents R).symm.toEquiv
  refine (Equiv.subtypeEquiv e (p := fun c ↦ p ∈ (OrderDual.ofDual c).val)
    (q := fun q ↦ q.val ≤ p.asIdeal) ?_).trans ?_
  · intro c
    dsimp [e]
    have h_eq : c = e.symm (e c) := (e.left_inv c).symm
    conv_lhs => rw [h_eq]
    dsimp [e]
    erw [val_equivIrreducibleComponents]
    rfl
  · exact Equiv.refl _

/-- For an affine scheme `Spec R`, the minimal prime ideals of the local ring (stalk)
at a point `p` are in bijection with the irreducible components of `Spec R` containing `p`. -/
private noncomputable def stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec
    (R : Type*) [CommRing R] (p : PrimeSpectrum R) :
    minimalPrimes (Localization.AtPrime p.asIdeal) ≃
      { c : irreducibleComponents (PrimeSpectrum R) // p ∈ (c : Set (PrimeSpectrum R)) } :=
  (minimalPrimesEquivMinimalPrimesLe p p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) rfl).trans
    (irreducibleComponentsContainingEquivMinimalPrimesLe R p).symm

/-- The minimal primes of the stalk of a scheme at a point `x`
are in bijection with the irreducible components containing `x`. -/
private lemma
    nonempty_stalkMinimalPrimesEquivIrreducibleComponentsContaining
    {X : Scheme} (x : X.carrier) :
    Nonempty (minimalPrimes (X.presheaf.stalk x) ≃
      { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) }) := by
  let i := X.affineCover.idx x
  let f := X.affineCover.f i
  have hf : IsOpenEmbedding f.1.base := f.isOpenEmbedding
  have hCov := X.affineCover.covers x
  let y := Classical.choose hCov
  have hy : f.1.base y = x := Classical.choose_spec hCov
  have eStalk := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  let U := X.affineCover.X i
  have eStalkX : X.presheaf.stalk x ≃+* U.presheaf.stalk y := by
    rw [← hy]
    exact eStalk
  let hEq1 := minimalPrimes_equiv_of_ringEquiv eStalkX
  let R := Γ(U, ⊤)
  let g := U.isoSpec
  let eHomeo := Scheme.homeoOfIso g
  let y_spec : PrimeSpectrum R := g.hom.1.1.base y
  have eStalkSpecG := (asIso (g.hom.stalkMap y)).commRingCatIsoToRingEquiv.symm
  let eStalk2 := (Spec.stalkIso R y_spec).commRingCatIsoToRingEquiv
  let eStalkSpec := eStalkSpecG.trans eStalk2
  let hEq2 := minimalPrimes_equiv_of_ringEquiv eStalkSpec
  let hEq3 := stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec R y_spec
  have hYspec : eHomeo.symm y_spec = y := by
    -- `y_spec = eHomeo y` by `Scheme.homeoOfIso_apply`.
    have : eHomeo y = y_spec :=
      Scheme.homeoOfIso_apply g y
    exact eHomeo.symm_apply_eq.mpr this.symm
  have hEq4 : { c : irreducibleComponents (PrimeSpectrum R) //
      y_spec ∈ (c : Set (PrimeSpectrum R)) } ≃
      { c : irreducibleComponents U.carrier // y ∈ (c : Set U.carrier) } := by
    have := irreducibleComponents_containing_equiv_of_isOpenEmbedding
      eHomeo.symm.isOpenEmbedding y_spec
    rwa [hYspec] at this
  have hEq5 : { c : irreducibleComponents U.carrier // y ∈ (c : Set U.carrier) } ≃
      { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) } := by
    have := irreducibleComponents_containing_equiv_of_isOpenEmbedding hf y
    rwa [hy] at this
  exact ⟨hEq1.trans (hEq2.trans (hEq3.trans (hEq4.trans hEq5)))⟩

/-- If the stalk at `x` has a unique minimal prime, then
`x` belongs to a unique irreducible component. -/
private lemma existsUnique_irreducibleComponent_of_unique_minimalPrime
    {X : Scheme} (x : X.carrier)
    [Unique (minimalPrimes (X.presheaf.stalk x))] :
    ∃! c : irreducibleComponents X.carrier,
      x ∈ (c : Set X.carrier) := by
  have e_nonempty :=
    nonempty_stalkMinimalPrimesEquivIrreducibleComponentsContaining x
  exact e_nonempty.elim fun e => by
    haveI hU : Unique { c : irreducibleComponents X.carrier //
        x ∈ (c : Set X.carrier) } :=
      Equiv.unique e.symm
    exact ⟨hU.default.1, hU.default.2,
      fun c hc ↦ congrArg Subtype.val (hU.uniq ⟨c, hc⟩)⟩

/-- In a scheme whose stalks have unique minimal primes, the irreducible
components are pairwise disjoint. -/
private lemma disjoint_irreducibleComponents_of_unique_minimalPrime {Z : Scheme}
  (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x))) :
  ∀ c1 c2 : irreducibleComponents Z.carrier, c1 ≠ c2 →
    Disjoint (c1 : Set Z.carrier) (c2 : Set Z.carrier) := by
  intro c1 c2 hneq
  rw [Set.disjoint_iff]
  intro x hx
  have hx1 : x ∈ (c1 : Set Z.carrier) := hx.1
  have hx2 : x ∈ (c2 : Set Z.carrier) := hx.2
  have h_unique := existsUnique_irreducibleComponent_of_unique_minimalPrime x
  obtain ⟨c, _, hcUniq⟩ := h_unique
  have hEq1 : c1 = c := hcUniq c1 hx1
  have hEq2 : c2 = c := hcUniq c2 hx2
  rw [hEq1, hEq2] at hneq
  exact hneq rfl

/-- In a topological space with finitely many irreducible components, pairwise-disjoint
components are open. -/
private lemma isOpen_irreducibleComponents_of_pairwise_disjoint {α : Type*} [TopologicalSpace α]
    (hFinite : (irreducibleComponents α).Finite)
    (hDisj : ∀ c1 c2 : irreducibleComponents α, c1 ≠ c2 →
      Disjoint (c1 : Set α) (c2 : Set α))
    (c : irreducibleComponents α) : IsOpen (c : Set α) := by
  have hEq : (c : Set α) = (⋃ c' ∈ (irreducibleComponents α \ {c.val}), c')ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, mem_sdiff, mem_singleton_iff]
    constructor
    · intro hx
      rintro ⟨c', ⟨hc', hneq⟩, hxc'⟩
      have hDisj' := hDisj c ⟨c', hc'⟩ (fun heq => hneq (congrArg Subtype.val heq).symm)
      exact hDisj'.le_bot ⟨hx, hxc'⟩
    · intro hx
      have hUniv : x ∈ ⋃₀ (irreducibleComponents α) := by
        rw [sUnion_irreducibleComponents]
        exact mem_univ x
      rcases hUniv with ⟨c', hc'S, hxc'⟩
      by_contra hc
      apply hx
      refine ⟨c', ⟨hc'S, ?_⟩, hxc'⟩
      intro heq
      exact hc (heq ▸ hxc')
  rw [hEq]
  rw [isOpen_compl_iff]
  exact Set.Finite.isClosed_biUnion hFinite.sdiff
    (fun t ht => isClosed_of_mem_irreducibleComponents t ht.1)

/-- In an affine locally noetherian scheme whose stalks have unique minimal
primes, every irreducible component is open. -/
private theorem isOpen_irreducibleComponents_of_affine_unique_minimalPrime {X : Scheme.{u}}
    [IsAffine X]
    [IsLocallyNoetherian X] (hStalks : ∀ x : X.carrier, Unique (minimalPrimes (X.presheaf.stalk x)))
    (c : irreducibleComponents X.carrier) : IsOpen (c : Set X.carrier) := by
  haveI : NoetherianSpace X.carrier :=
    @noetherianSpace_of_isAffine X _
      (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩)
  apply isOpen_irreducibleComponents_of_pairwise_disjoint
    (NoetherianSpace.finite_irreducibleComponents (α := X.carrier))
  exact disjoint_irreducibleComponents_of_unique_minimalPrime hStalks

/-- In a locally noetherian scheme whose stalks have unique minimal primes,
every irreducible component is open. -/
private theorem isOpen_irreducibleComponents_of_unique_minimalPrime {Z : Scheme.{u}}
    [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x)))
    (c : irreducibleComponents Z.carrier) :
    IsOpen (c : Set Z.carrier) := by
  rw [isOpen_iff_of_cover (fun j ↦ (Z.affineCover.f j).isOpenEmbedding.isOpen_range)
    Z.affineCover.iUnion_range]
  intro j
  rw [inter_comm]
  let f := Z.affineCover.f j
  have hf : IsOpenEmbedding f.1.base := f.isOpenEmbedding
  rw [← image_preimage_eq_inter_range]
  apply hf.isOpenMap
  let Y := Z.affineCover.X j
  have hStalksY : ∀ y : Y.carrier, Unique (minimalPrimes (Y.presheaf.stalk y)) := by
    intro y
    haveI hU : Unique (minimalPrimes (Z.presheaf.stalk (f.1.base y))) := hStalks (f.1.base y)
    exact Equiv.unique (minimalPrimes_equiv_of_ringEquiv
      (asIso <| f.stalkMap y).commRingCatIsoToRingEquiv.symm)
  by_cases hEmpty : (f.1.base ⁻¹' (c : Set Z.carrier)).Nonempty
  · have hNonempty : ((c : Set Z.carrier) ∩ Set.range f.1.base).Nonempty := by
      obtain ⟨x, hx⟩ := hEmpty
      exact ⟨f.1.base x, hx, ⟨x, rfl⟩⟩
    have hComp : f.1.base ⁻¹' (c : Set Z.carrier) ∈ irreducibleComponents Y.carrier :=
      preimage_mem_irreducibleComponents c.property hf hNonempty
    have hOpen := isOpen_irreducibleComponents_of_affine_unique_minimalPrime hStalksY ⟨_, hComp⟩
    exact hOpen
  · rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    rw [hEmpty]
    exact isOpen_empty

/-- A connected topological space with open irreducible components is irreducible. -/
private lemma irreducibleSpace_of_connected_of_open_components {α : Type*} [TopologicalSpace α]
    [ConnectedSpace α] (hOpen : ∀ c : irreducibleComponents α, IsOpen (c : Set α)) :
    IrreducibleSpace α := by
  have hNonempty : Nonempty (irreducibleComponents α) := by
    have h_ne : Nonempty α := inferInstance
    obtain ⟨x⟩ := h_ne
    have hSU : x ∈ ⋃₀ irreducibleComponents α := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ x
    obtain ⟨c, hc_in, hx⟩ := hSU
    exact ⟨⟨c, hc_in⟩⟩
  obtain ⟨c⟩ := hNonempty
  have hcClopen : IsClopen (c : Set α) :=
    ⟨isClosed_of_mem_irreducibleComponents (c : Set α) c.2, hOpen c⟩
  have hcNonempty : (c : Set α).Nonempty := c.2.1.1
  have hcEqUniv : (c : Set α) = univ := IsClopen.eq_univ hcClopen hcNonempty
  have hIrredUniv : IsIrreducible (univ : Set α) := by
    rw [← hcEqUniv]
    exact c.2.1
  haveI : PreirreducibleSpace α := ⟨hIrredUniv.2⟩
  exact ⟨inferInstance⟩

/-- A locally noetherian connected scheme whose stalks have unique minimal
primes is irreducible. -/
theorem irreducibleSpace_of_connected_of_unique_minimalPrime_stalk (Z : Scheme.{u})
    [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x))) :
    IrreducibleSpace Z := by
  apply irreducibleSpace_of_connected_of_open_components
  intro c
  exact isOpen_irreducibleComponents_of_unique_minimalPrime hStalks c

/-- A locally noetherian connected scheme whose stalks are integral domains
is irreducible. -/
theorem irreducibleSpace_of_connected_of_isDomain_stalk (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
    IrreducibleSpace Z := by
  haveI hU : ∀ x, Unique (minimalPrimes (Z.presheaf.stalk x)) := fun x => by
    haveI := hStalks x
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.uniqueSingleton ⊥
  exact irreducibleSpace_of_connected_of_unique_minimalPrime_stalk Z hU

end AlgebraicGeometry

end TauCeti
