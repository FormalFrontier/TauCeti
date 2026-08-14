/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Components
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TypeA

public section

/-!
# Reindexing a simply-laced branch diagram onto a star

Deleting the unique branch vertex of a connected simply-laced finite-type diagram leaves three
path components. This file roots each path at the neighbour of the deleted vertex and joins the
three rooted paths back to their centre. The resulting simultaneous row-and-column relabelling
identifies the original matrix with `TauCeti.starCartanMatrix`.

The model-star classification then applies to an arbitrary simply-laced branch diagram, completing
the `D` and `E` branch of the finite-type Cartan-matrix classification.

## Main results

* `TauCeti.IsFiniteType.exists_equiv_starCartanMatrix_of_isSimplyLaced_of_degree_eq_three`:
  a connected simply-laced finite-type matrix with a branch vertex is a three-armed star.
* `TauCeti.IsFiniteType.existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three`: such a
  matrix carries a unique valid Dynkin type.
* `TauCeti.existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three`: the corresponding
  classification statement for the base of an irreducible root system.

## References

This is the reindexing step in the "classification of finite-type Cartan matrices" target of
Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, Section 11.4, and Bourbaki, *Lie Groups
and Lie Algebras, Chapters 4--6*, Chapter VI, Section 4.
-/

namespace TauCeti

open SimpleGraph

private def pathGraphRevIso (n : ℕ) : pathGraph n ≃g pathGraph n where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro i j
    simp only [pathGraph_adj, Fin.revPerm_apply, Fin.val_rev]
    omega

@[simp] private theorem pathGraphRevIso_apply (n : ℕ) (i : Fin n) :
    pathGraphRevIso n i = i.rev :=
  rfl

private theorem exists_iso_pathGraph_apply_eq_zero {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (u : V) (hu : G.degree u ≤ 1)
    (hiso : Nonempty (G ≃g pathGraph (Nat.card V))) :
    ∃ e : G ≃g pathGraph (Nat.card V), (e u : ℕ) = 0 := by
  classical
  obtain ⟨e⟩ := hiso
  have hcard : 0 < Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨u⟩
  have hend : (e u : ℕ) = 0 ∨ (e u : ℕ) + 1 = Nat.card V := by
    by_contra h
    push Not at h
    let a : Fin (Nat.card V) := ⟨(e u : ℕ) - 1, by omega⟩
    let b : Fin (Nat.card V) := ⟨(e u : ℕ) + 1, by omega⟩
    have ha : a ∈ (pathGraph (Nat.card V)).neighborFinset (e u) := by
      rw [mem_neighborFinset, pathGraph_adj]
      exact Or.inr (by simp only [a]; omega)
    have hb : b ∈ (pathGraph (Nat.card V)).neighborFinset (e u) := by
      rw [mem_neighborFinset, pathGraph_adj]
      exact Or.inl (by simp only [b])
    have hab : a ≠ b := by
      intro hab
      have := congrArg Fin.val hab
      simp only [a, b] at this
      omega
    have htwo : 1 < (pathGraph (Nat.card V)).degree (e u) := by
      rw [← card_neighborFinset_eq_degree, Finset.one_lt_card]
      exact ⟨a, ha, b, hb, hab⟩
    rw [e.degree_eq] at htwo
    omega
  rcases hend with hend | hend
  · exact ⟨e, hend⟩
  · refine ⟨e.trans (pathGraphRevIso _), ?_⟩
    simp only [RelIso.trans_apply, pathGraphRevIso_apply, Fin.val_rev]
    omega

private noncomputable def starArmsEquiv {B : Type*} (c : B)
    (G : SimpleGraph B)
    (e : Fin 3 ≃ (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : ∀ i, (e i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (e i)))) :
    ((i : Fin 3) × Fin (Nat.card ↑(ConnectedComponent.supp (e i)))) ≃ {x : B // x ≠ c} :=
  let H := G.induce ({c}ᶜ : Set B)
  (Equiv.sigmaCongrRight fun i ↦ (f i).toEquiv.symm).trans
    ((Equiv.sigmaCongrLeft e).trans
      ((Equiv.sigmaFiberEquiv H.connectedComponentMk).trans
        (Equiv.subtypeEquivRight fun _ ↦ Set.mem_compl_singleton_iff)))

@[simp] private theorem starArmsEquiv_apply {B : Type*} (c : B)
    (G : SimpleGraph B)
    (e : Fin 3 ≃ (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : ∀ i, (e i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (e i))))
    (v : (i : Fin 3) × Fin (Nat.card ↑(ConnectedComponent.supp (e i)))) :
    (starArmsEquiv c G e f v).1 = ((f v.1).symm v.2).1.1 :=
  rfl

private noncomputable def starVertexEquiv {B : Type*} (c : B)
    (G : SimpleGraph B)
    (e : Fin 3 ≃ (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : ∀ i, (e i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (e i)))) :
    StarIndex (fun i ↦ Nat.card ↑(ConnectedComponent.supp (e i))) ≃ B :=
  letI : DecidableEq B := Classical.decEq B
  (Equiv.optionCongr (starArmsEquiv c G e f)).trans (Equiv.optionSubtypeNe c)

private theorem starVertexEquiv_none {B : Type*} (c : B)
    (G : SimpleGraph B)
    (e : Fin 3 ≃ (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : ∀ i, (e i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (e i)))) :
    starVertexEquiv c G e f none = c := by
  classical
  dsimp only [starVertexEquiv]
  rw [Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_none, Equiv.optionSubtypeNe_none]

private theorem starVertexEquiv_some {B : Type*} (c : B)
    (G : SimpleGraph B)
    (e : Fin 3 ≃ (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : ∀ i, (e i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (e i))))
    (v : (i : Fin 3) × Fin (Nat.card ↑(ConnectedComponent.supp (e i)))) :
    starVertexEquiv c G e f (some v) = ((f v.1).symm v.2).1.1 := by
  classical
  dsimp only [starVertexEquiv]
  rw [Equiv.trans_apply, Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some,
    starArmsEquiv_apply]

@[simp] private theorem connectedComponent_toSimpleGraph_adj {V : Type*}
    {G : SimpleGraph V} {s : Set V} (C : (G.induce s).ConnectedComponent)
    (u v : ↑C.supp) :
    C.toSimpleGraph.Adj u v ↔ G.Adj u.1.1 v.1.1 :=
  (C.toSimpleGraph_adj u.2 v.2).trans induce_adj

private theorem degree_toSimpleGraph_le_one_of_adj_branch {B : Type*} [Fintype B]
    {G : SimpleGraph B} [DecidableRel G.Adj] (c : B) (hdeg : ∀ x, G.degree x ≤ 3)
    (huniq : ∀ {x}, G.degree x = 3 → x = c) {x : B} (hcx : G.Adj c x)
    (C : (G.induce ({c}ᶜ : Set B)).ConnectedComponent)
    [Fintype ↑C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (hxC : (G.induce ({c}ᶜ : Set B)).connectedComponentMk
      ⟨x, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj hcx).symm⟩ = C) :
    C.toSimpleGraph.degree
      ⟨⟨x, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj hcx).symm⟩, hxC⟩ ≤ 1 := by
  classical
  let q : ↑C.supp :=
    ⟨⟨x, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj hcx).symm⟩, hxC⟩
  have hdegq : C.toSimpleGraph.degree q ≤ 1 := by
    by_contra hq
    have htwo : 1 < C.toSimpleGraph.degree q := by omega
    rw [← card_neighborFinset_eq_degree, Finset.one_lt_card] at htwo
    obtain ⟨a, ha, b, hb, hab⟩ := htwo
    rw [mem_neighborFinset, connectedComponent_toSimpleGraph_adj] at ha hb
    have hxa : G.Adj x a.1.1 := ha
    have hxb : G.Adj x b.1.1 := hb
    have hc_mem : c ∈ G.neighborFinset x := by
      rw [mem_neighborFinset]
      exact hcx.symm
    have ha_mem : a.1.1 ∈ G.neighborFinset x := by simp [hxa]
    have hb_mem : b.1.1 ∈ G.neighborFinset x := by simp [hxb]
    have hca : c ≠ a.1.1 := fun hca ↦
      (Set.mem_compl_singleton_iff.mp a.1.property) hca.symm
    have hcb : c ≠ b.1.1 := fun hcb ↦
      (Set.mem_compl_singleton_iff.mp b.1.property) hcb.symm
    have hab' : a.1.1 ≠ b.1.1 := fun hab' ↦ hab (Subtype.ext (Subtype.ext hab'))
    have hthree : 2 < G.degree x := by
      rw [← card_neighborFinset_eq_degree, Finset.two_lt_card]
      exact ⟨c, hc_mem, a.1.1, ha_mem, b.1.1, hb_mem, hca, hcb, hab'⟩
    have hxle := hdeg x
    have hx3 : G.degree x = 3 := by omega
    exact (G.ne_of_adj hcx) (huniq hx3).symm
  exact hdegq

private theorem apply_eq_chainEntry_of_component_iso {B : Type*} [Fintype B]
    {A : Matrix B B ℤ} (h : IsFiniteType A) (hsl : A.IsSimplyLaced) {c : B}
    (C : ((diagramGraph A).induce ({c}ᶜ : Set B)).ConnectedComponent)
    (f : C.toSimpleGraph ≃g pathGraph (Nat.card ↑C.supp)) (v w : ↑C.supp) :
    A v.1.1 w.1.1 = chainEntry (f v) (f w) := by
  let A' : Matrix ↑C.supp ↑C.supp ℤ := fun x y ↦ A x.1.1 y.1.1
  have hdiag' : ∀ x : ↑C.supp, A' x x = 2 := fun x ↦ h.apply_self x.1.1
  have hsl' : A'.IsSimplyLaced := fun {x y} hxy ↦
    hsl fun heq ↦ hxy (Subtype.ext (Subtype.ext heq))
  have hadj' : ∀ x y : ↑C.supp, C.toSimpleGraph.Adj x y ↔ x ≠ y ∧ A' x y ≠ 0 := by
    intro x y
    rw [connectedComponent_toSimpleGraph_adj, h.diagramGraph_adj_iff]
    exact ⟨fun ⟨hne, hA⟩ ↦ ⟨fun heq ↦ hne (congrArg (fun z : ↑C.supp ↦ z.1.1) heq), hA⟩,
      fun ⟨hne, hA⟩ ↦ ⟨fun heq ↦ hne (Subtype.ext (Subtype.ext heq)), hA⟩⟩
  exact apply_eq_chainEntry_of_iso_pathGraph hdiag' hsl' hadj' f v w

namespace IsFiniteType

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B ℤ}

/-- **A connected simply-laced finite-type matrix with a branch vertex is a three-armed star.**

The arm lengths are the cardinalities of the three components left after deleting the branch
vertex. They are nonzero, and the equivalence sends the branch vertex to the centre and roots each
arm at its unique neighbour of the centre. -/
theorem exists_equiv_starCartanMatrix_of_isSimplyLaced_of_degree_eq_three
    (h : IsFiniteType A) (hconn : (diagramGraph A).Connected) (hsl : A.IsSimplyLaced)
    {c : B} (hc : (diagramGraph A).degree c = 3) :
    ∃ (ℓ : Fin 3 → ℕ) (e : B ≃ StarIndex ℓ),
      (∀ i, ℓ i ≠ 0) ∧ e c = none ∧ ∀ i j, A i j = starCartanMatrix ℓ (e i) (e j) := by
  classical
  let G := diagramGraph A
  let H := G.induce ({c}ᶜ : Set B)
  have htree : G.IsTree := h.isTree_diagramGraph hconn
  obtain ⟨eC, heC⟩ := h.exists_three_path_components_of_isSimplyLaced hconn hsl hc
  let _ : (C : H.ConnectedComponent) → Fintype ↑C.supp := fun _ ↦ Fintype.ofFinite _
  let _ : (C : H.ConnectedComponent) → DecidableRel C.toSimpleGraph.Adj :=
    fun _ ↦ Classical.decRel _
  let n (i : Fin 3) : ↑(G.neighborSet c) :=
    (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree c).symm (eC i)
  have hcn (i : Fin 3) : G.Adj c (n i) := (n i).property
  let x (i : Fin 3) : ↑({c}ᶜ : Set B) :=
    ⟨n i, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj (hcn i)).symm⟩
  have hxC (i : Fin 3) : H.connectedComponentMk (x i) = eC i := by
    calc
      H.connectedComponentMk (x i) =
          TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree c (n i) := by
        symm
        exact TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply htree c (n i)
      _ = eC i := Equiv.apply_symm_apply _ _
  let q (i : Fin 3) : ↑(ConnectedComponent.supp (eC i)) := ⟨x i, hxC i⟩
  have hqdeg (i : Fin 3) : (eC i).toSimpleGraph.degree (q i) ≤ 1 := by
    exact degree_toSimpleGraph_le_one_of_adj_branch c h.degree_le_three
      (fun hx3 ↦ h.eq_of_degree_eq_three hsl hconn hx3 hc) (hcn i) (eC i) (hxC i)
  let f (i : Fin 3) : (eC i).toSimpleGraph ≃g
      pathGraph (Nat.card ↑(ConnectedComponent.supp (eC i))) := by
    exact Classical.choose
      (exists_iso_pathGraph_apply_eq_zero (q i) (hqdeg i) (heC i))
  have hfq (i : Fin 3) : ((f i) (q i) : ℕ) = 0 := by
    dsimp only [f]
    exact Classical.choose_spec
      (exists_iso_pathGraph_apply_eq_zero (q i) (hqdeg i) (heC i))
  let ℓ : Fin 3 → ℕ := fun i ↦ Nat.card ↑(ConnectedComponent.supp (eC i))
  let E : StarIndex ℓ ≃ B := starVertexEquiv c G eC f
  have hcenter (i : Fin 3) (t : Fin (ℓ i)) :
      G.Adj c ((f i).symm t).1.1 ↔ (t : ℕ) = 0 := by
    constructor
    · intro hct
      let z : ↑(G.neighborSet c) := ⟨((f i).symm t).1.1, hct⟩
      have hzC : TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree c z = eC i := by
        rw [TauCeti.IsTree.neighborSetEquivConnectedComponentCompl_apply]
        exact ((f i).symm t).property
      have hzn : z = n i := by
        apply (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl htree c).injective
        rw [hzC]
        exact (Equiv.apply_symm_apply _ _).symm
      have hyq : (f i).symm t = q i := by
        have h1 : ((f i).symm t).1.1 = (q i).1.1 :=
          congrArg (α := ↑(G.neighborSet c)) Subtype.val hzn
        exact Subtype.ext (Subtype.ext h1)
      calc
        (t : ℕ) = ((f i) ((f i).symm t) : ℕ) := by rw [RelIso.apply_symm_apply]
        _ = ((f i) (q i) : ℕ) := congrArg Fin.val (congrArg (f i) hyq)
        _ = 0 := hfq i
    · intro ht
      have htq : t = (f i) (q i) := Fin.ext (ht.trans (hfq i).symm)
      have hyq : (f i).symm t = q i := by rw [htq, RelIso.symm_apply_apply]
      rw [hyq]
      exact hcn i
  have hdifferent {i j : Fin 3} (hij : i ≠ j)
      (v : ↑(ConnectedComponent.supp (eC i)))
      (w : ↑(ConnectedComponent.supp (eC j))) : A v.1.1 w.1.1 = 0 := by
    by_contra hA
    have hadjG : G.Adj v.1.1 w.1.1 := h.diagramGraph_adj_iff.mpr ⟨by
      intro hvw
      have hvwH : v.1 = w.1 := Subtype.ext hvw
      have hcomp : eC i = eC j :=
        v.property.symm.trans ((congrArg H.connectedComponentMk hvwH).trans w.property)
      exact hij (eC.injective hcomp), hA⟩
    have hadjH : H.Adj v.1 w.1 := induce_adj.mpr hadjG
    have hcomp := ConnectedComponent.connectedComponentMk_eq_of_adj hadjH
    have heq : eC i = eC j := v.property.symm.trans (hcomp.trans w.property)
    exact hij (eC.injective heq)
  refine ⟨ℓ, E.symm, ?_, E.symm_apply_eq.mpr (starVertexEquiv_none c G eC f), ?_⟩
  · intro i hzero
    have hpos : 0 < Nat.card ↑(ConnectedComponent.supp (eC i)) :=
      Nat.card_pos_iff.mpr ⟨⟨x i, hxC i⟩, inferInstance⟩
    apply hpos.ne'
    simpa only [ℓ] using hzero
  · intro i j
    obtain ⟨v, rfl⟩ := E.surjective i
    obtain ⟨w, rfl⟩ := E.surjective j
    simp only [E.symm_apply_apply]
    rcases v with _ | v <;> rcases w with _ | w
    · simp only [E, starVertexEquiv_none, h.apply_self, starCartanMatrix_none_none]
    · simp only [E, starVertexEquiv_none, starVertexEquiv_some,
        starCartanMatrix_none_some]
      by_cases hw : (w.2 : ℕ) = 0
      · rw [ite_eq_left hw]
        have hadj := (hcenter w.1 w.2).mpr hw
        have hneA : A c ((f w.1).symm w.2).1.1 ≠ 0 := by
          exact (h.diagramGraph_adj_iff.mp hadj).2
        exact (hsl (G.ne_of_adj hadj)).resolve_left hneA
      · rw [ite_eq_right hw]
        by_contra hA
        have hadj : G.Adj c ((f w.1).symm w.2).1.1 :=
          h.diagramGraph_adj_iff.mpr ⟨fun hcw ↦ ((f w.1).symm w.2).1.property
            (Set.mem_singleton_iff.mpr hcw.symm), hA⟩
        exact hw ((hcenter w.1 w.2).mp hadj)
    · simp only [E, starVertexEquiv_none, starVertexEquiv_some,
        starCartanMatrix_some_none]
      by_cases hv : (v.2 : ℕ) = 0
      · rw [ite_eq_left hv]
        have hadj := (hcenter v.1 v.2).mpr hv
        have hneA : A ((f v.1).symm v.2).1.1 c ≠ 0 := by
          exact (h.diagramGraph_adj_iff.mp hadj.symm).2
        exact (hsl (G.ne_of_adj hadj).symm).resolve_left hneA
      · rw [ite_eq_right hv]
        by_contra hA
        have hadj : G.Adj c ((f v.1).symm v.2).1.1 := by
          symm
          exact h.diagramGraph_adj_iff.mpr ⟨fun hvc ↦ ((f v.1).symm v.2).1.property
            (Set.mem_singleton_iff.mpr hvc), hA⟩
        exact hv ((hcenter v.1 v.2).mp hadj)
    · rcases v with ⟨i, v⟩
      rcases w with ⟨j, w⟩
      simp only [E, starVertexEquiv_some, starCartanMatrix_some_some]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl]
        simpa only [RelIso.apply_symm_apply, chainEntry_def] using
          apply_eq_chainEntry_of_component_iso h hsl (eC i) (f i) ((f i).symm v) ((f i).symm w)
      · rw [ite_eq_right hij]
        exact hdifferent hij ((f i).symm v) ((f j).symm w)

/-- **The simply-laced branch case of the finite-type Cartan-matrix classification.** A connected
simply-laced finite-type matrix with a vertex of degree three has exactly one valid Dynkin type.
It is consequently one of `Dₙ`, `E₆`, `E₇`, or `E₈`, as determined by the three arm lengths
in `TauCeti.IsFiniteType.existsUnique_dynkinType_of_star`. -/
theorem existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three
    (h : IsFiniteType A) (hconn : (diagramGraph A).Connected) (hsl : A.IsSimplyLaced)
    {c : B} (hc : (diagramGraph A).degree c = 3) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
  classical
  obtain ⟨ℓ, e, hℓ, -, he⟩ :=
    h.exists_equiv_starCartanMatrix_of_isSimplyLaced_of_degree_eq_three hconn hsl hc
  have hstar : IsFiniteType (starCartanMatrix ℓ) := by
    have hreindex : starCartanMatrix ℓ = A.submatrix e.symm e.symm := by
      ext v w
      rw [Matrix.submatrix_apply, he, e.apply_symm_apply, e.apply_symm_apply]
    rw [hreindex]
    exact h.submatrix e.symm.injective
  obtain ⟨t, htstar, -⟩ := hstar.existsUnique_dynkinType_of_star hℓ
  have ht := htstar.1
  obtain ⟨et, het⟩ := (starHasCartanType_iff ℓ t).mp htstar.2
  refine ⟨t, ⟨ht, e.trans et, fun i j ↦ (he i j).trans (het (e i) (e j))⟩, ?_⟩
  intro s hs
  exact DynkinType.eq_of_valid_of_forall_eq hs.1 ht hs.2.choose (e.trans et)
    hs.2.choose_spec (fun i j ↦ (he i j).trans (het (e i) (e j)))

end IsFiniteType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R] [DecidableEq ι]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **An irreducible simply-laced root system with a branch vertex has a unique valid Dynkin
type.** The type is `Dₙ`, `E₆`, `E₇`, or `E₈`, with the three arms of the branch diagram
determining which one. -/
theorem existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) {c : b.support}
    (hc : (diagramGraph b.cartanMatrix).degree c = 3) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t := by
  have : Nonempty ι := ⟨c.1⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_cartanMatrix b).existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three
      (connected_diagramGraph_cartanMatrix b) hsl hc
  exact ((hasCartanType_iff b t).mpr ⟨e, he⟩).existsUnique_of_valid ht

end RootPairing

end TauCeti
