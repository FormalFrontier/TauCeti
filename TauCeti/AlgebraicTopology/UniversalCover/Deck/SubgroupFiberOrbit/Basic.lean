/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Orbit
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Fibre orbits for subgroups of the deck group

This file packages the orbit quotient of a single fibre by a chosen subgroup
`H ≤ Deck p`. It is the fibre-level bookkeeping needed for the universal-covers roadmap when
the cover attached to a subgroup is compared with a pointed cover: changing the chosen lift in
one fibre is controlled by subgroup orbits, and later regular-cover statements compare these
orbits with normalizers and deck groups.

Mathlib already supplies the generic orbit quotient `MulAction.orbitRel.Quotient`; the
declarations here only specialize it to the deck action on a fibre and record the maps that
will be reused by the classification bookkeeping.

## Main declarations

* `TauCeti.Deck.SubgroupFiberOrbitQuotient`: the quotient of one fibre by a subgroup of the
  deck group.
* `TauCeti.Deck.subgroupFiberOrbitClass`: the quotient class of a fibre point.
* `TauCeti.Deck.subgroupFiberOrbitMapOfLE`: the map induced by an inclusion `H ≤ K`.
* `TauCeti.Deck.subgroupFiberOrbitQuotientEquiv`: transport of subgroup fibre-orbit quotients
  along an over-base homeomorphism.
* `TauCeti.Deck.subgroupFiberOrbitQuotientBotEquiv`: the quotient for `⊥ ≤ Deck p` is the
  original fibre.
* `TauCeti.Deck.subgroupFiberOrbitQuotientTopEquiv`: the quotient for `⊤ ≤ Deck p` is the
  existing full deck-orbit quotient.
* `TauCeti.Deck.subgroupFiberOrbitMapToFiberOrbit`: the map from an `H`-fibre quotient to
  the full deck-orbit quotient induced by `H ≤ ⊤`.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
items 7 and 8: covers associated to subgroups and the pointed/unpointed Galois
correspondence, where fibre orbits by subgroups and their transports are part of the
basepoint bookkeeping. It is the subgroup-level analogue of
`TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Orbit`, adapting that file's
`fiberOrbitClass`, `fiberOrbitQuotientEquiv`, and fibre transport/conjugation lemmas from the
full deck group to arbitrary subgroups.
-/

public section

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B} {b : B}

/-- The quotient of the fibre over `b` by the restricted action of a subgroup of the deck
group. -/
abbrev SubgroupFiberOrbitQuotient (H : Subgroup (Deck p)) (b : B) : Type _ :=
  MulAction.orbitRel.Quotient H (p ⁻¹' {b})

/-- The `H`-orbit class of a point in one fibre. -/
@[expose] def subgroupFiberOrbitClass (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b :=
  Quotient.mk'' e

/-- The subgroup fibre-orbit quotient map sends a fibre point to its own class. -/
lemma subgroupFiberOrbitClass_eq_mk (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitClass H e =
      (Quotient.mk'' e : SubgroupFiberOrbitQuotient H b) :=
  rfl

/-- Two fibre points have the same `H`-orbit class exactly when they lie in the same
`H`-orbit. The orientation follows `MulAction.orbitRel_apply`: the left point is in the orbit
of the right point. -/
lemma subgroupFiberOrbitClass_eq_iff (H : Subgroup (Deck p)) (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass H e = subgroupFiberOrbitClass H e' ↔ e ∈ MulAction.orbit H e' := by
  rw [subgroupFiberOrbitClass_eq_mk, subgroupFiberOrbitClass_eq_mk, Quotient.eq'',
    MulAction.orbitRel_apply]

/-- A deck translate of the chosen fibre point has the same subgroup orbit class as the chosen
point exactly when the translating deck transformation lies in the subgroup. -/
lemma subgroupFiberOrbitClass_smul_eq_base_iff
    [IsCancelSMul (Deck p) (p ⁻¹' {b})] (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H e ↔ φ ∈ H := by
  exact TauCeti.MulAction.orbitRelQuotient_smul_eq_base_iff
    (G := Deck p) (X := p ⁻¹' {b}) H φ e

/-- For a preconnected covering, a deck translate of the chosen fibre point has the same
subgroup orbit class as the chosen point exactly when the translating deck transformation lies
in the subgroup. -/
lemma subgroupFiberOrbitClass_smul_eq_base_iff_of_isCoveringMap
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H e ↔ φ ∈ H := by
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_smul_eq_base_iff H e φ

/-- If `H ≤ K`, the quotient of a fibre by `H` maps naturally to the quotient by `K`. -/
@[expose] def subgroupFiberOrbitMapOfLE {H K : Subgroup (Deck p)} (hHK : H ≤ K) :
    SubgroupFiberOrbitQuotient H b → SubgroupFiberOrbitQuotient K b :=
  Setoid.map_of_le
    (TauCeti.MulAction.orbitRel_le_of_subgroup_le (G := Deck p) (X := p ⁻¹' {b}) hHK)

/-- The map induced by `H ≤ K` sends the `H`-class of a point to its `K`-class. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_apply {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitMapOfLE (b := b) hHK (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass K e :=
  rfl

/-- The map induced by the identity inclusion is the identity on the subgroup fibre-orbit
quotient. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_refl (H : Subgroup (Deck p)) :
    subgroupFiberOrbitMapOfLE (b := b) (le_rfl : H ≤ H) =
      id := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- The maps induced by subgroup inclusions compose as expected. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_comp {H K L : Subgroup (Deck p)} (hHK : H ≤ K) (hKL : K ≤ L) :
    (subgroupFiberOrbitMapOfLE (b := b) hKL) ∘
        subgroupFiberOrbitMapOfLE (b := b) hHK =
      subgroupFiberOrbitMapOfLE (b := b) (hHK.trans hKL) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- A subgroup fibre-orbit quotient is subsingleton exactly when that subgroup acts
transitively on the fibre. -/
lemma subgroupFiberOrbitQuotient_subsingleton_iff (H : Subgroup (Deck p)) :
    Subsingleton (SubgroupFiberOrbitQuotient H b) ↔
      MulAction.IsPretransitive H (p ⁻¹' {b}) := by
  exact (MulAction.pretransitive_iff_subsingleton_quotient H (p ⁻¹' {b})).symm

/-- If the full deck group acts transitively on a fibre, then the quotient of that fibre by
the full deck subgroup is a subsingleton. -/
lemma subsingleton_subgroupFiberOrbitQuotient_top [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] :
    Subsingleton (SubgroupFiberOrbitQuotient (⊤ : Subgroup (Deck p)) b) := by
  rw [subgroupFiberOrbitQuotient_subsingleton_iff]
  refine MulAction.IsPretransitive.mk ?_
  intro e e'
  rcases MulAction.exists_smul_eq (Deck p) e e' with ⟨φ, hφ⟩
  exact ⟨⟨φ, trivial⟩, by simpa [Subgroup.smul_def] using hφ⟩

/-- For a regular cover, the quotient of a fibre by the full deck subgroup is a
subsingleton. -/
lemma subsingleton_regularSubgroupFiberOrbitQuotient_top (hreg : IsRegular p) :
    Subsingleton (SubgroupFiberOrbitQuotient (⊤ : Subgroup (Deck p)) b) := by
  letI := hreg.fiber_isPretransitive b
  exact subsingleton_subgroupFiberOrbitQuotient_top

/-- Transporting a point in an `H`-orbit along an over-base homeomorphism puts the transported
point in the orbit for the conjugated subgroup. -/
lemma fiberMap_mem_orbit_subgroup_map (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) {e e' : p ⁻¹' {b}} (hee' : e ∈ MulAction.orbit H e') :
    fiberMap h hpq b e ∈
      MulAction.orbit (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (fiberMap h hpq b e') := by
  rcases hee' with ⟨φ, hφ⟩
  refine ⟨⟨conjMulEquiv h hpq φ.1, ⟨φ.1, φ.2, rfl⟩⟩, ?_⟩
  rw [← hφ]
  exact (fiberMap_smul h hpq φ.1 e').symm

/-- Membership in a subgroup fibre-orbit is preserved by an over-base homeomorphism, with the
subgroup conjugated along the induced deck-group isomorphism. -/
lemma mem_orbit_fiberMap_subgroup_map_iff (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (e e' : p ⁻¹' {b}) :
    fiberMap h hpq b e ∈
        MulAction.orbit (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
          (fiberMap h hpq b e') ↔
      e ∈ MulAction.orbit H e' := by
  constructor
  · rintro ⟨ψ, hψ⟩
    rcases ψ.2 with ⟨φ, hφH, hφψ⟩
    refine ⟨⟨φ, hφH⟩, ?_⟩
    apply (fiberMap h hpq b).injective
    have hψ' : (ψ.1 : Deck q) • fiberMap h hpq b e' = fiberMap h hpq b e := by
      simpa [Subgroup.smul_def] using hψ
    have hφ' : (conjMulEquiv h hpq φ) • fiberMap h hpq b e' =
        fiberMap h hpq b e := by
      exact (congrArg (fun η : Deck q => η • fiberMap h hpq b e') hφψ).trans hψ'
    simp only [Subgroup.smul_def, fiberMap_smul]
    exact hφ'
  · exact fiberMap_mem_orbit_subgroup_map h hpq H

/-- An over-base homeomorphism identifies subgroup fibre-orbit quotients, conjugating the
subgroup of deck transformations along the induced deck-group isomorphism. -/
@[expose] def subgroupFiberOrbitQuotientEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (b : B) :
    SubgroupFiberOrbitQuotient H b ≃
      SubgroupFiberOrbitQuotient
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) b :=
  Quotient.congr (fiberMap h hpq b).toEquiv fun e e' => by
    rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
    exact (mem_orbit_fiberMap_subgroup_map_iff h hpq H e e').symm

/-- The transported equivalence on subgroup fibre-orbit quotients sends a class to the class
of the transported fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquiv_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquiv h hpq H b (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (fiberMap h hpq b e) :=
  rfl

/-- The inverse transported equivalence sends a target class to the class of its inverse
transport. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquiv_symm_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (f : q ⁻¹' {b}) : (subgroupFiberOrbitQuotientEquiv h hpq H b).symm
        (subgroupFiberOrbitClass
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) f) =
      subgroupFiberOrbitClass H ((fiberMap h hpq b).symm f) := by
  simp only [subgroupFiberOrbitQuotientEquiv, subgroupFiberOrbitClass_eq_mk]
  exact congrArg Quotient.mk''
    (congrArg (fun g : q ⁻¹' {b} ≃ₜ p ⁻¹' {b} => g f)
      (fiberMap_symm (h := h) (hpq := hpq) (b := b))).symm

/-- Casting subgroup fibre-orbit quotients along an equality of subgroups carries the class of
a point to the corresponding class for the target subgroup. -/
lemma cast_subgroupFiberOrbitClass {H K : Subgroup (Deck p)} (hHK : H = K) (e : p ⁻¹' {b}) :
    Equiv.cast (congrArg (fun H' => SubgroupFiberOrbitQuotient H' b) hHK)
        (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass K e := by
  subst hHK
  rfl

/-- The identity over-base homeomorphism induces the identity on subgroup fibre-orbit
quotients, up to the canonical rewrite identifying the image of a subgroup under the identity
conjugation with the original subgroup. -/
-- The compatibility argument is written `by change p e = p e; rfl` rather than `rfl`: a bare
-- `rfl` elaborates at `p ((Homeomorph.refl E) e) = p ((Homeomorph.refl E) e)`, and the rewrite by
-- `subgroupFiberOrbitQuotientEquiv_apply` in the proof below then no longer matches.
@[simp]
lemma subgroupFiberOrbitQuotientEquiv_refl (H : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) :
    cast (congrArg (fun H' => SubgroupFiberOrbitQuotient H' b)
        (subgroup_map_conj_refl (p := p) H))
      (subgroupFiberOrbitQuotientEquiv (Homeomorph.refl E) (p := p) (q := p)
        (fun e => by change p e = p e; rfl) H b x) =
      x := by
  rw [← Equiv.cast_apply]
  refine Quotient.inductionOn' x ?_
  intro e
  -- Quotient induction exposes the representative as `Quotient.mk''`; rewrite that
  -- definitional representative to the local class API before applying transport lemmas.
  change
    Equiv.cast (congrArg (fun H' => SubgroupFiberOrbitQuotient H' b)
        (subgroup_map_conj_refl (p := p) H))
      (subgroupFiberOrbitQuotientEquiv (Homeomorph.refl E) (p := p) (q := p)
        (fun e => by change p e = p e; rfl) H b (subgroupFiberOrbitClass H e)) =
      subgroupFiberOrbitClass H e
  rw [subgroupFiberOrbitQuotientEquiv_apply, fiberMap_refl]
  exact cast_subgroupFiberOrbitClass (subgroup_map_conj_refl (p := p) H) e

/-- Subgroup fibre-orbit quotient equivalences compose as the underlying over-base
homeomorphisms compose, with subgroup maps rewritten along conjugation composition. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquiv_trans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) (H : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitQuotientEquiv (h.trans k)
        (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) H b x =
      Equiv.cast (congrArg (fun H' => SubgroupFiberOrbitQuotient H' b)
        (subgroup_map_conj_trans h k hpq hqr H))
        (subgroupFiberOrbitQuotientEquiv k hqr
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) b
          (subgroupFiberOrbitQuotientEquiv h hpq H b x)) := by
  refine Quotient.inductionOn' x ?_
  intro e
  -- Quotient induction exposes the representative as `Quotient.mk''`; rewrite that
  -- definitional representative to the local class API before applying transport lemmas.
  change
    subgroupFiberOrbitQuotientEquiv (h.trans k)
        (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) H b
        (subgroupFiberOrbitClass H e) =
      Equiv.cast (congrArg (fun H' => SubgroupFiberOrbitQuotient H' b)
        (subgroup_map_conj_trans h k hpq hqr H))
        (subgroupFiberOrbitQuotientEquiv k hqr
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) b
          (subgroupFiberOrbitQuotientEquiv h hpq H b (subgroupFiberOrbitClass H e)))
  rw [subgroupFiberOrbitQuotientEquiv_apply, subgroupFiberOrbitQuotientEquiv_apply,
    subgroupFiberOrbitQuotientEquiv_apply]
  rw [← fiberMap_trans (h := h) (k := k) (p := p) (q := q) (r := r)
    (hpq := hpq) (hqr := hqr) (b := b)]
  exact (cast_subgroupFiberOrbitClass (subgroup_map_conj_trans h k hpq hqr H)
    (fiberMap k hqr b (fiberMap h hpq b e))).symm

/-- Transport of subgroup fibre-orbit quotients is natural with respect to maps induced by
subgroup inclusions. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquiv_mapOfLE (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) : (subgroupFiberOrbitQuotientEquiv h hpq K b) ∘
        subgroupFiberOrbitMapOfLE (b := b) hHK =
      subgroupFiberOrbitMapOfLE (b := b) (Subgroup.map_mono
        (f := ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) hHK) ∘
        subgroupFiberOrbitQuotientEquiv h hpq H b := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- Quotienting a fibre by the trivial deck subgroup gives the fibre itself. -/
noncomputable def subgroupFiberOrbitQuotientBotEquiv :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b ≃ p ⁻¹' {b} :=
  TauCeti.MulAction.orbitRelQuotientBotEquiv (G := Deck p) (X := p ⁻¹' {b})

/-- The bottom-subgroup quotient equivalence sends a class to its representative fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquiv_apply (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientBotEquiv
        (p := p) (b := b) (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e) = e :=
  TauCeti.MulAction.orbitRelQuotientBotEquiv_mk (G := Deck p) (X := p ⁻¹' {b}) e

/-- The inverse bottom-subgroup quotient equivalence sends a fibre point to its quotient
class. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquiv_symm_apply (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm e =
      subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e :=
  TauCeti.MulAction.orbitRelQuotientBotEquiv_symm_apply
    (G := Deck p) (X := p ⁻¹' {b}) e

/-- Equality of bottom-subgroup fibre-orbit classes is equality of fibre points. -/
lemma subgroupFiberOrbitClass_bot_eq_iff (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e' ↔
      e = e' := by
  exact TauCeti.MulAction.orbitRelQuotientBot_mk_eq_iff
    (G := Deck p) (X := p ⁻¹' {b}) e e'

/-- The quotient map induced by `⊥ ≤ H`, after identifying the bottom quotient with the
fibre, is the `H`-orbit class map. -/
lemma subgroupFiberOrbitMapOfLE_bot_apply (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitMapOfLE (b := b) (bot_le : (⊥ : Subgroup (Deck p)) ≤ H)
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm e) =
      subgroupFiberOrbitClass H e :=
  by rw [subgroupFiberOrbitQuotientBotEquiv_symm_apply, subgroupFiberOrbitMapOfLE_apply]

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_bot_eq (H : Subgroup (Deck p)) :
    subgroupFiberOrbitMapOfLE (p := p) (b := b)
        (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) =
      (fun e => subgroupFiberOrbitClass H e) ∘
        subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) := by
  exact TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq
    (G := Deck p) (X := p ⁻¹' {b}) H

/-- Equality in an `H`-fibre quotient can be checked after choosing representatives through
the bottom quotient. -/
lemma subgroupFiberOrbitMapOfLE_bot_eq_iff (H : Subgroup (Deck p))
    (x y : SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b) :
    subgroupFiberOrbitMapOfLE (p := p) (b := b)
        (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) x =
        subgroupFiberOrbitMapOfLE (p := p) (b := b)
          (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) y ↔
      subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) x ∈
        _root_.MulAction.orbit H (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) y) := by
  exact TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq_iff
    (G := Deck p) (X := p ⁻¹' {b}) H x y

/-- The quotient by the full deck group is the previously defined deck fibre-orbit quotient. -/
@[expose] def subgroupFiberOrbitQuotientTopEquiv :
    SubgroupFiberOrbitQuotient (⊤ : Subgroup (Deck p)) b ≃ FiberOrbitQuotient p b :=
  Quotient.congr (Equiv.refl (p ⁻¹' {b})) fun e e' => by
    rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.1, hφ⟩
    · rintro ⟨φ, hφ⟩
      exact ⟨⟨φ, trivial⟩, hφ⟩

/-- The top-subgroup quotient equivalence sends a class to the full deck-orbit class of the
same fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientTopEquiv_apply (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientTopEquiv
        (p := p) (b := b) (subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e) =
      fiberOrbitClass e :=
  rfl

/-- The inverse top-subgroup quotient equivalence sends a full deck-orbit class to the class
for the top subgroup. -/
@[simp]
lemma subgroupFiberOrbitQuotientTopEquiv_symm_apply (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)).symm (fiberOrbitClass e) =
      subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e :=
  rfl

/-- The map from the quotient of one fibre by `H` to the full deck-orbit quotient, induced
by the subgroup inclusion `H ≤ ⊤`. -/
@[expose] def subgroupFiberOrbitMapToFiberOrbit (H : Subgroup (Deck p)) :
    SubgroupFiberOrbitQuotient H b → FiberOrbitQuotient p b :=
  subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) ∘
    subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p)))

/-- Forgetting from `H`-orbits to full deck orbits sends a class to the full orbit class of
the same fibre point. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_apply (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitMapToFiberOrbit H (subgroupFiberOrbitClass H e) =
      fiberOrbitClass e :=
  rfl

/-- For `H = ⊤`, forgetting from `H`-orbits to full deck orbits is the top-subgroup
identification already supplied by `subgroupFiberOrbitQuotientTopEquiv`. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_top :
    subgroupFiberOrbitMapToFiberOrbit (p := p) (b := b) (⊤ : Subgroup (Deck p)) =
      subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- The top-subgroup equivalence identifies equality of top-subgroup classes with equality
of the corresponding full deck-orbit classes. -/
@[simp]
lemma subgroupFiberOrbitClass_top_eq_iff (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e' ↔
      fiberOrbitClass e = fiberOrbitClass e' := by
  constructor
  · intro h
    exact congrArg (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)) h
  · intro h
    exact congrArg (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)).symm h

/-- Equality of top-subgroup fibre-orbit classes is membership in a full deck orbit. -/
lemma subgroupFiberOrbitClass_top_eq_iff_mem_orbit (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e' ↔
      e ∈ MulAction.orbit (Deck p) e' := by
  rw [subgroupFiberOrbitClass_top_eq_iff, fiberOrbitClass_eq_iff]

/-- The map induced by `H ≤ ⊤`, after identifying the top quotient with the full deck-orbit
quotient, is `subgroupFiberOrbitMapToFiberOrbit`. -/
@[simp]
lemma subgroupFiberOrbitQuotientTopEquiv_mapOfLE (H : Subgroup (Deck p)) :
    subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) ∘
        subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p))) =
      subgroupFiberOrbitMapToFiberOrbit (p := p) (b := b) H :=
  rfl

/-- Equality after mapping two subgroup fibre-orbit representatives into a common
supergroup quotient is exactly membership in the common supergroup orbit. -/
lemma subgroupFiberOrbitMapOfLE_apply_eq_iff {H K L : Subgroup (Deck p)}
    (hHL : H ≤ L) (hKL : K ≤ L) (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitMapOfLE (b := b) hHL (subgroupFiberOrbitClass H e) =
        subgroupFiberOrbitMapOfLE (b := b) hKL (subgroupFiberOrbitClass K e') ↔
      e ∈ MulAction.orbit L e' := by
  rw [subgroupFiberOrbitMapOfLE_apply, subgroupFiberOrbitMapOfLE_apply,
    subgroupFiberOrbitClass_eq_iff]

/-- Equality after mapping two subgroup fibre quotients into a common supergroup quotient
can be checked on representatives from the common supergroup orbit. -/
lemma subgroupFiberOrbitMapOfLE_eq_iff {H K L : Subgroup (Deck p)} (hHL : H ≤ L) (hKL : K ≤ L)
    (x : SubgroupFiberOrbitQuotient H b) (y : SubgroupFiberOrbitQuotient K b) :
    subgroupFiberOrbitMapOfLE (b := b) hHL x = subgroupFiberOrbitMapOfLE (b := b) hKL y ↔
      ∃ e e' : p ⁻¹' {b}, x = subgroupFiberOrbitClass H e ∧
        y = subgroupFiberOrbitClass K e' ∧ e ∈ MulAction.orbit L e' := by
  refine Quotient.inductionOn' x ?_
  intro e
  refine Quotient.inductionOn' y ?_
  intro e'
  constructor
  · intro hxy
    refine ⟨e, e', rfl, rfl, ?_⟩
    exact (subgroupFiberOrbitMapOfLE_apply_eq_iff hHL hKL e e').mp hxy
  · rintro ⟨e, e', hx, hy, hee'⟩
    rw [hx, hy]
    exact (subgroupFiberOrbitMapOfLE_apply_eq_iff hHL hKL e e').mpr hee'

/-- Equality after forgetting from `H`-orbits to full deck orbits is exactly membership of
representatives in the same full deck orbit. -/
lemma subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff (H K : Subgroup (Deck p)) (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitMapToFiberOrbit H (subgroupFiberOrbitClass H e) =
        subgroupFiberOrbitMapToFiberOrbit K (subgroupFiberOrbitClass K e') ↔
      e ∈ MulAction.orbit (Deck p) e' := by
  constructor
  · intro h
    have htop :
        subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p)))
            (subgroupFiberOrbitClass H e) =
          subgroupFiberOrbitMapOfLE (b := b) (le_top : K ≤ (⊤ : Subgroup (Deck p)))
            (subgroupFiberOrbitClass K e') := by
      apply (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)).injective
      simpa [subgroupFiberOrbitMapToFiberOrbit] using h
    have htop_orbit :
        e ∈ MulAction.orbit (⊤ : Subgroup (Deck p)) e' :=
      (subgroupFiberOrbitMapOfLE_apply_eq_iff
        (b := b) (L := (⊤ : Subgroup (Deck p))) (le_top : H ≤ _) (le_top : K ≤ _) e e').mp
        htop
    exact (subgroupFiberOrbitClass_top_eq_iff_mem_orbit (p := p) (b := b) e e').mp
      ((subgroupFiberOrbitClass_eq_iff (p := p) (b := b) (⊤ : Subgroup (Deck p)) e e').mpr
        htop_orbit)
  · intro h
    have htop_orbit :
        e ∈ MulAction.orbit (⊤ : Subgroup (Deck p)) e' :=
      (subgroupFiberOrbitClass_eq_iff (p := p) (b := b) (⊤ : Subgroup (Deck p)) e e').mp
        ((subgroupFiberOrbitClass_top_eq_iff_mem_orbit (p := p) (b := b) e e').mpr h)
    have htop :
        subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p)))
            (subgroupFiberOrbitClass H e) =
          subgroupFiberOrbitMapOfLE (b := b) (le_top : K ≤ (⊤ : Subgroup (Deck p)))
            (subgroupFiberOrbitClass K e') :=
      (subgroupFiberOrbitMapOfLE_apply_eq_iff
        (b := b) (L := (⊤ : Subgroup (Deck p))) (le_top : H ≤ _) (le_top : K ≤ _) e e').mpr
        htop_orbit
    simpa [subgroupFiberOrbitMapToFiberOrbit] using
      congrArg (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)) htop

/-- Equality after forgetting from subgroup fibre quotients to full deck orbits can be
checked on representatives, even when the two subgroup quotients come from different
subgroups. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq_iff (H K : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) (y : SubgroupFiberOrbitQuotient K b) :
    subgroupFiberOrbitMapToFiberOrbit H x = subgroupFiberOrbitMapToFiberOrbit K y ↔
      ∃ e e' : p ⁻¹' {b}, x = subgroupFiberOrbitClass H e ∧
        y = subgroupFiberOrbitClass K e' ∧ e ∈ MulAction.orbit (Deck p) e' := by
  refine Quotient.inductionOn' x ?_
  intro e
  refine Quotient.inductionOn' y ?_
  intro e'
  constructor
  · intro hxy
    refine ⟨e, e', rfl, rfl, ?_⟩
    exact (subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff H K e e').mp hxy
  · rintro ⟨e, e', hx, hy, hee'⟩
    rw [hx, hy]
    exact (subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff H K e e').mpr hee'

/-- If `H ≤ K`, forgetting `H`-orbits to full deck orbits factors through the `K`-orbit
quotient. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_mapOfLE {H K : Subgroup (Deck p)} (hHK : H ≤ K)
    (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit K (subgroupFiberOrbitMapOfLE (b := b) hHK x) =
      subgroupFiberOrbitMapToFiberOrbit H x := by
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- If the full deck-orbit quotient of a fibre is a subsingleton, every `H`-fibre orbit maps
to the same full deck-orbit class as any chosen point of the fibre. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq [Subsingleton (FiberOrbitQuotient p b)]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit H x = fiberOrbitClass e :=
  Subsingleton.elim _ _

/-- If the full deck-orbit quotient of a fibre is a subsingleton, forgetting any two
subgroup fibre-orbit classes to full deck orbits gives the same result. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq_subgroupFiberOrbitMapToFiberOrbit
    [Subsingleton (FiberOrbitQuotient p b)] (H K : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) (y : SubgroupFiberOrbitQuotient K b) :
    subgroupFiberOrbitMapToFiberOrbit H x = subgroupFiberOrbitMapToFiberOrbit K y :=
  Subsingleton.elim _ _

namespace IsRegular

/-- For a regular deck action, every `H`-fibre orbit maps to the same full deck-orbit class
as any chosen point of the fibre. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq (hreg : IsRegular p) (H : Subgroup (Deck p))
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit H x = fiberOrbitClass e := by
  letI : Subsingleton (FiberOrbitQuotient p b) := hreg.subsingleton_fiberOrbitQuotient b
  exact Deck.subgroupFiberOrbitMapToFiberOrbit_eq H e x

/-- For a regular deck action, forgetting any two subgroup fibre-orbit classes to full deck
orbits gives the same result. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq_subgroupFiberOrbitMapToFiberOrbit
    (hreg : IsRegular p) (H K : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) (y : SubgroupFiberOrbitQuotient K b) :
    subgroupFiberOrbitMapToFiberOrbit H x = subgroupFiberOrbitMapToFiberOrbit K y := by
  letI : Subsingleton (FiberOrbitQuotient p b) := hreg.subsingleton_fiberOrbitQuotient b
  exact Deck.subgroupFiberOrbitMapToFiberOrbit_eq_subgroupFiberOrbitMapToFiberOrbit H K x y

end IsRegular

end Deck

end TauCeti
