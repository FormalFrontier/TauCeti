/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Sym.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The symmetric power of a topological space

The `n`-th symmetric power `Sym α n` of a type is the type of unordered `n`-tuples of points of
`α`. It is the quotient of the space `Fin n → α` of ordered tuples by the permutation action, and
this file gives it the corresponding quotient topology, together with the API that a quotient
topology is used through: the quotient map is continuous, and a map out of `Sym α n` is continuous
exactly when its composition with the quotient map is.

The quotient map is `TauCeti.Sym.ofFn`, which reads an ordered tuple as an unordered one. It is
Mathlib's quotient map `Sym.ofVector` composed with `List.Vector.ofFn`; the `Fin n → α` form is the
one that carries a product topology, so it is what the quotient topology is defined against.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.Sym.instTopologicalSpace`: the quotient topology on `Sym α n`, coinduced along `ofFn`.
* `TauCeti.Sym.isQuotientMap_ofFn`, `TauCeti.Sym.continuous_ofFn` and
  `TauCeti.Sym.continuous_iff_comp_ofFn`: the resulting quotient-map API.
* `TauCeti.Sym.isOpenMap_ofFn` and `TauCeti.Sym.isClosedMap_ofFn`: the quotient map is open and
  closed, the permutation group being finite.
* `TauCeti.Sym.instCompactSpace` and `TauCeti.Sym.instT2Space`: the symmetric power of a compact
  space is compact, and that of a Hausdorff space is Hausdorff.

Lane F4.1 of the analytic Heegaard Floer roadmap needs `Sym^g(Σ)` as a space before it can be
given a complex structure; this file supplies the underlying topology, and
`TauCeti/Analysis/Polynomial/SymmetricPower.lean` identifies it, over an algebraically closed
normed field, with affine space through the elementary symmetric functions.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α β : Type*} {n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; it is the map
that `Sym α n` carries the quotient topology along. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

/-- The multiset underlying `ofFn f` is the list of values of `f`. -/
@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

/-- The points of `ofFn f` are exactly the values of `f`. -/
@[simp]
theorem mem_ofFn {a : α} {f : Fin n → α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  rw [← _root_.Sym.mem_coe, coe_ofFn]
  simp

/-- Every unordered `n`-tuple is the image of an ordered one: `ofFn` is the quotient map
presenting `Sym α n` as a quotient of `Fin n → α`. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  have hlen : l.length = n := by simpa using hs
  subst hlen
  exact ⟨l.get, Subtype.ext (by simp)⟩

/-- Prepending a point to an ordered tuple adjoins it to the unordered one. -/
@[simp]
theorem ofFn_cons (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a ::ₛ ofFn f :=
  Subtype.ext <| by simp [Sym.coe_cons, List.ofFn_succ]

/-! ### The fibres of the quotient map -/

/-- Reindexing an ordered tuple by a permutation leaves the underlying unordered tuple unchanged. -/
theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

/-- Two ordered tuples have the same underlying unordered tuple exactly when one is a reindexing
of the other: the fibres of `ofFn` are the orbits of the permutation action. -/
theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · -- the two tuples take each value the same number of times, so their fibres are equinumerous
    have key : ∀ (u : Fin n → α) (c : α),
        Fintype.card {i // u i = c} = Multiset.count c (↑(List.ofFn u) : Multiset α) := by
      intro u c
      have hmap : (↑(List.ofFn u) : Multiset α) = Multiset.map u Finset.univ.val := by
        rw [List.ofFn_eq_map]; rfl
      rw [Fintype.card_subtype, hmap, Multiset.count_map, ← Finset.filter_val, Finset.card_def]
      simp [eq_comm]
    have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
      rw [key, key, ← coe_ofFn, ← coe_ofFn, h]
    exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
      funext fun i => Equiv.ofFiberEquiv_map _ i⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFn_comp_perm σ f).symm

/-- The saturation of a set of ordered tuples under `ofFn` is the union of its reindexings. -/
theorem preimage_image_ofFn (s : Set (Fin n → α)) :
    ofFn ⁻¹' (ofFn '' s) = ⋃ σ : Equiv.Perm (Fin n), (· ∘ σ) ⁻¹' s := by
  ext g
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨f, hf, hfg⟩
    obtain ⟨σ, rfl⟩ := ofFn_eq_ofFn_iff.1 hfg
    exact ⟨σ.symm, by simpa [Function.comp_assoc] using hf⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨g ∘ σ, hσ, ofFn_comp_perm σ g⟩

/-! ### The quotient topology -/

variable [TopologicalSpace α] [TopologicalSpace β]

/-- The `n`-th symmetric power of a topological space carries the quotient topology of the
permutation action on ordered `n`-tuples, presented as the topology coinduced along
`TauCeti.Sym.ofFn`. -/
instance instTopologicalSpace : TopologicalSpace (Sym α n) :=
  .coinduced ofFn inferInstance

/-- The quotient map onto the symmetric power is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofFn : Continuous (ofFn : (Fin n → α) → Sym α n) :=
  continuous_coinduced_rng

/-- `ofFn` presents `Sym α n` as a topological quotient of `Fin n → α`. -/
theorem isQuotientMap_ofFn : IsQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  ⟨⟨rfl⟩, ofFn_surjective⟩

/-- A map out of a symmetric power is continuous exactly when the associated map on ordered
tuples is; this is the universal property of the quotient topology. -/
theorem continuous_iff_comp_ofFn {g : Sym α n → β} : Continuous g ↔ Continuous (g ∘ ofFn) :=
  isQuotientMap_ofFn.continuous_iff

/-- The quotient map onto the symmetric power is open: the saturation of an open set is the union
of its reindexings, each of them open. -/
theorem isOpenMap_ofFn : IsOpenMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isOpen_preimage, preimage_image_ofFn]
  exact isOpen_iUnion fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The quotient map onto the symmetric power is closed: the saturation of a closed set is the
union of its reindexings, a *finite* union of closed sets. -/
theorem isClosedMap_ofFn : IsClosedMap (ofFn : (Fin n → α) → Sym α n) := fun s hs => by
  rw [← isQuotientMap_ofFn.isCoinducing.isClosed_preimage, preimage_image_ofFn]
  exact isClosed_iUnion_of_finite fun σ => hs.preimage (Pi.continuous_precomp σ)

/-- The symmetric power of a compact space is compact, being a continuous image of a finite power
of that space. -/
instance instCompactSpace [CompactSpace α] : CompactSpace (Sym α n) :=
  ⟨by
    rw [← Set.image_univ_of_surjective (ofFn_surjective (α := α) (n := n))]
    exact isCompact_univ.image continuous_ofFn⟩

/-- The symmetric power of a Hausdorff space is Hausdorff: `ofFn` is an open quotient map, and the
relation it induces is the finite union, over permutations, of the graphs of the reindexing maps,
hence closed. -/
instance instT2Space [T2Space α] : T2Space (Sym α n) := by
  rw [t2Space_iff_of_isOpenQuotientMap
    (.of_isOpenMap_isQuotientMap isOpenMap_ofFn isQuotientMap_ofFn)]
  have hrel : {q : (Fin n → α) × (Fin n → α) | ofFn q.1 = ofFn q.2} =
      ⋃ σ : Equiv.Perm (Fin n), {q : (Fin n → α) × (Fin n → α) | q.1 ∘ σ = q.2} := by
    ext q
    simpa using ofFn_eq_ofFn_iff
  rw [hrel]
  exact isClosed_iUnion_of_finite fun σ =>
    isClosed_eq ((Pi.continuous_precomp σ).comp continuous_fst) continuous_snd

end Sym

end TauCeti
