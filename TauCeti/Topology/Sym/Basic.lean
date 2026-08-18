/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Data.Sym.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The symmetric power of a topological space

The `n`-th symmetric power `Sym α n` of a type is the type of unordered `n`-tuples of points of
`α`. It is the quotient of the space `Fin n → α` of ordered tuples by the permutation action, and
this file gives it the corresponding quotient topology, together with the API that a quotient
topology is used through: the quotient map is continuous, and a map out of `Sym α n` is continuous
exactly when its composition with the quotient map is.

The quotient map is `TauCeti.Sym.ofFn` of `TauCeti/Data/Sym/Basic.lean`, which reads an ordered
tuple as an unordered one; the `Fin n → α` form is the one that carries a product topology, so it
is what the quotient topology is defined against. Its surjectivity and the description
`TauCeti.Sym.ofFn_eq_ofFn_iff` of its fibres as the orbits of the permutation action are the two
facts about it used below.

## Main declarations

* `TauCeti.Sym.preimage_image_ofFn`: the saturation of a set of ordered tuples under `ofFn` is the
  union of its reindexings.
* `TauCeti.Sym.instTopologicalSpace`: the quotient topology on `Sym α n`, coinduced along `ofFn`.
* `TauCeti.Sym.isQuotientMap_ofFn`, `TauCeti.Sym.continuous_ofFn` and
  `TauCeti.Sym.continuous_iff_comp_ofFn`: the resulting quotient-map API.
* `TauCeti.Sym.isOpenMap_ofFn`, `TauCeti.Sym.isClosedMap_ofFn` and
  `TauCeti.Sym.isOpenQuotientMap_ofFn`: the quotient map is open and closed, the permutation group
  being finite.
* `TauCeti.Sym.continuous_map`, `TauCeti.Sym.isOpenMap_map` and
  `TauCeti.Sym.isOpenEmbedding_map`: the `n`-th symmetric power of a continuous, open, or open
  embedding map is again one; in particular the symmetric power of an open subspace is an open
  subspace of the symmetric power.
* `TauCeti.Sym.continuous_append` and `TauCeti.Sym.isOpenMap_append`: concatenation of symmetric
  powers is continuous and open.
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

variable {α β : Type*} {m n : ℕ}

/-! ### The fibres of the quotient map -/

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

/-- The quotient map onto the symmetric power is an open quotient map. -/
theorem isOpenQuotientMap_ofFn : IsOpenQuotientMap (ofFn : (Fin n → α) → Sym α n) :=
  .of_isOpenMap_isQuotientMap isOpenMap_ofFn isQuotientMap_ofFn

/-! ### Functoriality -/

/-- The symmetric power of a continuous map is continuous. -/
@[continuity, fun_prop]
theorem continuous_map {f : α → β} (hf : Continuous f) :
    Continuous (Sym.map f : Sym α n → Sym β n) := by
  rw [continuous_iff_comp_ofFn, map_comp_ofFn]
  exact continuous_ofFn.comp (Continuous.piMap fun _ => hf)

/-- The symmetric power of an open map is open: the quotient map onto the symmetric power is open,
and postcomposition by an open map is open on ordered tuples. -/
theorem isOpenMap_map {f : α → β} (hf : IsOpenMap f) :
    IsOpenMap (Sym.map f : Sym α n → Sym β n) := by
  rw [isOpenQuotientMap_ofFn.isOpenMap_iff, map_comp_ofFn]
  exact isOpenMap_ofFn.comp (IsOpenMap.piMap (fun _ => hf) (by simp))

/-- The symmetric power of an open embedding is an open embedding: the `n`-th symmetric power of
an open subspace is an open subspace of the `n`-th symmetric power. -/
theorem isOpenEmbedding_map {f : α → β} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Sym.map f : Sym α n → Sym β n) :=
  .of_continuous_injective_isOpenMap (continuous_map hf.continuous)
    (Sym.map_injective hf.injective n) (isOpenMap_map hf.isOpenMap)

/-- Concatenation of two symmetric-power points is continuous. -/
@[continuity, fun_prop]
theorem continuous_append :
    Continuous fun p : Sym α n × Sym α m => p.1.append p.2 := by
  have hcomp : (fun p : Sym α n × Sym α m => p.1.append p.2) ∘ Prod.map ofFn ofFn =
      ofFn ∘ fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
    funext p
    obtain ⟨f, g⟩ := p
    exact (ofFn_fin_append f g).symm
  rw [← (isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).continuous_comp_iff, hcomp]
  exact continuous_ofFn.comp (Fin.continuous_append n m)

/-- Concatenation of two symmetric-power points is an open map. -/
theorem isOpenMap_append :
    IsOpenMap fun p : Sym α n × Sym α m => p.1.append p.2 := by
  have hcomp : (fun p : Sym α n × Sym α m => p.1.append p.2) ∘ Prod.map ofFn ofFn =
      ofFn ∘ fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
    funext p
    obtain ⟨f, g⟩ := p
    exact (ofFn_fin_append f g).symm
  have hcoe : ⇑(Fin.appendHomeomorph (X := α) n m) =
      fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
    funext q i
    simp
  rw [(isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).isOpenMap_iff, hcomp, ← hcoe]
  exact isOpenMap_ofFn.comp (Fin.appendHomeomorph n m).isOpenMap

/-! ### Separation and compactness -/

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
  rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_ofFn]
  have hrel : {q : (Fin n → α) × (Fin n → α) | ofFn q.1 = ofFn q.2} =
      ⋃ σ : Equiv.Perm (Fin n), {q : (Fin n → α) × (Fin n → α) | q.1 ∘ σ = q.2} := by
    ext q
    simpa using ofFn_eq_ofFn_iff
  rw [hrel]
  exact isClosed_iUnion_of_finite fun σ =>
    isClosed_eq ((Pi.continuous_precomp σ).comp continuous_fst) continuous_snd

end Sym

end TauCeti
