/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers, and the map
`TauCeti.Sym.ofFn` reading an ordered `n`-tuple `f : Fin n → α` as an unordered one.

`ofFn` presents `Sym α n` as a quotient of `Fin n → α`: it is surjective, and its fibres are the
orbits of the permutation action, by `TauCeti.Sym.ofFn_eq_ofFn_iff`. Nothing here is topological;
`TauCeti/Topology/Sym.lean` uses this to give `Sym α n` the quotient topology coinduced along
`ofFn`.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.symFinTwoEquiv`: an unordered `d`-tuple over `Fin 2` is determined by how many of its
  entries are `0`, so there are `d + 1` of them.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; the `Fin n → α`
form is the one that carries a product topology, so it is the map that `Sym α n` carries the
quotient topology along in `TauCeti/Topology/Sym.lean`. -/
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

end Sym

/-! ### Unordered tuples over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

end TauCeti
