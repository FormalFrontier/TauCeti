/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic

/-!
# Wedhorn's chain of rational subsets

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Remark 7.55.**

Wedhorn refines a rational subset `U = R(T/s)` into a descending chain of rational subsets

```text
Spa (A, A⁺) ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = U
```

in which every step adjoins a single numerator: `X₀ = R({u}/s)` for an element `u` dominated by
`s` throughout `U`, and `Xᵢ` adjoins the `i`-th element of `T`. The point of the
chain is that each of its steps is an elementary one, so a statement about restriction maps
between rational localisations that is stable under composition need only be proved for a single
adjoined numerator; this is how Wedhorn's Proposition 8.30 reduces flatness to an elementary case.

## The dominating element

Wedhorn obtains `u` from quasi-compactness of `U` via his Corollary 7.32, which produces a *unit*
`u ∈ Aˣ` with `|u(x)| < |s(x)| on U`, and writes the first link as
`X₀ = {x ∈ Spa A; 1 ≤ x(s/u)}`. That description presupposes `u` invertible, in order to form the
fraction `s/u`. Here `u : A` is an arbitrary ring element and `X₀` is the rational subset
`R({u}/s)`, which is the same set whenever `u` is a unit: `R({u}/s)` asks for `v(u) ≤ v(s)` together
with `v(s) ≠ 0`, and for a unit the second condition follows from the first, since `v(u) ≠ 0`.
Nothing in the chain needs invertibility, so it is not assumed; a caller holding Corollary 7.32's
unit `ϖ` applies these results with `u := (ϖ : A)`.

Strictness is likewise not needed. Wedhorn's `u` satisfies `v(u) < v(s)` on `U`, but the chain
only ever consumes the non-strict `v(u) ≤ v(s)`, so that is what the results below assume; a
caller holding the strict form passes `(hu v hv).vle`.

Quasi-compactness of `U` is likewise not a hypothesis here. It is the input to Corollary 7.32, and
enters only when a caller discharges the domination hypothesis by that route.

## Main results

* `TauCeti.ValuationSpectrum.exists_rationalSubset_chain` : Remark 7.55 itself — the descending
  chain of rational subsets from `R({u}/s)` down to `R(T/s)`, each step adjoining one element
  of `T`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Remark 7.55.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

open scoped Classical in
/-- Adjoining a fixed element to ever longer prefixes of a list gives an increasing family of
finite sets. This is what makes the chain below descend: a longer prefix is a larger numerator
set, and the rational subset is antitone in that set. -/
private theorem insert_take_toFinset_mono {α : Type*} (u : α) (l : List α) {i j : ℕ}
    (hij : i ≤ j) : insert u (l.take i).toFinset ⊆ insert u (l.take j).toFinset := by
  refine Finset.insert_subset_insert _ ?_
  intro a ha
  rw [List.mem_toFinset] at ha ⊢
  exact (List.take_prefix_take_left hij).subset ha

open scoped Classical in
/-- **Wedhorn Remark 7.55: the chain of rational subsets.** Let `u` be dominated by `s`
throughout `U = R(T/s)`. Then there is a descending chain of rational subsets

```text
Spa (A, A⁺) ⊇ R({u}/s) = X₀ ⊇ X₁ ⊇ ⋯ ⊇ X_{#T} = U
```

whose every step adjoins a single element of `T` to the numerators.

The chain is exhibited by its numerator sets `N i`, each `Xᵢ` being `R(N i / s)`, so that every
member is a rational subset by construction rather than by a separate argument. The enumeration of
`T` is `Finset.toList`; any enumeration would do, and the statement fixes one only so that the
`i`-th step has a name. -/
theorem exists_rationalSubset_chain (Aplus : Subring A) (T : Finset A) (s u : A)
    (hu : ∀ v ∈ rationalSubset Aplus T s, v.toValuativeRel.vle u s) : ∃ N : ℕ → Finset A,
      N 0 = {u} ∧
      (∀ i, rationalSubset Aplus (N i) s ⊆ spa Aplus) ∧
      Antitone (fun i ↦ rationalSubset Aplus (N i) s) ∧
      (∀ i < T.card, ∃ t ∈ T, N (i + 1) = insert t (N i)) ∧
      rationalSubset Aplus (N T.card) s = rationalSubset Aplus T s := by
  classical
  refine ⟨fun i ↦ insert u ((T.toList.take i).toFinset), by simp,
    fun i ↦ rationalSubset_subset_spa _ _ _, ?_, ?_, ?_⟩
  · exact fun i j hij ↦ rationalSubset_subset_rationalSubset_of_subset Aplus
      (insert_take_toFinset_mono u T.toList hij) s
  · intro i hi
    have hlen : i < T.toList.length := by simpa [Finset.length_toList] using hi
    refine ⟨T.toList[i], Finset.mem_toList.mp (List.getElem_mem hlen), ?_⟩
    -- `change` only unfolds the chosen witness: `N i` is by definition
    -- `insert u ((T.toList.take i).toFinset)`, so this restates the goal up to defeq.
    change insert u (T.toList.take (i + 1)).toFinset
        = insert T.toList[i] (insert u (T.toList.take i).toFinset)
    ext a
    rw [← List.take_concat_get' _ _ hlen]
    simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append, List.mem_singleton]
    tauto
  · -- As above, `change` only unfolds the witness `N T.card` to its definition.
    change rationalSubset Aplus (insert u (T.toList.take T.card).toFinset) s
        = rationalSubset Aplus T s
    rw [← Finset.length_toList, List.take_length, Finset.toList_toFinset]
    exact rationalSubset_insert_of_forall_vle Aplus T s u hu

end TauCeti.ValuationSpectrum

end
