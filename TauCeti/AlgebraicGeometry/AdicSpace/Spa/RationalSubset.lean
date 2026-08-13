/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic

/-!
# Rational subsets of the adic spectrum

**The set-level constructions beneath Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
Definition 7.29 and Remark 7.30.**

For a finite numerator set `T` and a denominator `s`, the rational subset is the trace on
`spa A⁺` of the basic open `Spv(A)(T/s)`:

```text
R(T/s) = {v ∈ spa A⁺ ; v(t) ≤ v(s) ≠ 0 for every t ∈ T} = spa A⁺ ∩ Spv(A)(T/s).
```

As with `spa` itself, the definition is stated for arbitrary data: no hypothesis relates the
topology of `A` to its ring operations, the subring is arbitrary, and Wedhorn's standing
condition that the ideal `T · A` be open is not assumed. It is Wedhorn's rational subset of
`Spa (A, A⁺)` under his hypotheses (a Huber ring, a ring of integral elements, `T · A` open);
the open-ideal condition enters only in the results that need it — the basis claims of
Definition 7.29 and the quasi-compactness of Theorem 7.35 — none of which is in this file.

What is here is what holds with no hypotheses at all: the exported interface of the
definition, the normalizations and the intersection identity inherited from `Spv(A)(T/s)`,
the whole-space case, containment in `spa A⁺`, and relative openness in the subspace.

On the intersection identity, writing `Uᵢ = insert sᵢ Tᵢ` for each numerator set augmented by
its own denominator (which costs nothing, by `rationalSubset_insert_self`),

```text
R(T₁/s₁) ∩ R(T₂/s₂) = R(U₁U₂ / s₁s₂).
```

The augmentation is essential: with the bare products `T₁T₂` the identity is false — for
`T₁ = {t}` and `T₂ = ∅` the right-hand side would forget the condition `v(t) ≤ v(s₁)`. This
identity is the set-level half of Wedhorn's Remark 7.30(5); his full statement also says the
right-hand pair is again *admissible* (`U₁U₂ · A` open), which belongs to the open-ideal
layer deferred above.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalSubset` : the rational subset `R(T/s)` of `spa A⁺`, as a
  `Set (Spv A)`.

## Main results

* `TauCeti.ValuationSpectrum.rationalSubset_def` and
  `TauCeti.ValuationSpectrum.mem_rationalSubset_iff` : the set-level and membership-level
  characterizations — the definition is not exposed across the module boundary, so these two
  are the exported interface, as for `spa_def`/`mem_spa_iff`.
* `TauCeti.ValuationSpectrum.rationalSubset_subset_spa` : every rational subset is contained
  in the adic spectrum.
* `TauCeti.ValuationSpectrum.rationalSubset_insert_self` : the denominator may be inserted
  among the numerators.
* `TauCeti.ValuationSpectrum.rationalSubset_singleton_one` : the whole spectrum is the
  rational subset `R({1}/1)` — Wedhorn's "`Spa (A, A⁺)` itself is rational".
* `TauCeti.ValuationSpectrum.isOpen_val_preimage_rationalSubset` : a rational subset is
  relatively open in the subspace `spa A⁺`.
* `TauCeti.ValuationSpectrum.rationalSubset_inter` : the intersection identity above — the
  set-level half of Remark 7.30(5).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.29 and Remark 7.30.
* AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/AdicSpaces/Adic spaces/RationalSubsets.lean`, is the roadmap's designated prior
  formalisation of this material and was consulted. It develops the same statements around a
  standalone `rationalOpen` and an existential `IsRationalSubset` predicate, with the
  intersection identity conditioned on each denominator lying in its numerator set and the
  same insert-absorption discharging that condition. Here the rational subset is instead the
  trace of the merged `Spv A`-level `basicOpenFinset`, so the identities are inherited from
  `basicOpenFinset_insert_self` and `basicOpenFinset_inter` rather than reproved; nothing was
  copied.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The rational subset `R(T/s)` of the adic spectrum: the trace on `spa A⁺` of the basic open
`Spv(A)(T/s)`. Under Wedhorn's hypotheses — a Huber ring, a ring of integral elements, and the
ideal `T · A` open — this is his Definition 7.29; the definition itself asks for none of them,
and the open-ideal condition first matters for the basis claims, which are not in this file. -/
def rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) : Set (Spv A) :=
  spa Aplus ∩ basicOpenFinset T s

/-- The set-level characterization of a rational subset. The definition is not exposed across
the module boundary, so this equation is how consumers apply set-level results to
`rationalSubset` — for instance `rationalSubset_def _ _ _ ▸ Set.inter_subset_left` for the
containment in `spa A⁺`, which `rationalSubset_subset_spa` records. -/
theorem rationalSubset_def (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus T s = spa Aplus ∩ basicOpenFinset T s := (rfl)

/-- Membership in `R(T/s)`: a point of the adic spectrum where every numerator is dominated by
the denominator and the denominator is not in the support. -/
@[simp]
theorem mem_rationalSubset_iff (Aplus : Subring A) (T : Finset A) (s : A) (v : Spv A) :
    v ∈ rationalSubset Aplus T s ↔
      v ∈ spa Aplus ∧ (∀ t ∈ T, v.toValuativeRel.vle t s) ∧ ¬ v.toValuativeRel.vle s 0 := by
  rw [rationalSubset_def, Set.mem_inter_iff, mem_basicOpenFinset_iff]

/-- Every rational subset is contained in the adic spectrum. -/
theorem rationalSubset_subset_spa (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus T s ⊆ spa Aplus :=
  rationalSubset_def Aplus T s ▸ Set.inter_subset_left

open scoped Classical in
/-- Inserting the denominator among the numerators changes nothing — Wedhorn's "one may
replace `T` by `T ∪ {s}`" (Definition 7.29). -/
@[simp]
theorem rationalSubset_insert_self (Aplus : Subring A) (T : Finset A) (s : A) :
    rationalSubset Aplus (insert s T) s = rationalSubset Aplus T s := by
  rw [rationalSubset_def, rationalSubset_def, basicOpenFinset_insert_self]

/-- The whole adic spectrum is the rational subset `R({1}/1)` — Wedhorn's observation that
`Spa (A, A⁺)` itself is rational. The single condition `v(1) ≤ v(1) ≠ 0` holds at every
point. -/
@[simp]
theorem rationalSubset_singleton_one (Aplus : Subring A) :
    rationalSubset Aplus {1} 1 = spa Aplus := by
  rw [rationalSubset_def]
  refine Set.inter_eq_left.mpr fun v _ => (mem_basicOpenFinset_iff _ _ _).mpr ?_
  exact ⟨fun t ht => by simp [Finset.mem_singleton.mp ht],
    v.toValuativeRel.not_vle_one_zero⟩

/-- The preimage of `R(T/s)` under the coercion of the subtype `spa A⁺` is open: a rational
subset is relatively open in the adic spectrum. -/
theorem isOpen_val_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    IsOpen (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  rw [rationalSubset_def, Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]
  exact (isOpen_basicOpenFinset T s).preimage continuous_subtype_val

open scoped Classical Pointwise in
/-- **The set-level half of Wedhorn Remark 7.30(5)**: writing `Uᵢ = insert sᵢ Tᵢ` for each
numerator set augmented by its own denominator,
`R(T₁/s₁) ∩ R(T₂/s₂) = R(U₁U₂ / s₁s₂)`. The augmentation costs nothing
(`rationalSubset_insert_self`) and is essential — with the bare products the identity fails
for `T₂ = ∅`. Wedhorn's full Remark 7.30(5) additionally says the right-hand pair is again
admissible; that lives with the deferred open-ideal layer. This identity is the form Theorem
7.35's own proof consumes. -/
@[simp]
theorem rationalSubset_inter (Aplus : Subring A) (T₁ T₂ : Finset A) (s₁ s₂ : A) :
    rationalSubset Aplus T₁ s₁ ∩ rationalSubset Aplus T₂ s₂
      = rationalSubset Aplus (insert s₁ T₁ * insert s₂ T₂) (s₁ * s₂) := by
  rw [rationalSubset_def, rationalSubset_def, rationalSubset_def, ← basicOpenFinset_inter]
  exact (Set.inter_inter_distrib_left _ _ _).symm

end TauCeti.ValuationSpectrum

end
