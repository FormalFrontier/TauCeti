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
the open-ideal condition enters only in the results that need it — Wedhorn's admissibility
setting, the basis claims of Definition 7.29, and the quasi-compactness of Theorem 7.35. The
generalized unit-ideal standard-cover theorem itself requires no openness hypothesis.

The exported interface of the definition, the normalizations and the intersection identity
inherited from `Spv(A)(T/s)`, the whole-space case, containment in `spa A⁺`, and relative
openness in the subspace all hold with no extra hypotheses. The file also proves the forward
standard-cover implication of Corollary 7.53.

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
* `TauCeti.ValuationSpectrum.val_preimage_rationalSubset` : on the subtype `spa A⁺`, a
  rational subset is just the trace of its ambient basic open.
* `TauCeti.ValuationSpectrum.isOpen_val_preimage_rationalSubset` : a rational subset is
  relatively open in the subspace `spa A⁺`.
* `TauCeti.ValuationSpectrum.rationalSubset_inter` : the intersection identity above — the
  set-level half of Remark 7.30(5).
* `TauCeti.ValuationSpectrum.exists_refinement_of_subset` : the re-presentation step of Wedhorn
  §8.2 — from `R(T'/s') ⊆ R(T/s)`, a presentation `R(T''/(s · s'))` of the smaller subset whose
  denominator has each original denominator as a factor and whose numerators contain `t · s'` for
  `t ∈ T` and `t' · s` for `t' ∈ T'`. Constructing a restriction map needs one further, algebraic
  input beyond these, the standing `HasDenominatorPower` hypothesis for the new pair, which this
  file does not supply.
* `TauCeti.ValuationSpectrum.spa_eq_biUnion_rationalSubset_of_span_eq_top` : a finite set
  generating the unit ideal gives a standard rational cover, the forward implication of
  Corollary 7.53.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.29, Remark 7.30, and
  Corollary 7.53.
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
and the open-ideal condition matters only for results such as Wedhorn's admissibility setting
or the basis claims, not for the definition nor the generalized unit-ideal cover. -/
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

/-- **The containment criterion for rational subsets.** One rational subset is contained in
another exactly when, at every point of the smaller, the larger one's numerators are dominated
by its denominator and that denominator is off the support.

Containment in `spa A⁺` is automatic on both sides, so it drops out of the criterion: only the
`T`-over-`s` conditions are left to check. This is the set-level input to Wedhorn's comparison of
two presentations (§8.2) — it says *which* valuation-theoretic facts a containment gives you,
leaving the passage from those facts to invertibility of `s` and power-boundedness of `t/s` in
the coordinate ring as a separate, genuinely algebraic step. -/
theorem rationalSubset_subset_rationalSubset_iff (Aplus : Subring A) (T T' : Finset A)
    (s s' : A) :
    rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s ↔
      ∀ v ∈ rationalSubset Aplus T' s',
        (∀ t ∈ T, v.toValuativeRel.vle t s) ∧ ¬ v.toValuativeRel.vle s 0 := by
  constructor
  · intro h v hv
    exact ((mem_rationalSubset_iff Aplus T s v).mp (h hv)).2
  · intro h v hv
    exact (mem_rationalSubset_iff Aplus T s v).mpr
      ⟨rationalSubset_subset_spa Aplus T' s' hv, (h v hv).1, (h v hv).2⟩

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

/-- On the subtype `spa A⁺`, the preimage of `R(T/s)` is the preimage of the ambient basic
open `Spv(A)(T/s)`: the `spa A⁺` condition is automatic from the subtype. This is the form used
to compare the rational bases of `Spa(A,A⁺)` and `Spv(A,I)`. -/
@[simp]
theorem val_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) =
      Subtype.val ⁻¹' basicOpenFinset T s := by
  rw [rationalSubset_def, Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]

/-- The preimage of `R(T/s)` under the coercion of the subtype `spa A⁺` is open: a rational
subset is relatively open in the adic spectrum. -/
theorem isOpen_val_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    IsOpen (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  rw [val_preimage_rationalSubset]
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

/-! ### Re-presenting a contained rational subset -/

open scoped Classical Pointwise in
/-- **A containment of rational subsets yields a presentation of the smaller one over the product
denominator.** If `R(T'/s') ⊆ R(T/s)` then `R(T'/s')` has a presentation `R(T''/(s · s'))` whose
numerators contain `t · s'` for every `t ∈ T` and `t' · s` for every `t' ∈ T'`.

The denominator is the point: it is divisible by `s`, so in a localisation presented by this pair
`s` is invertible by construction, and each numerator condition makes the fractions of one of the
two original presentations distinguished fractions of the new one. Those are the *set-level* inputs
a restriction map `A⟨T/s⟩ → A⟨T''/(s · s')⟩` is built from, and this is the re-presentation step of
Wedhorn §8.2.

**They are not by themselves enough to construct that map.** A presentation also carries the
standing hypothesis `HasDenominatorPower` for the new pair, an algebraic obligation about the ideal
of definition that this file does not supply — nothing here mentions coordinate rings at all.

Both numerator conditions are given rather than only the one for `T`, because discharging that
standing hypothesis for a product denominator needs the fractions of *each* factor; a consumer
holding one alone could not use it. -/
theorem exists_refinement_of_subset (Aplus : Subring A) (T T' : Finset A) (s s' : A)
    (h : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    ∃ T'' : Finset A, rationalSubset Aplus T' s' = rationalSubset Aplus T'' (s * s')
      ∧ (∀ t ∈ T, t * s' ∈ T'') ∧ ∀ t' ∈ T', t' * s ∈ T'' :=
  ⟨insert s T * insert s' T', by rw [← rationalSubset_inter, Set.inter_eq_right.mpr h],
    fun _ ht ↦ Finset.mul_mem_mul (Finset.mem_insert_of_mem ht) (Finset.mem_insert_self s' T'),
    fun t' ht' ↦ by
      rw [mul_comm t' s]
      exact Finset.mul_mem_mul (Finset.mem_insert_self s T) (Finset.mem_insert_of_mem ht')⟩

/-- Generalization of the pointwise forward implication of Wedhorn Corollary 7.53 (which assumes
a complete Hausdorff affinoid ring): for an arbitrary commutative ring `A` and subring `A⁺`, if `T`
generates the unit ideal of `A`, then every point `v ∈ spa Aplus` belongs to the standard rational
subset `R(T/s)` for some `s ∈ T`. -/
theorem mem_rationalSubset_of_span_eq_top_of_mem_spa (Aplus : Subring A) {T : Finset A}
    (hT : Ideal.span (T : Set A) = ⊤) {v : Spv A} (hv : v ∈ spa Aplus) :
    ∃ s ∈ T, v ∈ rationalSubset Aplus T s := by
  have hT_ne : T.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty.mp h_empty, Finset.coe_empty, Ideal.span_empty] at hT
    have h1 : (1 : A) ∈ (⊥ : Ideal A) := hT ▸ Submodule.mem_top
    rw [Ideal.mem_bot] at h1
    exact v.toValuativeRel.not_vle_one_zero (h1 ▸ v.toValuativeRel.vle_refl 0)
  obtain ⟨s, hs, hmax'⟩ := Finset.exists_max_image T v.valuation hT_ne
  have hmax : ∀ t ∈ T, v.toValuativeRel.vle t s := fun t ht ↦
    (valuation_le_iff v t s).mp (hmax' t ht)
  refine ⟨s, hs, (mem_rationalSubset_iff Aplus T s v).mpr ⟨hv, hmax, fun h_zero ↦ ?_⟩⟩
  have h_supp : (T : Set A) ⊆ (v.supp : Set A) := fun t ht ↦
    (mem_supp_iff v t).mpr (v.toValuativeRel.vle_trans (hmax t ht) h_zero)
  have h_top_supp : Ideal.span (T : Set A) ≤ v.supp := Ideal.span_le.mpr h_supp
  rw [hT] at h_top_supp
  have h1 : (1 : A) ∈ v.supp := h_top_supp Submodule.mem_top
  have h1_vle : v.toValuativeRel.vle 1 0 := (mem_supp_iff v 1).mp h1
  exact v.toValuativeRel.not_vle_one_zero h1_vle

/-- Generalization of the forward implication of Wedhorn Corollary 7.53 (which assumes a complete
Hausdorff affinoid ring): for an arbitrary commutative ring `A` and subring `A⁺`, if a finite set
`T` generates the unit ideal of `A`, then the standard rational subsets `(R(T/t))_{t ∈ T}` cover
`spa Aplus`. -/
theorem spa_eq_biUnion_rationalSubset_of_span_eq_top (Aplus : Subring A) {T : Finset A}
    (hT : Ideal.span (T : Set A) = ⊤) :
    spa Aplus = ⋃ t ∈ T, rationalSubset Aplus T t := by
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨s, hs, hmem⟩ := mem_rationalSubset_of_span_eq_top_of_mem_spa Aplus hT hv
    exact Set.mem_iUnion₂_of_mem hs hmem
  · exact Set.iUnion₂_subset fun t _ ↦ rationalSubset_subset_spa Aplus T t

end TauCeti.ValuationSpectrum

end
