/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Bounding a product of ideals by a span over a subsemiring

Let `S` be a subsemiring of `R`, let `G ⊆ R`, and let `J` be an ideal of `R` whose elements lie
in `S`. Then

```text
J * Ideal.span G ≤ Submodule.span S G,
```

the containment being of `S`-submodules of `R`. Taking `J = Ideal.span G`, legitimate when that
ideal itself lies inside `S`, bounds the *square* of the ideal.

## Why the coefficients can be moved

An element `Σ bᵢ gᵢ` of `Ideal.span G` has its coefficients `bᵢ` in `R`, and nothing puts them in
`S` — so `Ideal.span G` generally is **not** spanned by `G` over `S`. Multiplying by `x ∈ J`
rescues this, because the coefficients move onto the other factor:

```text
x * (Σ bᵢ gᵢ) = Σ (x * bᵢ) gᵢ
```

and each `x * bᵢ` lies in `J`, hence in `S`. The new coefficients are in `S` even though the old
ones were not.

Only `CommSemiring` and `SubsemiringClass` are needed: no step uses negation.

## What is and is not claimed

The conclusion is a **containment**, not an equality, and it does not say the left side is a
finitely generated `S`-submodule: a submodule of a finitely generated module need not be finitely
generated over a non-noetherian ring. What it gives, for finite `G`, is a finitely generated
`S`-submodule sitting *above* the product.

In the intended application — the intersection of two rings of definition, where the ideal must
descend to a *smaller* subring and `Ideal.map` is unavailable — `G` lies inside `Ideal.span G`,
which lies inside `S`, so `Submodule.span S G` is an ideal of `S`, is finitely generated when `G`
is, and sandwiches the square as `I * I ≤ Submodule.span S G ≤ I`.

## Main results

* `Submodule.mul_mem_span_of_mem_ideal_span`
* `Submodule.restrictScalars_mul_ideal_span_le_span`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Corollary 6.4.
-/

public section

namespace Submodule

variable {R : Type*} [CommSemiring R] {T : Type*} [SetLike T R] [SubsemiringClass T R] (S : T)
  {G : Set R} {J : Ideal R}

/-- Multiplying by an element of an ideal contained in `S` moves the coefficients into `S`: for
`x` in such an ideal and `y` in `Ideal.span G`, the product `x * y` lies in the `S`-span of `G`. -/
theorem mul_mem_span_of_mem_ideal_span (hJS : ∀ x ∈ J, x ∈ S) {x y : R} (hx : x ∈ J)
    (hy : y ∈ Ideal.span G) : x * y ∈ Submodule.span S G := by
  induction hy using Submodule.span_induction generalizing x with
  | mem g hg => exact Submodule.smul_mem _ (⟨x, hJS x hx⟩ : S) (Submodule.subset_span hg)
  | zero => simp
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ (ih₁ hx) (ih₂ hx)
  | smul c y _ ih => rw [smul_eq_mul, ← mul_assoc]; exact ih (J.mul_mem_right c hx)

/-- **An ideal inside a subsemiring, times a span, is bounded by the span over that subsemiring.**
If `J` is an ideal of `R` lying inside `S`, then `J * Ideal.span G` is contained in the `S`-span
of `G`. Taking `J = Ideal.span G`, legitimate when that ideal itself lies inside `S`, bounds the
square of the ideal. -/
theorem restrictScalars_mul_ideal_span_le_span (hJS : ∀ x ∈ J, x ∈ S) :
    Submodule.restrictScalars S (J * Ideal.span G) ≤ Submodule.span S G := by
  intro a ha
  rw [Submodule.restrictScalars_mem] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) fun x y hx hy ↦ ?_
  · exact mul_mem_span_of_mem_ideal_span S hJS hx hy
  · exact Submodule.add_mem _ hx hy

end Submodule
