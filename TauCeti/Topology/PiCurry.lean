/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Currying and regrouping a tuple, topologically

A family of spaces indexed by a sigma type has the same sections as the curried family: the
equivalence `Equiv.piCurry` is a homeomorphism for the product topologies. Composing it with a
bijection `(Σ i, Fin (m i)) ≃ Fin n`, available whenever the degrees `m i` add up to `n`, presents
an `n`-tuple of points of a fixed space as a family of `m i`-tuples.

Mathlib has `Homeomorph.piCurry` for a *product* index `X × Y`; the sigma-indexed version below is
what a decomposition `n = ∑ i, m i` with varying `m i` needs.

## Main declarations

* `TauCeti.piCurryHomeomorph`: `Equiv.piCurry` as a homeomorphism.
* `TauCeti.piFinSumHomeomorph`: for `∑ i, m i = n`, a homeomorphism between the families of
  `m i`-tuples of points of `Y` and the `n`-tuples of points of `Y`. It depends on a choice of
  bijection `(Σ i, Fin (m i)) ≃ Fin n` and so is not canonical; only its existence is ever used.
-/

public section

namespace TauCeti

/-- **Currying a sigma-indexed family of spaces**, as a homeomorphism.

It is `@[expose]`d because both directions are used through their defining formulas, which a
theorem exported from this file may not unfold otherwise. -/
@[expose]
def piCurryHomeomorph {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] : (∀ p : Σ i, κ i, Y p.1 p.2) ≃ₜ (∀ i j, Y i j) where
  toEquiv := Equiv.piCurry Y
  continuous_toFun :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (⟨i, j⟩ : Σ i, κ i)
  continuous_invFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)

@[simp]
theorem piCurryHomeomorph_apply {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] (f : ∀ p : Σ i, κ i, Y p.1 p.2) (i : ι) (j : κ i) :
    piCurryHomeomorph Y f i j = f ⟨i, j⟩ :=
  (rfl)

@[simp]
theorem piCurryHomeomorph_symm_apply {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] (f : ∀ i j, Y i j) (p : Σ i, κ i) :
    (piCurryHomeomorph Y).symm f p = f p.1 p.2 :=
  (rfl)

/-- **Regrouping a tuple.** If the degrees `m i` add up to `n`, then a family of `m i`-tuples of
points of `Y` carries the same information as an `n`-tuple of points of `Y`. The identification
depends on a choice of bijection `(Σ i, Fin (m i)) ≃ Fin n`; it is used only through its
existence. -/
noncomputable def piFinSumHomeomorph (Y : Type*) [TopologicalSpace Y] {ι : Type*} [Fintype ι]
    {m : ι → ℕ} {n : ℕ} (hn : ∑ i, m i = n) : (∀ i, Fin (m i) → Y) ≃ₜ (Fin n → Y) :=
  (piCurryHomeomorph fun (i : ι) (_ : Fin (m i)) => Y).symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin n => Y)
      (Fintype.equivFinOfCardEq (by simpa using hn)))

end TauCeti
