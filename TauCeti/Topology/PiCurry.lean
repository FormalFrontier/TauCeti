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
* `TauCeti.piSigmaHomeomorph`: reindex a curried dependent family along an equivalence from its
  sigma index.
* `TauCeti.piFinSumHomeomorph`: along an explicit equivalence `(Σ i, Fin (m i)) ≃ Fin n`, a
  homeomorphism between families of `m i`-tuples and `n`-tuples.
-/

public section

namespace TauCeti

/-- **Currying a sigma-indexed family of spaces**, as a homeomorphism. -/
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

/-- **Regrouping a dependent family.** Curry a family indexed by a sigma type, then reindex its
uncurried form along an explicit equivalence. -/
def piSigmaHomeomorph {ι : Type*} {κ : ι → Type*} (Z : ι → Type*)
    [∀ i, TopologicalSpace (Z i)] {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → Z i) ≃ₜ (∀ j : ι', Z (e.symm j).1) :=
  (piCurryHomeomorph fun (i : ι) (_ : κ i) => Z i).symm.trans
    (Homeomorph.piCongrLeft (Y := fun k : (Σ i, κ i) => Z k.1) e.symm).symm

@[simp]
theorem piSigmaHomeomorph_apply {ι : Type*} {κ : ι → Type*} (Z : ι → Type*)
    [∀ i, TopologicalSpace (Z i)] {ι' : Type*} (e : (Σ i, κ i) ≃ ι')
    (f : ∀ i, κ i → Z i) (j : ι') :
    piSigmaHomeomorph Z e f j = f (e.symm j).1 (e.symm j).2 :=
  (rfl)

/-- **Regrouping a tuple.** An explicit bijection `(Σ i, Fin (m i)) ≃ Fin n` identifies a family
of `m i`-tuples of points of `Y` with an `n`-tuple of points of `Y`. -/
def piFinSumHomeomorph (Y : Type*) [TopologicalSpace Y] {ι : Type*} {m : ι → ℕ} {n : ℕ}
    (e : (Σ i, Fin (m i)) ≃ Fin n) : (∀ i, Fin (m i) → Y) ≃ₜ (Fin n → Y) :=
  piSigmaHomeomorph (fun _ : ι => Y) e

@[simp]
theorem piFinSumHomeomorph_apply (Y : Type*) [TopologicalSpace Y] {ι : Type*} {m : ι → ℕ}
    {n : ℕ} (e : (Σ i, Fin (m i)) ≃ Fin n) (f : ∀ i, Fin (m i) → Y) (j : Fin n) :
    piFinSumHomeomorph Y e f j = f (e.symm j).1 (e.symm j).2 :=
  (rfl)

@[simp]
theorem piFinSumHomeomorph_symm_apply (Y : Type*) [TopologicalSpace Y] {ι : Type*} {m : ι → ℕ}
    {n : ℕ} (e : (Σ i, Fin (m i)) ≃ Fin n) (f : Fin n → Y) (i : ι) (j : Fin (m i)) :
    (piFinSumHomeomorph Y e).symm f i j = f (e ⟨i, j⟩) :=
  by
    change (Homeomorph.piCongrLeft (Y := fun _ : (Σ i, Fin (m i)) => Y) e.symm) f ⟨i, j⟩ = _
    simpa using Homeomorph.piCongrLeft_apply_apply
      (Y := fun _ : (Σ i, Fin (m i)) => Y) e.symm f (e ⟨i, j⟩)

end TauCeti
