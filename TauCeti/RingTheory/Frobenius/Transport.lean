/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
public import TauCeti.RingTheory.Ideal.AlgEquiv

/-!
# Transporting ideals and Frobenius data along an algebra equivalence

An algebra equivalence `e : S ≃ₐ[R] T` of commutative `R`-algebras moves ideals of `S` to ideals
of `T` and conjugates endomorphisms of `S` into endomorphisms of `T`.  The local data attached to
an ideal is invariant under this transport:

* the contraction to `R` of an ideal is unchanged by mapping it along `e`
  (`Ideal.under_mapAlgEquiv`);
* an arithmetic Frobenius `φ : S →ₐ[R] S` conjugates to an arithmetic Frobenius at the mapped
  ideal, and the property is an equivalence (`AlgHom.IsArithFrobAt.mapAlgEquiv`,
  `AlgHom.IsArithFrobAt.mapAlgEquiv_iff`).

The arithmetic Frobenius results can be combined with the number-field compatibility of
automorphism actions on rings of integers in
`TauCeti/NumberTheory/NumberField/AutomorphismAction.lean`.

-/

public section

namespace AlgHom.IsArithFrobAt

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **An arithmetic Frobenius conjugates to an arithmetic Frobenius.**  If `φ : S →ₐ[R] S` is an
arithmetic Frobenius at `Q` and `e : S ≃ₐ[R] T`, then the conjugate
`e ∘ φ ∘ e.symm : T →ₐ[R] T` is an arithmetic Frobenius at the mapped ideal `Q.map e`.  The
exponent is unchanged because the mapped ideal has the same contraction to `R`
(`Ideal.under_mapAlgEquiv`). -/
theorem mapAlgEquiv (e : S ≃ₐ[R] T) (Q : Ideal S) (φ : S →ₐ[R] S)
    (hφ : φ.IsArithFrobAt Q) :
    ((e : S →ₐ[R] T).comp (φ.comp e.symm.toAlgHom)).IsArithFrobAt (Q.map e) := by
  intro x
  rw [Ideal.under_mapAlgEquiv]
  simp only [AlgHom.comp_apply]
  have h2 : (e : S →ₐ[R] T) (φ (e.symm x) - (e.symm x) ^ Nat.card (R ⧸ Q.under R))
      ∈ Q.map e := Ideal.mem_map_of_mem e (hφ (e.symm x))
  -- Push the conjugated map inside with named lemmas only: unfold the
  -- `(↑e : S →ₐ[R] T)` application via `toAlgHom_apply`, then cancel
  -- `e (e.symm x)` with `apply_symm_apply` (`simp only` rewrites every occurrence;
  -- a single `rw` rewrites only the first unified instance).
  simp only [map_sub, map_pow, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply] at h2
  exact h2

/-- **Being an arithmetic Frobenius is invariant under conjugation by an algebra equivalence.** -/
@[simp]
theorem mapAlgEquiv_iff (e : S ≃ₐ[R] T) (Q : Ideal S) (φ : S →ₐ[R] S) :
    ((e : S →ₐ[R] T).comp (φ.comp e.symm.toAlgHom)).IsArithFrobAt (Q.map e) ↔
      φ.IsArithFrobAt Q := by
  constructor
  · intro h
    have h' := mapAlgEquiv e.symm (Q.map e) _ h
    have hmap : (Q.map e).map e.symm = Q := Ideal.map_of_equiv e.toRingEquiv
    simp only [hmap] at h'
    have hcomp : e.symm.toAlgHom.comp
        (((e : S →ₐ[R] T).comp (φ.comp e.symm.toAlgHom)).comp e.symm.symm.toAlgHom) = φ := by
      ext y
      simp
    rwa [hcomp] at h'
  · exact mapAlgEquiv e Q φ

end AlgHom.IsArithFrobAt
