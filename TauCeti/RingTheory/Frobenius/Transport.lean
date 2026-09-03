/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Transporting unramifiedness and Frobenius data along an algebra equivalence

An algebra equivalence `e : S ≃ₐ[R] T` of commutative `R`-algebras moves ideals of `S` to ideals
of `T` and conjugates endomorphisms of `S` into endomorphisms of `T`.  The local data attached to
a prime is invariant under this transport:

* the contraction to `R` of an ideal is unchanged by mapping it along `e`
  (`Ideal.under_mapAlgEquiv`), and mapping along `e` and back along `e.symm` recovers the ideal
  (`Ideal.map_of_equiv`);
* unramifiedness at a prime is preserved, and is an equivalence
  (`Algebra.IsUnramifiedAt.mapAlgEquiv`, `Algebra.IsUnramifiedAt.mapAlgEquiv_iff`);
* an arithmetic Frobenius `φ : S →ₐ[R] S` conjugates to an arithmetic Frobenius at the mapped
  prime, and the property is an equivalence (`AlgHom.IsArithFrobAt.mapAlgEquiv`,
  `AlgHom.IsArithFrobAt.mapAlgEquiv_iff`).

These are the generic commutative-algebra forms of the number-field transport facts in
`TauCeti/NumberTheory/NumberField/Frobenius/Transport.lean`, which specialize them along the
ring-of-integers equivalence `NumberField.RingOfIntegers.mapAlgEquiv`.

-/

public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **Mapping an ideal along an algebra equivalence preserves its contraction.**  For an
`R`-algebra equivalence `e : S ≃ₐ[R] T`, the ideal `Q.map e` of `T` has the same contraction to
`R` as `Q`. -/
@[simp]
theorem under_mapAlgEquiv (e : S ≃ₐ[R] T) (Q : Ideal S) :
    (Q.map e).under R = Q.under R := by
  rw [under_def, under_def]
  -- `Ideal.map` is applied via `RingHomClass`, so the `AlgEquiv` and `RingEquiv`
  -- coercions give syntactically different terms; they coincide definitionally
  -- (Mathlib proves the underlying `RingHom` equality
  -- `AlgEquiv.toRingEquiv_toRingHom` itself by `rfl`), hence this `rfl`.
  have hmap : Q.map e = Q.map (e.toRingEquiv : S →+* T) := rfl
  rw [hmap, map_comap_of_equiv]
  ext x
  simp only [mem_comap]
  rw [← e.commutes]
  simp

end Ideal

namespace Algebra.IsUnramifiedAt

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **Unramifiedness is preserved by an algebra equivalence.**  If `S` is unramified over `R` at
the prime `Q` and `e : S ≃ₐ[R] T`, then `T` is unramified over `R` at the mapped prime. -/
theorem mapAlgEquiv (e : S ≃ₐ[R] T) (Q : Ideal S) [Q.IsPrime]
    (hQ : IsUnramifiedAt R Q) : IsUnramifiedAt R (Q.map e) := by
  have hcomap : Q = (Q.map e).comap e :=
    (Q.comap_map_of_bijective _ e.bijective).symm
  let eLocal : Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime (Q.map e) :=
    Localization.localAlgEquiv Q _ e hcomap
  let _ : Algebra.FormallyUnramified R (Localization.AtPrime Q) := hQ
  exact Algebra.FormallyUnramified.of_equiv eLocal

/-- **Unramifiedness is invariant under an algebra equivalence.** -/
@[simp]
theorem mapAlgEquiv_iff (e : S ≃ₐ[R] T) (Q : Ideal S) [Q.IsPrime] :
    IsUnramifiedAt R (Q.map e) ↔ IsUnramifiedAt R Q := by
  constructor
  · intro h
    have _hp : ((Q.map e : Ideal T)).IsPrime := Ideal.map_isPrime_of_equiv e
    have hQ := mapAlgEquiv e.symm (Q.map e) h
    have hmap : (Q.map e).map e.symm = Q := Ideal.map_of_equiv e.toRingEquiv
    simp only [hmap] at hQ
    exact hQ
  · exact mapAlgEquiv e Q

end Algebra.IsUnramifiedAt

namespace AlgHom.IsArithFrobAt

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **An arithmetic Frobenius conjugates to an arithmetic Frobenius.**  If `φ : S →ₐ[R] S` is an
arithmetic Frobenius at `Q` and `e : S ≃ₐ[R] T`, then the conjugate
`e ∘ φ ∘ e.symm : T →ₐ[R] T` is an arithmetic Frobenius at the mapped prime `Q.map e`.  The
exponent is unchanged because the mapped prime has the same contraction to `R`
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
