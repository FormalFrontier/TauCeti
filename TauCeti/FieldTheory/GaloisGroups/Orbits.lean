/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Galois orbits on the roots of a polynomial

Let `p` be a polynomial over a field `F` and let `E` be an extension in which `p` splits. The
Galois group `Polynomial.Gal p` acts on `p.rootSet E`, and this file identifies the orbits of
that action with the monic irreducible factors of `p`.

The invariant that separates the orbits is the minimal polynomial: two roots lie in the same
orbit exactly when they have the same minimal polynomial over `F`, so the orbit of a root is the
whole root set of its minimal polynomial. Passing to the orbit quotient turns this into a
bijection with the distinct monic irreducible factors of `p`, that is, with the members of
`UniqueFactorizationMonoid.normalizedFactors p`.

The dictionary has an immediate consequence that later work leans on constantly, because the
polynomials it must handle are usually reducible: for a separable polynomial of positive degree
the root action is transitive if and only if the polynomial is irreducible.

## Main results

* `TauCeti.mem_orbit_iff_minpoly_eq`: two roots of `p` are in the same Galois orbit exactly when
  their minimal polynomials agree.
* `TauCeti.image_val_orbit_eq_rootSet_minpoly`: read inside `E`, the orbit of a root is the root
  set of its minimal polynomial.
* `TauCeti.natCard_orbit_eq_natDegree_minpoly`: for separable `p`, an orbit has as many elements
  as the degree of the corresponding factor.
* `TauCeti.isPretransitive_iff_irreducible`: for separable `p` of positive degree, transitivity
  of the root action is equivalent to irreducibility of `p`.
* `TauCeti.orbitQuotientEquivNormalizedFactors`: the orbit quotient is in bijection with the
  monic irreducible factors of `p`, the orbit of a root going to its minimal polynomial.
* `TauCeti.natCard_quotientOrbit_eq_natDegree`: along that bijection, and for separable `p`, the
  degree of a factor is the number of roots in the matching orbit.

## Implementation notes

Everything is stated over an arbitrary splitting extension `E`, not only over
`p.SplittingField`, since the polynomials met in practice are handed to us inside a fixed
extension such as `ℂ`. The action on `p.rootSet E` is transported from the one on
`p.rootSet p.SplittingField` along `Polynomial.Gal.rootsEquivRootsAux`, so the proofs first move
the minimal polynomial across that bijection and then apply Mathlib's
`Normal.minpoly_eq_iff_mem_orbit` in the splitting field, where the extension is normal.

Writing `UniqueFactorizationMonoid.normalizedFactors p` requires the `NormalizationMonoid F[X]`
instance, which is built from `DecidableEq F`; the statements about factors therefore carry that
instance, exactly as Mathlib's `Polynomial.mem_normalizedFactors_iff` does.
-/

public section

namespace TauCeti

open Polynomial UniqueFactorizationMonoid

universe u v w

variable {F : Type u} [Field F] {p : F[X]} (E : Type v) [Field E] [Algebra F E]
  [Fact ((p.map (algebraMap F E)).Splits)]

/-! ## The minimal polynomial as an invariant of a root -/

/-- The minimal polynomial of a root is unchanged by Mathlib's comparison map from the roots in
the splitting field to the roots in an arbitrary splitting extension. -/
theorem minpoly_rootsEquivRootsAux (z : p.rootSet p.SplittingField) :
    minpoly F ((Gal.rootsEquivRootsAux p E z : p.rootSet E) : E)
      = minpoly F (z : p.SplittingField) :=
  minpoly.algHom_eq (IsScalarTower.toAlgHom F p.SplittingField E)
    (algebraMap p.SplittingField E).injective _

/-- The inverse form of `TauCeti.minpoly_rootsEquivRootsAux`. -/
theorem minpoly_rootsEquivRootsAux_symm (x : p.rootSet E) :
    minpoly F (((Gal.rootsEquivRootsAux p E).symm x : p.rootSet p.SplittingField) :
      p.SplittingField) = minpoly F (x : E) := by
  conv_rhs => rw [← Equiv.apply_symm_apply (Gal.rootsEquivRootsAux p E) x]
  exact (minpoly_rootsEquivRootsAux E _).symm

/-- The minimal polynomial of a root of `p` does not depend on the splitting extension in which
the root is read: it is preserved by the Galois-equivariant comparison of two root sets. -/
theorem minpoly_rootsEquivRoots (E' : Type w) [Field E'] [Algebra F E']
    [Fact ((p.map (algebraMap F E')).Splits)] (x : p.rootSet E) :
    minpoly F ((Gal.rootsEquivRoots p E E' x : p.rootSet E') : E') = minpoly F (x : E) :=
  (minpoly_rootsEquivRootsAux E' _).trans (minpoly_rootsEquivRootsAux_symm E x)

/-- Two roots of `p` lie in the same Galois orbit exactly when their minimal polynomials over the
base field agree. -/
theorem mem_orbit_iff_minpoly_eq {x y : p.rootSet E} :
    x ∈ MulAction.orbit p.Gal y ↔ minpoly F (x : E) = minpoly F (y : E) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [← minpoly_rootsEquivRootsAux_symm E (g • y), ← minpoly_rootsEquivRootsAux_symm E y]
    have hg : (Gal.rootsEquivRootsAux p E).symm (g • y)
        = g • (Gal.rootsEquivRootsAux p E).symm y := by
      rw [Gal.smul_def, Equiv.symm_apply_apply]
    rw [hg]
    exact minpoly.algEquiv_eq g _
  · intro h
    rw [← minpoly_rootsEquivRootsAux_symm E x, ← minpoly_rootsEquivRootsAux_symm E y] at h
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp h
    exact ⟨g, (Gal.rootsEquivRootsAux p E).eq_symm_apply.mp (Subtype.ext hg)⟩

/-! ## The orbit of a root -/

/-- The orbit of a root of `p` consists of the roots of its minimal polynomial. -/
theorem orbit_eq_preimage_rootSet_minpoly (x : p.rootSet E) :
    MulAction.orbit p.Gal x = Subtype.val ⁻¹' (minpoly F (x : E)).rootSet E := by
  have hint : IsIntegral F (x : E) := (isAlgebraic_of_mem_rootSet x.2).isIntegral
  ext y
  rw [Set.mem_preimage, mem_rootSet, mem_orbit_iff_minpoly_eq]
  refine ⟨fun h => ⟨minpoly.ne_zero hint, h ▸ minpoly.aeval F (y : E)⟩, fun h => ?_⟩
  exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h.2
    (minpoly.monic hint)).symm

/-- Read inside the ambient field, the orbit of a root of `p` is exactly the root set of its
minimal polynomial. -/
theorem image_val_orbit_eq_rootSet_minpoly (x : p.rootSet E) :
    Subtype.val '' MulAction.orbit p.Gal x = (minpoly F (x : E)).rootSet E := by
  have hdvd : minpoly F (x : E) ∣ p := minpoly.dvd F _ (aeval_eq_zero_of_mem_rootSet x.2)
  refine Set.Subset.antisymm ?_ fun z hz => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (orbit_eq_preimage_rootSet_minpoly E x).le hy
  · have hzp : z ∈ p.rootSet E := mem_rootSet.mpr ⟨ne_zero_of_mem_rootSet x.2,
      aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (aeval_eq_zero_of_mem_rootSet hz)⟩
    exact ⟨⟨z, hzp⟩, (orbit_eq_preimage_rootSet_minpoly E x).ge hz, rfl⟩

/-- For a separable polynomial, the orbit of a root has as many elements as the degree of its
minimal polynomial. -/
theorem natCard_orbit_eq_natDegree_minpoly (hsep : p.Separable) (x : p.rootSet E) :
    Nat.card (MulAction.orbit p.Gal x) = (minpoly F (x : E)).natDegree := by
  have hdvd : minpoly F (x : E) ∣ p := minpoly.dvd F _ (aeval_eq_zero_of_mem_rootSet x.2)
  have hsplits : ((minpoly F (x : E)).map (algebraMap F E)).Splits :=
    (Fact.out (p := ((p.map (algebraMap F E)).Splits))).of_dvd
      (by simpa using ne_zero_of_mem_rootSet x.2) (Polynomial.map_dvd _ hdvd)
  rw [Nat.card_congr (Equiv.Set.image _ _ Subtype.val_injective),
    image_val_orbit_eq_rootSet_minpoly, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree (hsep.of_dvd hdvd) hsplits]

/-! ## Transitivity and irreducibility -/

/-- For a separable polynomial of positive degree, the Galois action on the roots in a splitting
extension is transitive exactly when the polynomial is irreducible.

Separability cannot be dropped: over `ℚ` the polynomial `(X ^ 2 - 2) ^ 2` is reducible, yet its
Galois group acts transitively on its two distinct roots. Without separability the forward
implication only says that `p` is a unit times a power of one irreducible polynomial. -/
theorem isPretransitive_iff_irreducible (hsep : p.Separable) (hdeg : 0 < p.natDegree) :
    MulAction.IsPretransitive p.Gal (p.rootSet E) ↔ Irreducible p := by
  refine ⟨fun h => ?_, fun h => Gal.galAction_isPretransitive p E h⟩
  have hcard : Fintype.card (p.rootSet E) = p.natDegree := card_rootSet_eq_natDegree hsep Fact.out
  obtain ⟨x⟩ : Nonempty (p.rootSet E) := Fintype.card_pos_iff.mp (by omega)
  have hp0 : p ≠ 0 := ne_zero_of_mem_rootSet x.2
  have hint : IsIntegral F (x : E) := (isAlgebraic_of_mem_rootSet x.2).isIntegral
  have hdvd : minpoly F (x : E) ∣ p := minpoly.dvd F _ (aeval_eq_zero_of_mem_rootSet x.2)
  have hdegle : p.natDegree ≤ (minpoly F (x : E)).natDegree := by
    rw [← natCard_orbit_eq_natDegree_minpoly E hsep x, MulAction.orbit_eq_univ]
    simp [Nat.card_eq_fintype_card, hcard]
  have hunit : IsUnit (C p.leadingCoeff) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp0))
  rw [eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hdvd hdegle,
    irreducible_isUnit_mul hunit]
  exact minpoly.irreducible hint

/-! ## Orbits and monic irreducible factors -/

variable [DecidableEq F]

omit [Fact ((p.map (algebraMap F E)).Splits)] in
/-- The minimal polynomial of a root of `p` is one of the monic irreducible factors of `p`. -/
theorem minpoly_mem_normalizedFactors (x : p.rootSet E) :
    minpoly F (x : E) ∈ normalizedFactors p := by
  have hint : IsIntegral F (x : E) := (isAlgebraic_of_mem_rootSet x.2).isIntegral
  exact (Polynomial.mem_normalizedFactors_iff (ne_zero_of_mem_rootSet x.2)).mpr
    ⟨minpoly.irreducible hint, minpoly.monic hint,
      minpoly.dvd F _ (aeval_eq_zero_of_mem_rootSet x.2)⟩

/-- Every monic irreducible factor of `p` is the minimal polynomial of a root of `p` in a
splitting extension. -/
theorem exists_mem_rootSet_minpoly_eq {q : F[X]} (hq : q ∈ normalizedFactors p) :
    ∃ x : p.rootSet E, minpoly F (x : E) = q := by
  have hp : p ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨hirr, hmonic, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hp).mp hq
  have hsplits : (q.map (algebraMap F E)).Splits :=
    (Fact.out (p := ((p.map (algebraMap F E)).Splits))).of_dvd
      (by simpa using hp) (Polynomial.map_dvd _ hdvd)
  have hdeg : (q.map (algebraMap F E)).natDegree ≠ 0 := by
    rw [natDegree_map]
    exact hirr.natDegree_pos.ne'
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero (hsplits.roots_ne_zero hdeg)
  have hzq : aeval z q = 0 := by
    rw [aeval_def, ← eval_map]
    exact (mem_roots (hmonic.map (algebraMap F E)).ne_zero).mp hz
  refine ⟨⟨z, mem_rootSet.mpr ⟨hp, aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hzq⟩⟩, ?_⟩
  exact (minpoly.eq_of_irreducible_of_monic hirr hzq hmonic).symm

variable (p) in
/-- The Galois orbits on the roots of `p` in a splitting extension are in bijection with the
monic irreducible factors of `p`; the orbit of a root goes to its minimal polynomial. -/
noncomputable def orbitQuotientEquivNormalizedFactors :
    MulAction.orbitRel.Quotient p.Gal (p.rootSet E) ≃ {q : F[X] // q ∈ normalizedFactors p} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x : p.rootSet E =>
        (⟨minpoly F (x : E), minpoly_mem_normalizedFactors E x⟩ :
          {q : F[X] // q ∈ normalizedFactors p}))
      fun _ _ hxy => Subtype.ext ((mem_orbit_iff_minpoly_eq E).mp hxy))
    ⟨by
      refine fun a b => Quotient.inductionOn₂ a b fun x y hxy => ?_
      exact Quotient.sound ((mem_orbit_iff_minpoly_eq E).mpr (Subtype.ext_iff.mp hxy)), by
      rintro ⟨q, hq⟩
      obtain ⟨x, hx⟩ := exists_mem_rootSet_minpoly_eq E hq
      exact ⟨Quotient.mk _ x, Subtype.ext hx⟩⟩

@[simp]
theorem orbitQuotientEquivNormalizedFactors_mk (x : p.rootSet E) :
    orbitQuotientEquivNormalizedFactors p E (Quotient.mk _ x)
      = ⟨minpoly F (x : E), minpoly_mem_normalizedFactors E x⟩ :=
  (rfl)

/-- Along the bijection of `TauCeti.orbitQuotientEquivNormalizedFactors`, the degree of a monic
irreducible factor of a separable `p` is the number of roots in the matching Galois orbit. -/
theorem natCard_quotientOrbit_eq_natDegree (hsep : p.Separable)
    (ω : MulAction.orbitRel.Quotient p.Gal (p.rootSet E)) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω)
      = (orbitQuotientEquivNormalizedFactors p E ω : F[X]).natDegree := by
  induction ω using Quotient.inductionOn with
  | h x => exact natCard_orbit_eq_natDegree_minpoly E hsep x

variable (p) in
/-- The number of Galois orbits on the roots of `p` is the number of its monic irreducible
factors. -/
theorem natCard_orbitQuotient :
    Nat.card (MulAction.orbitRel.Quotient p.Gal (p.rootSet E))
      = Nat.card {q : F[X] // q ∈ normalizedFactors p} :=
  Nat.card_congr (orbitQuotientEquivNormalizedFactors p E)

end TauCeti
