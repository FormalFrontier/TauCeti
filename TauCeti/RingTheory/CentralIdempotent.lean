/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Central idempotents

A **central idempotent** of a ring `R` is an element `e` with `e * e = e` that commutes with
everything.  Such an element splits `R` as a product of the two rings `eR` and `(1 - e)R`, so the
central idempotents record how far `R` is from being indecomposable as a ring.

This file collects the three facts that make `TauCeti.centralIdempotents` a *counting* invariant.
It is preserved by ring isomorphisms (`TauCeti.centralIdempotentsCongr`); it is computed
coordinatewise on a product (`TauCeti.centralIdempotentsPiEquiv`); and a simple ring has exactly
two of them, `0` and `1` (`TauCeti.centralIdempotents_eq_pair`).  Together these say that a finite
product of simple rings has exactly `2 ^ (number of factors)` central idempotents
(`TauCeti.card_centralIdempotents_pi_of_isSimpleRing`), so the number of factors can be read off
the isomorphism class of the ring alone; `TauCeti/RingTheory/Semisimple/BlockCount.lean` draws that
conclusion.

Mathlib has `IsIdempotentElem` and the orthogonal decompositions of `1` it generates
(`Mathlib/RingTheory/Idempotents.lean`), and `Subring.center`, but nothing about the idempotents
that are also central.  The one nontrivial ingredient below,
`TauCeti.centralIdempotents_eq_pair`, is the observation that a central idempotent of `R` is an
idempotent of `Subring.center R`, which for simple `R` is a field by
`IsSimpleRing.isField_center`; a field has only the idempotents `0` and `1`.

The last section applies that dichotomy in the other direction: a surjection of algebras
`A × A ↠ B` onto a *simple* `B` sends `(1, 0)` to a central idempotent, so one of the two blocks
already maps onto `B` (`TauCeti.exists_algHom_surjective_of_prod`).

## Main definitions

* `TauCeti.centralIdempotents R`: the set of central idempotents of `R`.
* `TauCeti.centralIdempotentsCongr`: a ring isomorphism `R ≃+* S` restricts to an equivalence
  between the central idempotents of `R` and those of `S`.
* `TauCeti.centralIdempotentsPiEquiv`: the central idempotents of a product of rings are the
  families of central idempotents of the factors.

## Main results

* `TauCeti.centralIdempotents_eq_pair`: **a simple ring has exactly the two central idempotents
  `0` and `1`**, and `TauCeti.card_centralIdempotents_of_isSimpleRing` counts them.
* `TauCeti.card_centralIdempotents_pi`: the count is multiplicative over a finite product, whence
  `TauCeti.card_centralIdempotents_pi_of_isSimpleRing`: a finite product of simple rings has
  `2 ^ (number of factors)` central idempotents.
* `TauCeti.exists_algHom_surjective_of_prod`: a surjection of algebras `A × A ↠ B` onto a simple
  ring restricts to a surjection along one of the two coordinates.

## Implementation notes

`centralIdempotents R` is a `Set R` rather than a subtype or a bundled structure: the only thing
done with it here is to transport it along isomorphisms and to count it, and `Nat.card` of the
coercion is the count.  Centrality is spelled as membership in `Subring.center R`, which is
Mathlib's canonical form; `TauCeti.mul_comm_of_mem_centralIdempotents` unpacks it to the bare
commutation equation.
-/

public section

namespace TauCeti

variable {R S : Type*} [Ring R] [Ring S]

/-- The set of **central idempotents** of a ring: the idempotents lying in the centre. -/
def centralIdempotents (R : Type*) [Ring R] : Set R :=
  {e | IsIdempotentElem e ∧ e ∈ Subring.center R}

-- Not `@[simp]`: unfolding membership everywhere would rewrite the left-hand side of
-- `mem_centralIdempotents_pi` below, so only one of the two can be a simp lemma, and the
-- coordinatewise form is the useful normal form.
theorem mem_centralIdempotents {e : R} :
    e ∈ centralIdempotents R ↔ IsIdempotentElem e ∧ e ∈ Subring.center R := (Iff.rfl)

/-- A central idempotent is idempotent. -/
theorem isIdempotentElem_of_mem_centralIdempotents {e : R} (he : e ∈ centralIdempotents R) :
    IsIdempotentElem e :=
  he.1

/-- A central idempotent commutes with every element. -/
theorem mul_comm_of_mem_centralIdempotents {e : R} (he : e ∈ centralIdempotents R) (x : R) :
    e * x = x * e :=
  (Subring.mem_center_iff.mp he.2 x).symm

theorem zero_mem_centralIdempotents : (0 : R) ∈ centralIdempotents R :=
  ⟨IsIdempotentElem.zero, Subring.zero_mem _⟩

theorem one_mem_centralIdempotents : (1 : R) ∈ centralIdempotents R :=
  ⟨IsIdempotentElem.one, Subring.one_mem _⟩

section Congr

/-- A ring isomorphism preserves central idempotents. -/
theorem map_mem_centralIdempotents (f : R ≃+* S) {e : R} (he : e ∈ centralIdempotents R) :
    f e ∈ centralIdempotents S :=
  ⟨he.1.map f, MulEquivClass.apply_mem_center f he.2⟩

/-- **A ring isomorphism restricts to a bijection of central idempotents.** -/
def centralIdempotentsCongr (f : R ≃+* S) : centralIdempotents R ≃ centralIdempotents S where
  toFun e := ⟨f e, map_mem_centralIdempotents f e.2⟩
  invFun e := ⟨f.symm e, map_mem_centralIdempotents f.symm e.2⟩
  left_inv e := Subtype.ext (f.symm_apply_apply e)
  right_inv e := Subtype.ext (f.apply_symm_apply e)

@[simp]
theorem coe_centralIdempotentsCongr_apply (f : R ≃+* S) (e : centralIdempotents R) :
    (centralIdempotentsCongr f e : S) = f e := (rfl)

@[simp]
theorem coe_centralIdempotentsCongr_symm_apply (f : R ≃+* S) (e : centralIdempotents S) :
    ((centralIdempotentsCongr f).symm e : R) = f.symm e := (rfl)

/-- Isomorphic rings have the same number of central idempotents. -/
theorem card_centralIdempotents_congr (f : R ≃+* S) :
    Nat.card (centralIdempotents R) = Nat.card (centralIdempotents S) :=
  Nat.card_congr (centralIdempotentsCongr f)

end Congr

section Pi

variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)]

/-- Both halves of being a central idempotent are coordinatewise conditions on a product of
rings. -/
@[simp]
theorem mem_centralIdempotents_pi {e : ∀ i, A i} :
    e ∈ centralIdempotents (∀ i, A i) ↔ ∀ i, e i ∈ centralIdempotents (A i) := by
  have hcenter : e ∈ Subring.center (∀ i, A i) ↔ ∀ i, e i ∈ Subring.center (A i) := by
    rw [← SetLike.mem_coe, Subring.coe_center, Set.center_pi, Set.mem_univ_pi]
    exact forall_congr' fun _ => Iff.rfl
  simp only [mem_centralIdempotents, hcenter, IsIdempotentElem, funext_iff, Pi.mul_apply,
    ← forall_and]

/-- **The central idempotents of a product of rings are the families of central idempotents.** -/
def centralIdempotentsPiEquiv :
    centralIdempotents (∀ i, A i) ≃ ∀ i, centralIdempotents (A i) :=
  (Equiv.subtypeEquivRight fun _ => mem_centralIdempotents_pi A).trans Equiv.subtypePiEquivPi

@[simp]
theorem coe_centralIdempotentsPiEquiv_apply (e : centralIdempotents (∀ i, A i)) (i : ι) :
    (centralIdempotentsPiEquiv A e i : A i) = (e : ∀ i, A i) i := (rfl)

@[simp]
theorem coe_centralIdempotentsPiEquiv_symm_apply (e : ∀ i, centralIdempotents (A i)) (i : ι) :
    ((centralIdempotentsPiEquiv A).symm e : ∀ i, A i) i = (e i : A i) := (rfl)

/-- The number of central idempotents is multiplicative over a finite product of rings. -/
theorem card_centralIdempotents_pi [Fintype ι] :
    Nat.card (centralIdempotents (∀ i, A i)) = ∏ i, Nat.card (centralIdempotents (A i)) :=
  (Nat.card_congr (centralIdempotentsPiEquiv A)).trans Nat.card_pi

end Pi

section IsSimpleRing

variable (R) in
/-- **A simple ring has exactly two central idempotents, `0` and `1`.**

A central idempotent of `R` is exactly an idempotent of the subring `Subring.center R`, which is a
field because `R` is simple (`IsSimpleRing.isField_center`); and a field has no idempotents besides
`0` and `1` (`IsIdempotentElem.iff_eq_zero_or_one`). -/
theorem centralIdempotents_eq_pair [IsSimpleRing R] : centralIdempotents R = {0, 1} := by
  let _ := (IsSimpleRing.isField_center R).toField
  refine Set.eq_of_subset_of_subset (fun e he => ?_) ?_
  · have hidem : IsIdempotentElem (⟨e, he.2⟩ : Subring.center R) := Subtype.ext he.1
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
    · exact Or.inl (by simpa [Subtype.ext_iff] using h)
    · exact Or.inr (by simpa [Subtype.ext_iff] using h)
  · rintro e (rfl | rfl)
    · exact zero_mem_centralIdempotents
    · exact one_mem_centralIdempotents

variable (R) in
/-- A simple ring has exactly two central idempotents. -/
theorem card_centralIdempotents_of_isSimpleRing [IsSimpleRing R] :
    Nat.card (centralIdempotents R) = 2 := by
  rw [centralIdempotents_eq_pair R, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]

/-- A finite product of simple rings has `2 ^ (number of factors)` central idempotents: one
independent binary choice per factor. -/
theorem card_centralIdempotents_pi_of_isSimpleRing {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)] :
    Nat.card (centralIdempotents (∀ i, A i)) = 2 ^ Nat.card ι := by
  have := Fintype.ofFinite ι
  rw [card_centralIdempotents_pi A, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.prod_const]
  exact Finset.prod_congr rfl fun i _ => card_centralIdempotents_of_isSimpleRing (A i)

end IsSimpleRing

/-! ### A surjection onto a simple ring from a product of two copies of an algebra -/

section ProdSurjection

variable {F A B : Type*} [CommSemiring F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]

/-- The images of the two coordinate units of `A × A` add up to the unit of `B`. -/
private theorem map_one_zero_add_map_zero_one (φ : (A × A) →ₐ[F] B) :
    φ (1, 0) + φ (0, 1) = 1 := by
  have hone : ((1, 0) + (0, 1) : A × A) = 1 := by simp [Prod.ext_iff]
  rw [← map_add, hone, map_one]

/-- The coordinate map `a ↦ φ (a, 0)` attached to an algebra map out of `A × A`, packaged as an
algebra map once the image of `(1, 0)` is known to be the unit. It is multiplicative and linear for
every `φ`; unitality is exactly the hypothesis. -/
private def prodFirstAlgHom (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1) : A →ₐ[F] B where
  toFun a := φ (a, 0)
  map_one' := hu
  map_mul' a a' := by rw [← map_mul]; congr 1; simp
  map_zero' := map_zero φ
  map_add' a a' := by rw [← map_add]; congr 1; simp
  commutes' r := by
    have hr : ((algebraMap F A r : A), (0 : A)) = algebraMap F (A × A) r * (1, 0) := by
      simp [Prod.algebraMap_apply]
    rw [hr, map_mul, AlgHom.commutes, hu, mul_one]

/-- The first coordinate map is what its name says: `a ↦ φ (a, 0)`. -/
private theorem prodFirstAlgHom_apply (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1) (a : A) :
    prodFirstAlgHom φ hu a = φ (a, 0) := (rfl)

/-- If the image of `(1, 0)` is the unit then the first coordinate map is surjective as soon as `φ`
is: the image of `(0, 1)` is then complementary to `1`, so it vanishes, and with it the whole
second coordinate. -/
private theorem prodFirstAlgHom_surjective (φ : (A × A) →ₐ[F] B) (hu : φ (1, 0) = 1)
    (hφ : Function.Surjective φ) : Function.Surjective (prodFirstAlgHom φ hu) := by
  have hw : φ (0, 1) = 0 := by
    have hsum := map_one_zero_add_map_zero_one φ
    rw [hu] at hsum
    simpa using hsum
  intro b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hφ b
  refine ⟨a₁, ?_⟩
  have hsplit : ((a₁, a₂) : A × A) = (a₁, 0) + (0, a₂) * (0, 1) := by simp
  rw [prodFirstAlgHom_apply, hsplit, map_add, map_mul, hw, mul_zero, add_zero]

/-- **A surjection onto a simple ring from a product of two copies of an algebra factors through a
coordinate.** The image of `(1, 0)` is a central idempotent of `B`, hence `0` or `1`
(`TauCeti.centralIdempotents_eq_pair`); whichever it is, one of the two coordinate maps
`a ↦ φ (a, 0)`, `a ↦ φ (0, a)` is an algebra map onto `B`.

This is what turns a two-block splitting of an algebra into a statement about a single block; it is
used that way for an odd-dimensional Clifford algebra in
`TauCeti/RepresentationTheory/Spin/OddStructure.lean`. -/
theorem exists_algHom_surjective_of_prod [IsSimpleRing B] (φ : (A × A) →ₐ[F] B)
    (hφ : Function.Surjective φ) : ∃ ψ : A →ₐ[F] B, Function.Surjective ψ := by
  -- The swap of the two factors, used to reduce the second case to the first.
  set swap : (A × A) →ₐ[F] (A × A) := (AlgHom.snd F A A).prod (AlgHom.fst F A A) with hswap
  have hidem : IsIdempotentElem (φ (1, 0)) := by
    have hsq : ((1 : A), (0 : A)) * (1, 0) = (1, 0) := by simp
    calc φ (1, 0) * φ (1, 0) = φ ((1, 0) * (1, 0)) := (map_mul φ _ _).symm
      _ = φ (1, 0) := by rw [hsq]
  have hmem : φ (1, 0) ∈ centralIdempotents B := by
    refine mem_centralIdempotents.mpr ⟨hidem, Subring.mem_center_iff.mpr fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hφ x
    rw [← map_mul, ← map_mul]
    congr 1
    simp [Prod.ext_iff]
  have hpair := centralIdempotents_eq_pair (R := B) ▸ hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
  rcases hpair with h | h
  · -- `φ (1, 0) = 0`, so `φ (0, 1) = 1` and the *second* coordinate is the surjective one.
    have hw : φ (0, 1) = 1 := by
      have hsum := map_one_zero_add_map_zero_one φ
      rwa [h, zero_add] at hsum
    have hswapone : swap (1, 0) = ((0 : A), (1 : A)) := by simp [hswap]
    have hu : (φ.comp swap) (1, 0) = 1 := by
      rw [AlgHom.comp_apply, hswapone, hw]
    refine ⟨prodFirstAlgHom (φ.comp swap) hu, prodFirstAlgHom_surjective _ hu fun b => ?_⟩
    obtain ⟨⟨a₁, a₂⟩, ha⟩ := hφ b
    exact ⟨(a₂, a₁), by simpa [hswap] using ha⟩
  · exact ⟨prodFirstAlgHom φ h, prodFirstAlgHom_surjective φ h hφ⟩

end ProdSurjection

end TauCeti
