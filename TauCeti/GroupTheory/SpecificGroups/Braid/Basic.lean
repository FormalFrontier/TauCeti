/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support
public import TauCeti.GroupTheory.Presentation.Relator

/-!
# Artin Braid Groups

The Artin braid group on `n` strands, $B_n$, is the group defined by generators
$\sigma_0, \sigma_1, \dots, \sigma_{n-2}$ (indexed by `Fin (n - 1)`) and relations:
- $\sigma_i \sigma_j = \sigma_j \sigma_i$ whenever $|i - j| \ge 2$ (far commutation),
- $\sigma_i \sigma_{i+1} \sigma_i = \sigma_{i+1} \sigma_i \sigma_{i+1}$ (adjacent braid relation).

This provides the algebraic foundation for the braid presentation of knots and links requested by
Layer 4 ("knot theory, done properly") of the geometric-topology roadmap. Signed braid words reuse
`TauCeti.PresentationWord` from `TauCeti.GroupTheory.Presentation.Relator`
(adapted there from the roadmap's `TauCetiRoadmap/CFSGStatement/Suggested.lean`).

## Main definitions

* `TauCeti.ArtinRelation n`: the Artin relations in `FreeGroup (Fin (n - 1))`.
* `TauCeti.artinRelations n`: the corresponding set of relators.
* `TauCeti.BraidGroup n`: the Artin braid group $B_n$.
* `TauCeti.BraidGroup.sigma i`: the standard generator $\sigma_i$.
* `TauCeti.BraidGroup.lift`: the universal property of the Artin presentation.
* `TauCeti.BraidGroup.exponentSumHom`: the exponent-sum homomorphism.
* `TauCeti.BraidGroup.permHom`: the canonical permutation homomorphism.
* `TauCeti.BraidGroup.pureBraidGroup n`: the subgroup of pure braids.
* `TauCeti.BraidGroup.castLE`: the homomorphism adjoining unbraided strands.

## Main results

* `TauCeti.BraidGroup.sigma_def`: definition of standard generators as presented-group generators.
* `TauCeti.BraidGroup.sigma_comm`: far generators commute.
* `TauCeti.BraidGroup.sigma_braid`: adjacent generators satisfy the braid relation.
* `TauCeti.BraidGroup.lift_sigma`: the universal lift agrees with its generator map.
* `TauCeti.BraidGroup.hom_ext`: homomorphisms from a braid group agree if they agree on generators.
* `TauCeti.BraidGroup.orderOf_sigma`: standard braid generators have infinite order.

## References

* E. Artin, *Theorie der Zöpfe*, Abh. Math. Sem. Univ. Hamburg 4 (1925), 47–72.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Chapter 1.
-/

public section

namespace TauCeti

open PresentedGroup Equiv Perm

/-- The defining relations for the Artin braid group on `n` strands in
`FreeGroup (Fin (n - 1))`.

The `comm` constructor gives far commutation in one ordering; symmetry in the presented group is
provided by `BraidGroup.sigma_comm`. The `braid` constructor gives the adjacent braid relation.
-/
inductive ArtinRelation (n : ℕ) : FreeGroup (Fin (n - 1)) → Prop
  | comm (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1) :
      ArtinRelation n (FreeGroup.of i * FreeGroup.of j *
        (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹)
  | braid (i j : Fin (n - 1)) (h : i.1 + 1 = j.1) :
      ArtinRelation n (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)

/-- The set of defining relations for the Artin braid group $B_n$. -/
def artinRelations (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  { r | ArtinRelation n r }

/-- Membership in `artinRelations n` is exactly the predicate `ArtinRelation n`. -/
@[simp]
theorem mem_artinRelations {n : ℕ} {r : FreeGroup (Fin (n - 1))} :
    r ∈ artinRelations n ↔ ArtinRelation n r :=
  Iff.rfl

/-- The Artin braid group $B_n$ on `n` strands, presented by generators `Fin (n - 1)` and the
relations `artinRelations n`. -/
abbrev BraidGroup (n : ℕ) : Type _ :=
  PresentedGroup (artinRelations n)

namespace BraidGroup

variable {n : ℕ}

/-- The standard generator $\sigma_i$ ($0 \le i < n - 1$) of the braid group $B_n$. -/
def sigma (i : Fin (n - 1)) : BraidGroup n :=
  PresentedGroup.of i

/-- Definition of the standard generator `sigma i` as `PresentedGroup.of i`. -/
theorem sigma_def (i : Fin (n - 1)) :
    sigma i = PresentedGroup.of i := by
  unfold sigma
  rfl

/-- Bridge identifying the standard generator with its canonical representative
in `PresentedGroup`. -/
private theorem sigma_eq_mk (i : Fin (n - 1)) :
    sigma i = PresentedGroup.mk (artinRelations n) (FreeGroup.of i) :=
  rfl

private theorem sigma_comm_ordered (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1) :
    sigma i * sigma j = sigma j * sigma i := by
  have hmem : FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
      (FreeGroup.of j)⁻¹ ∈ artinRelations n :=
    mem_artinRelations.mpr (ArtinRelation.comm i j h)
  have hrel : sigma i * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹ = 1 := by
    simpa only [sigma_eq_mk, map_mul, map_inv] using PresentedGroup.one_of_mem hmem
  rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at hrel
  exact hrel

/-- Far generators commute whenever their indices differ by at least two, in either order. -/
theorem sigma_comm (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1 ∨ j.1 + 2 ≤ i.1) :
    sigma i * sigma j = sigma j * sigma i := by
  rcases h with h | h
  · exact sigma_comm_ordered i j h
  · exact (sigma_comm_ordered j i h).symm

private theorem sigma_braid_ordered (i j : Fin (n - 1)) (h : i.1 + 1 = j.1) :
    sigma i * sigma j * sigma i = sigma j * sigma i * sigma j := by
  have hmem : FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹ ∈ artinRelations n :=
    mem_artinRelations.mpr (ArtinRelation.braid i j h)
  have hrel := PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem
  simpa only [sigma_eq_mk, map_mul] using hrel

/-- Adjacent generators satisfy the Artin braid relation, in either index order. -/
theorem sigma_braid (i j : Fin (n - 1)) (h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
    sigma i * sigma j * sigma i = sigma j * sigma i * sigma j := by
  rcases h with h | h
  · exact sigma_braid_ordered i j h
  · exact (sigma_braid_ordered j i h).symm

/-- The universal homomorphism from `BraidGroup n`: a map on generators descends when it satisfies
far commutation and the adjacent braid relation. -/
def lift {G : Type*} [Group G] (f : Fin (n - 1) → G)
    (hcomm : ∀ i j, i.1 + 2 ≤ j.1 → f i * f j = f j * f i)
    (hbraid : ∀ i j, i.1 + 1 = j.1 → f i * f j * f i = f j * f i * f j) :
    BraidGroup n →* G :=
  PresentedGroup.toGroup (by
    intro r hr
    rw [mem_artinRelations] at hr
    rcases hr with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm i j h
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      exact hbraid i j h)

/-- The universal lift sends each braid generator to the prescribed element. -/
@[simp]
theorem lift_sigma {G : Type*} [Group G] (f : Fin (n - 1) → G) (hcomm) (hbraid)
    (i : Fin (n - 1)) : lift f hcomm hbraid (sigma i) = f i :=
  PresentedGroup.toGroup.of _

/-- Two homomorphisms from `BraidGroup n` are equal if they agree on every standard generator. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] {φ ψ : BraidGroup n →* G}
    (h : ∀ i, φ (sigma i) = ψ (sigma i)) : φ = ψ :=
  PresentedGroup.ext h

/-- The standard generators generate the whole braid group. -/
@[simp]
theorem closure_range_sigma : Subgroup.closure (Set.range (@sigma n)) = ⊤ :=
  PresentedGroup.closure_range_of (artinRelations n)

/-- The exponent-sum homomorphism, sending every generator to `Multiplicative.ofAdd 1`, i.e. the
integer `1` written multiplicatively. -/
def exponentSumHom (n : ℕ) : BraidGroup n →* Multiplicative ℤ :=
  lift (fun _ ↦ Multiplicative.ofAdd 1) (fun _ _ _ ↦ mul_comm _ _)
    (fun _ _ _ ↦ by simp only [← ofAdd_add])

/-- The exponent sum of a standard generator is the integer `1`, written multiplicatively. -/
@[simp]
theorem exponentSumHom_sigma (i : Fin (n - 1)) :
    exponentSumHom n (sigma i) = Multiplicative.ofAdd 1 := by
  simp [exponentSumHom]

private def strand (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, by omega⟩

private def nextStrand (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by omega⟩

@[simp]
private theorem strand_val (i : Fin (n - 1)) : (strand i).1 = i.1 :=
  rfl

@[simp]
private theorem nextStrand_val (i : Fin (n - 1)) : (nextStrand i).1 = i.1 + 1 :=
  rfl

private theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  calc
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
        Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
      rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
    _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hbc.symm hac.symm
    _ = Equiv.swap c a := Equiv.swap_comm _ _
    _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
      (Equiv.swap_mul_swap_mul_swap hab hac).symm

private def permGen (n : ℕ) (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap (strand i) (nextStrand i)

private theorem permGen_comm (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1) :
    permGen n i * permGen n j = permGen n j * permGen n i := by
  have hab : strand i ≠ nextStrand i := by simp [Fin.ext_iff]
  have hac : strand i ≠ strand j := by simp [Fin.ext_iff]; omega
  have had : strand i ≠ nextStrand j := by simp [Fin.ext_iff]; omega
  have hbc : nextStrand i ≠ strand j := by simp [Fin.ext_iff]; omega
  have hbd : nextStrand i ≠ nextStrand j := by simp [Fin.ext_iff]; omega
  have hcd : strand j ≠ nextStrand j := by simp [Fin.ext_iff]
  exact (Equiv.Perm.disjoint_swap_swap (by simp [hab, hac, had, hbc, hbd, hcd])).commute.eq

private theorem permGen_braid (i j : Fin (n - 1)) (h : i.1 + 1 = j.1) :
    permGen n i * permGen n j * permGen n i = permGen n j * permGen n i * permGen n j := by
  have hj : strand j = nextStrand i := by
    ext
    simp [h]
  rw [permGen, permGen, hj]
  have hab : strand i ≠ nextStrand i := by simp [Fin.ext_iff]
  have hbc : nextStrand i ≠ nextStrand j := by simp [Fin.ext_iff]; omega
  have hac : strand i ≠ nextStrand j := by simp [Fin.ext_iff]; omega
  exact swap_braid hab hbc hac

/-- The canonical permutation homomorphism `BraidGroup n →* Equiv.Perm (Fin n)`, sending generator
$\sigma_i$ to the transposition swapping strand $i$ and strand $i+1$. -/
def permHom (n : ℕ) : BraidGroup n →* Equiv.Perm (Fin n) :=
  lift (permGen n) permGen_comm permGen_braid

/-- The canonical permutation homomorphism sends `sigma i` to the adjacent transposition. -/
@[simp]
theorem permHom_sigma (i : Fin (n - 1)) :
    permHom n (sigma i) =
      Equiv.swap ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ := by
  simp [permHom, permGen, strand, nextStrand]

/-- The subgroup of pure braids, defined as the kernel of the canonical permutation homomorphism. -/
def pureBraidGroup (n : ℕ) : Subgroup (BraidGroup n) :=
  (permHom n).ker

/-- A braid is pure if and only if its permutation representation is the identity. -/
@[simp]
theorem mem_pureBraidGroup {b : BraidGroup n} : b ∈ pureBraidGroup n ↔ permHom n b = 1 :=
  MonoidHom.mem_ker

/-- The pure braid subgroup is normal. -/
instance pureBraidGroup_normal : (pureBraidGroup n).Normal :=
  (permHom n).normal_ker

/-- The square of every standard generator is a pure braid. -/
theorem sigma_sq_mem_pureBraidGroup (i : Fin (n - 1)) : sigma i ^ 2 ∈ pureBraidGroup n := by
  rw [mem_pureBraidGroup, map_pow, permHom_sigma, pow_two, Equiv.swap_mul_self]

/-- The exponent-sum homomorphism sends integer powers of standard generators to their exponent. -/
@[simp]
theorem exponentSumHom_sigma_zpow (i : Fin (n - 1)) (k : ℤ) :
    exponentSumHom n (sigma i ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, exponentSumHom_sigma, ← ofAdd_zsmul, zsmul_one, Int.cast_id]

/-- An integer power of a standard generator is trivial if and only if the exponent is zero. -/
@[simp]
theorem sigma_zpow_eq_one_iff (i : Fin (n - 1)) (k : ℤ) :
    sigma i ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    have hsum : exponentSumHom n (sigma i ^ k) = 1 := by rw [h, map_one]
    rw [exponentSumHom_sigma_zpow] at hsum
    exact Multiplicative.ofAdd.injective hsum
  · rintro rfl
    exact zpow_zero _

/-- A natural power of a standard generator is trivial if and only if the exponent is zero. -/
@[simp]
theorem sigma_pow_eq_one_iff (i : Fin (n - 1)) (k : ℕ) :
    sigma i ^ k = 1 ↔ k = 0 := by
  rw [← zpow_natCast, sigma_zpow_eq_one_iff, Int.natCast_eq_zero]

/-- Every standard generator has infinite order. -/
@[simp]
theorem orderOf_sigma (i : Fin (n - 1)) : orderOf (sigma i) = 0 :=
  orderOf_eq_zero_iff'.mpr fun k hk => (sigma_pow_eq_one_iff i k).not.mpr (ne_of_gt hk)

/-- The standard generator is nontrivial. -/
@[simp]
theorem sigma_ne_one (i : Fin (n - 1)) : sigma i ≠ 1 := by
  intro h
  have : (1 : ℕ) = 0 := (sigma_pow_eq_one_iff i 1).mp (by rwa [pow_one])
  omega

/-- For `h : m ≤ n`, the homomorphism `BraidGroup m →* BraidGroup n` which adjoins `n - m`
unbraided strands and sends each standard generator to the generator with the same index. -/
def castLE {m n : ℕ} (h : m ≤ n) : BraidGroup m →* BraidGroup n :=
  lift (fun i ↦ sigma ⟨i.1, by omega⟩)
    (fun i j hij ↦ sigma_comm _ _ (Or.inl hij))
    (fun i j hij ↦ sigma_braid _ _ (Or.inl hij))

/-- Adjoining strands preserves every standard generator. -/
@[simp]
theorem castLE_sigma {m n : ℕ} (h : m ≤ n) (i : Fin (m - 1)) :
    castLE h (sigma i) = sigma ⟨i.1, by omega⟩ := by
  simp [castLE]

/-- Adjoining no strands is the identity homomorphism. -/
@[simp]
theorem castLE_rfl (n : ℕ) : castLE (Nat.le_refl n) = MonoidHom.id (BraidGroup n) := by
  apply hom_ext
  intro i
  simp

/-- Successively adjoining strands agrees with adjoining all of them at once. -/
@[simp]
theorem castLE_comp_castLE {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    (castLE hmn).comp (castLE hlm) = castLE (hlm.trans hmn) := by
  apply hom_ext
  intro i
  simp

end BraidGroup

end TauCeti
