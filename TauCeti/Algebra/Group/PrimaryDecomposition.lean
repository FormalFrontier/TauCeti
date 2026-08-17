/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Torsion

/-!
# Primary decomposition of finite abelian groups

This file packages the canonical decomposition of a finite abelian group as the product of its
prime-primary components. The equivalence sends a tuple of primary elements to their sum in the
ambient group.

The proof follows the cardinality argument used by Mathlib's `Sylow.directProductOfNormal`:
primary components for distinct primes have coprime cardinalities, and the product of those
cardinalities is the cardinality of the group. We pass through the multiplicative avatar of the
group only to reuse `Sylow.card_eq_multiplicity`; the resulting equivalence is entirely additive
and uses Mathlib's canonical `AddCommGroup.primaryComponent` subgroups.

## Main results

* `TauCeti.AddCommGroup.primaryDecomposition`: a finite abelian group is additively equivalent to
  the product of its prime-primary components.
* `TauCeti.AddCommGroup.primaryDecomposition_apply`: the equivalence is the sum of the component
  inclusions.

## References

* D. Gorenstein, *Finite Groups*, Chapter 1.

This is the group-theoretic input to the primary-decomposition part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

universe u

namespace AddCommGroup

variable (A : Type u) [AddCommGroup A] [Finite A]

private noncomputable def primaryComponentMulEquivSylow
    (p : (Nat.card A).primeFactors) :
    Multiplicative (AddCommGroup.primaryComponent A p.1) ≃*
      (default : Sylow p.1 (Multiplicative A)) where
  toFun x := ⟨Multiplicative.ofAdd x.toAdd.1, by
    have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    apply IsPGroup.le_sylow_of_normal
      (CommGroup.primaryComponent.isPGroup (G := Multiplicative A))
      (default : Sylow p.1 (Multiplicative A))
    rw [CommGroup.mem_primaryComponent]
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.toAdd.2
    exact ⟨k, by
      simpa only [← ofAdd_nsmul, ofAdd_zero] using (congrArg Multiplicative.ofAdd hk)⟩⟩
  invFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd x.1, by
    rw [AddCommGroup.mem_primaryComponent]
    obtain ⟨k, hk⟩ :=
      (default : Sylow p.1 (Multiplicative A)).isPGroup'.exists_pow_pow_eq_one x
    exact ⟨k, by
      have hk' := congrArg (fun y : (default : Sylow p.1 (Multiplicative A)) ↦
        Multiplicative.toAdd y.1) hk
      simpa only [SubgroupClass.coe_pow, Subgroup.coe_one, toAdd_pow, toAdd_one] using hk'⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

private theorem natCard_primaryComponent (p : (Nat.card A).primeFactors) :
    Nat.card (AddCommGroup.primaryComponent A p.1) =
      p.1 ^ (Nat.card A).factorization p.1 := by
  have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  calc
    Nat.card (AddCommGroup.primaryComponent A p.1) =
        Nat.card (Multiplicative (AddCommGroup.primaryComponent A p.1)) :=
      (Nat.card_congr Multiplicative.toAdd).symm
    _ = Nat.card (default : Sylow p.1 (Multiplicative A)) :=
      Nat.card_congr (primaryComponentMulEquivSylow A p).toEquiv
    _ = p.1 ^ (Nat.card (Multiplicative A)).factorization p.1 :=
      Sylow.card_eq_multiplicity _
    _ = p.1 ^ (Nat.card A).factorization p.1 := by
      rw [Nat.card_congr Multiplicative.toAdd]

omit [Finite A] in
private theorem primaryComponents_pairwise_addCommute :
    Pairwise fun p q : (Nat.card A).primeFactors ↦
      ∀ x y : A, x ∈ AddCommGroup.primaryComponent A p.1 →
        y ∈ AddCommGroup.primaryComponent A q.1 → AddCommute x y :=
  fun _ _ _ x y _ _ ↦ AddCommute.all x y

private noncomputable def primaryDecompositionHom :
    (∀ p : (Nat.card A).primeFactors, AddCommGroup.primaryComponent A p.1) →+ A :=
  AddSubgroup.noncommPiCoprod (primaryComponents_pairwise_addCommute A)

/-- A finite abelian group is canonically the direct product of its prime-primary components. -/
noncomputable def primaryDecomposition :
    (∀ p : (Nat.card A).primeFactors, AddCommGroup.primaryComponent A p.1) ≃+ A :=
  AddEquiv.ofBijective (primaryDecompositionHom A) (by
    classical
    let _ := Fintype.ofFinite A
    let _ : ∀ p : (Nat.card A).primeFactors,
        Fintype (AddCommGroup.primaryComponent A p.1) := fun _ ↦ Fintype.ofFinite _
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    -- Unfold the private homomorphism so the existing injectivity theorem applies to its
    -- `noncommPiCoprod` implementation.
    · change Function.Injective
        (AddSubgroup.noncommPiCoprod (primaryComponents_pairwise_addCommute A))
      apply AddSubgroup.injective_noncommPiCoprod_of_iSupIndep
      apply AddSubgroup.independent_of_coprime_order (primaryComponents_pairwise_addCommute A)
      rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
      rw [← Nat.card_eq_fintype_card, natCard_primaryComponent A ⟨p, hp⟩,
        ← Nat.card_eq_fintype_card, natCard_primaryComponent A ⟨q, hq⟩]
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr (by simpa using hpq)).pow _ _
    · simp only [← Nat.card_eq_fintype_card]
      calc
        Nat.card (∀ p : (Nat.card A).primeFactors,
            AddCommGroup.primaryComponent A p.1) =
            ∏ p : (Nat.card A).primeFactors,
              Nat.card (AddCommGroup.primaryComponent A p.1) := Nat.card_pi
        _ = ∏ p : (Nat.card A).primeFactors,
            p.1 ^ (Nat.card A).factorization p.1 := by
          congr 1 with p
          exact natCard_primaryComponent A p
        _ = ∏ p ∈ (Nat.card A).primeFactors,
            p ^ (Nat.card A).factorization p :=
          Finset.prod_finset_coe (fun p ↦ p ^ (Nat.card A).factorization p) _
        _ = (Nat.card A).factorization.prod (· ^ ·) := rfl
        _ = Nat.card A := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne')

/-- The canonical primary decomposition maps a tuple to the sum of its components. -/
@[simp]
theorem primaryDecomposition_apply (x) :
    primaryDecomposition A x = ∑ p, (x p : A) := by
  change primaryDecompositionHom A x = _
  rw [primaryDecompositionHom, AddSubgroup.noncommPiCoprod_apply,
    Finset.noncommSum_eq_sum]

end AddCommGroup

end TauCeti
