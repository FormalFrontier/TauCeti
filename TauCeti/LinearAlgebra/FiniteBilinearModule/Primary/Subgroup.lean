/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition

/-!
# Subgroups and primary decomposition of finite modules

This file proves that the subgroup calculations used with finite bilinear and quadratic modules
can be performed one prime at a time.  The `p`-primary part of a subgroup is its intersection with
the ambient `p`-primary component, regarded as a subgroup of that component.  Bilinear and
quadratic isotropy are equivalent to isotropy of all these primary parts.

Orthogonal complementation is componentwise as well: inside the restricted `p`-primary module, the
orthogonal complement of the `p`-primary part of `H` is the `p`-primary part of the orthogonal
complement of `H`.  The reverse inclusion uses the primary decomposition of `H`; components at
primes different from `p` are automatically orthogonal.

## Main results

* `TauCeti.FiniteBilinearModule.primaryPart`: the part of a subgroup in one primary component.
* `TauCeti.FiniteBilinearModule.isIsotropic_iff_primaryPart`: bilinear isotropy can be checked on
  every primary part.
* `TauCeti.FiniteQuadraticModule.isIsotropic_iff_primaryPart`: quadratic isotropy can be checked on
  every primary part.
* `TauCeti.FiniteBilinearModule.primaryPart_orthogonalComplement`: orthogonal complementation
  commutes with passage to a primary component.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This completes the componentwise-isotropy and orthogonal-complement part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- The `p`-primary part of `H`, regarded as a subgroup of the ambient `p`-primary component. -/
def primaryPart (H : AddSubgroup A) (p : ℕ) :
    AddSubgroup (AddCommGroup.primaryComponent A p) :=
  H.comap (AddCommGroup.primaryComponent A p).subtype

@[simp]
theorem mem_primaryPart_iff (H : AddSubgroup A) (p : ℕ)
    (x : AddCommGroup.primaryComponent A p) :
    x ∈ A.primaryPart H p ↔ (x : A) ∈ H :=
  Iff.rfl

private theorem coe_mem_primaryComponent_of_mem_primaryComponent
    (H : AddSubgroup A) (p : ℕ) (x : AddCommGroup.primaryComponent H p) :
    ((x : H) : A) ∈ AddCommGroup.primaryComponent A p := by
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
  exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Subtype.val hk⟩

private theorem coe_primaryDecomposition_sum (H : AddSubgroup A) (x : H) :
    (x : A) = ∑ p : (Nat.card H).primeFactors,
      (((AddCommGroup.primaryDecomposition H).symm x p : H) : A) := by
  have h := AddCommGroup.primaryDecomposition_apply H
    ((AddCommGroup.primaryDecomposition H).symm x)
  rw [AddEquiv.apply_symm_apply] at h
  simpa only [map_sum, AddSubgroup.subtype_apply] using congrArg H.subtype h

/-- A subgroup of a finite bilinear module is isotropic if and only if its part in every prime
primary component is isotropic for the restricted pairing. -/
theorem isIsotropic_iff_primaryPart (H : AddSubgroup A) :
    A.IsIsotropic H ↔
      ∀ p : ℕ, p.Prime →
        (A.restrict (AddCommGroup.primaryComponent A p)).IsIsotropic (A.primaryPart H p) := by
  constructor
  · intro hH p _
    rw [(A.restrict (AddCommGroup.primaryComponent A p)).isIsotropic_def]
    rw [A.isIsotropic_def] at hH
    intro x hx y hy
    exact hH x.1 hx y.1 hy
  · intro hprimary
    rw [A.isIsotropic_def]
    intro x hx y hy
    let xH : H := ⟨x, hx⟩
    let yH : H := ⟨y, hy⟩
    let xd := (AddCommGroup.primaryDecomposition H).symm xH
    let yd := (AddCommGroup.primaryDecomposition H).symm yH
    calc
      A.pairing x y =
          A.pairing (∑ p, ((xd p : H) : A)) (∑ p, ((yd p : H) : A)) := by
        rw [← A.coe_primaryDecomposition_sum H xH, ← A.coe_primaryDecomposition_sum H yH]
      _ = ∑ p, A.pairing ((xd p : H) : A) ((yd p : H) : A) := by
        apply A.pairing_sum_eq_sum_pairing_of_mem_primaryComponent Finset.univ Subtype.val
        · exact fun p _ ↦ Nat.prime_of_mem_primeFactors p.2
        · exact fun p _ q _ hpq ↦ by simpa using hpq
        · exact fun p _ ↦ A.coe_mem_primaryComponent_of_mem_primaryComponent H p (xd p)
        · exact fun p _ ↦ A.coe_mem_primaryComponent_of_mem_primaryComponent H p (yd p)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        let xp : AddCommGroup.primaryComponent A p.1 :=
          ⟨((xd p : H) : A), A.coe_mem_primaryComponent_of_mem_primaryComponent H p (xd p)⟩
        let yp : AddCommGroup.primaryComponent A p.1 :=
          ⟨((yd p : H) : A), A.coe_mem_primaryComponent_of_mem_primaryComponent H p (yd p)⟩
        exact (A.restrict (AddCommGroup.primaryComponent A p.1)).isIsotropic_def.mp
          (hprimary p.1 (Nat.prime_of_mem_primeFactors p.2))
          xp (xd p).1.2 yp (yd p).1.2

/-- Orthogonal complementation commutes with passage to a prime-primary component. -/
theorem primaryPart_orthogonalComplement (H : AddSubgroup A) {p : ℕ} (hp : p.Prime) :
    A.primaryPart (A.orthogonalComplement H) p =
      (A.restrict (AddCommGroup.primaryComponent A p)).orthogonalComplement
        (A.primaryPart H p) := by
  ext x
  rw [A.mem_primaryPart_iff]
  constructor
  · intro hx
    rw [(A.restrict (AddCommGroup.primaryComponent A p)).mem_orthogonalComplement_iff]
    intro y hy
    exact A.mem_orthogonalComplement_iff H x.1 |>.mp hx y.1 hy
  · intro hx
    rw [A.mem_orthogonalComplement_iff]
    intro y hy
    let yH : H := ⟨y, hy⟩
    let yd := (AddCommGroup.primaryDecomposition H).symm yH
    have hydecomp : y = ∑ q, ((yd q : H) : A) := by
      simpa only [yH, yd] using A.coe_primaryDecomposition_sum H yH
    rw [hydecomp, map_sum]
    apply Finset.sum_eq_zero
    intro q _
    have hq : q.1.Prime := Nat.prime_of_mem_primeFactors q.2
    have hyq : ((yd q : H) : A) ∈ AddCommGroup.primaryComponent A q.1 :=
      A.coe_mem_primaryComponent_of_mem_primaryComponent H q (yd q)
    by_cases hqp : q.1 = p
    · let yq : AddCommGroup.primaryComponent A p :=
        ⟨((yd q : H) : A), hqp ▸ hyq⟩
      have hyqH : yq ∈ A.primaryPart H p := (yd q).1.2
      exact (A.restrict (AddCommGroup.primaryComponent A p)).mem_orthogonalComplement_iff
        (A.primaryPart H p) x |>.mp hx yq hyqH
    · exact A.pairing_eq_zero_of_mem_primaryComponent hp hq (Ne.symm hqp) x.2 hyq

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- A subgroup of a finite quadratic module is isotropic if and only if its part in every prime
primary component is isotropic for the restricted quadratic map. -/
theorem isIsotropic_iff_primaryPart (H : AddSubgroup A) :
    A.IsIsotropic H ↔
      ∀ p : ℕ, p.Prime →
        (A.restrict (AddCommGroup.primaryComponent A p)).IsIsotropic
          (A.toFiniteBilinearModule.primaryPart H p) := by
  constructor
  · intro hH p _
    apply (A.restrict (AddCommGroup.primaryComponent A p)).isIsotropic_def.mpr
    rw [A.isIsotropic_def] at hH
    intro x hx
    exact hH x.1 hx
  · intro hprimary
    rw [A.isIsotropic_def]
    intro x hx
    let xH : H := ⟨x, hx⟩
    let xd := (AddCommGroup.primaryDecomposition H).symm xH
    calc
      A.quadratic x = A.quadratic (∑ p, ((xd p : H) : A)) := by
        rw [← A.toFiniteBilinearModule.coe_primaryDecomposition_sum H xH]
      _ = ∑ p, A.quadratic ((xd p : H) : A) := by
        apply A.quadratic_sum_of_mem_primaryComponent Finset.univ Subtype.val
        · exact fun p _ ↦ Nat.prime_of_mem_primeFactors p.2
        · exact fun p _ q _ hpq ↦ by simpa using hpq
        · exact fun p _ ↦
            A.toFiniteBilinearModule.coe_mem_primaryComponent_of_mem_primaryComponent H p (xd p)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        let xp : AddCommGroup.primaryComponent A p.1 :=
          ⟨((xd p : H) : A),
            A.toFiniteBilinearModule.coe_mem_primaryComponent_of_mem_primaryComponent H p (xd p)⟩
        exact (A.restrict (AddCommGroup.primaryComponent A p.1)).isIsotropic_def.mp
          (hprimary p.1 (Nat.prime_of_mem_primeFactors p.2)) xp (xd p).1.2

end FiniteQuadraticModule

end TauCeti
