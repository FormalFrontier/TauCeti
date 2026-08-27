/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.RootSystem.FiniteType.Bounded
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

public section

/-!
# The weight cone below a weight is finite once it is stable under the simple reflections

Fix a base `b` of a finite crystallographic root system `P` and a weight `lam`. The set of weights
lying **below** `lam`, that is those `mu` with `lam - mu` in the positive root cone `Q⁺`, is
infinite: it is a whole translated cone. This file proves that two further conditions cut it down
to a finite set.

* **Dominance.** Only finitely many `mu` below `lam` take a natural value on every simple coroot
  (`TauCeti.finite_setOf_dominant_sub_mem_posRootCone`). This is the classical statement that a
  dominant weight below `lam` is bounded, and it comes straight from positive definiteness of the
  symmetrized Cartan matrix, in the form given in
  `TauCeti/LinearAlgebra/RootSystem/FiniteType/Bounded.lean`.
* **Stability under the simple reflections.** A set of weights below `lam` on which every simple
  coroot takes integer values and which is carried into itself by every simple reflection is
  finite (`TauCeti.finite_of_forall_reflection_mem_of_sub_mem_posRootCone`). Stability replaces
  dominance: a non-dominant member is raised by a simple reflection to another member strictly
  closer to `lam`, so it is a Weyl translate of a dominant member, and the Weyl group is finite.

The second statement is the shape the representation theory needs. The weights of an irreducible
highest weight module of dominant integral highest weight `lam` lie in `lam - Q⁺`, take integer
values on the simple coroots and are stable under the simple reflections, none of which presupposes
that the module is finite-dimensional; the theorem below turns those three facts into finiteness of
the weight support.

## Main results

* `TauCeti.finite_setOf_dominant_sub_mem_posRootCone`: **only finitely many dominant weights lie
  below a given weight.**
* `TauCeti.finite_of_forall_reflection_mem_of_sub_mem_posRootCone`: **a set of weights below `lam`,
  integral on the simple coroots and stable under the simple reflections, is finite.**

## The argument

Writing `lam - mu = ∑ j, c j • αⱼ` with natural coefficients `c j`, the value of `mu` on the simple
coroot `αᵢ^∨` is `lam (αᵢ^∨) - ∑ j, c j * ⟨αⱼ, αᵢ^∨⟩`. Dominance therefore says that the natural
vector `c` solves the Cartan inequality of the transposed Cartan matrix, whose solution set is
finite; the right-hand side of the inequality is manufactured from one member of the set, which is
why the argument begins by disposing of the empty case.

For the second statement, if `mu` is a member on which `αᵢ^∨` takes a negative value, then
`sᵢ mu = mu - ⟨mu, αᵢ^∨⟩ αᵢ` is again a member and `lam - sᵢ mu` has strictly smaller height: the
simple roots are linearly independent, so the coefficient vectors of the two differences agree
except at `i`, where the coefficient drops by `-⟨mu, αᵢ^∨⟩ ≥ 1`. Induction on that height therefore
writes every member as a Weyl translate of a dominant member.

## References

This is the root-system content of the "weight-cone bound" milestone of Layer 4, "the
classification of finite-dimensional irreducibles", of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2 and
  §21.2.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
  [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base)

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] in
/-- The value of a simple coroot on a natural combination of the simple roots, as an integer read
off the Cartan matrix. -/
private theorem coroot'_sum_nsmul_root (f : ι → ℕ) (i : ι) :
    P.coroot' i (∑ j ∈ b.support, f j • P.root j)
      = ((∑ j : b.support, P.pairingIn ℤ j i * (f j : ℤ) : ℤ) : R) := by
  have hpair : ∀ p q : ι, ((P.pairingIn ℤ p q : ℤ) : R) = P.pairing p q := by
    intro p q
    rw [← P.algebraMap_pairingIn ℤ p q]
    simp
  rw [map_sum, ← Finset.sum_coe_sort b.support fun j ↦ P.coroot' i (f j • P.root j)]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_nsmul, P.root_coroot'_eq_pairing, nsmul_eq_mul, hpair]
  ring

/-- **Only finitely many dominant weights lie below a given weight.** For a base `b` of a finite
crystallographic root system and a weight `lam`, only finitely many `mu` satisfy both that
`lam - mu` is a nonnegative integer combination of the simple roots and that every simple coroot
takes a natural value on `mu`.

The two hypotheses pull in opposite directions: the first writes `lam - mu` as `∑ j, c j • αⱼ` with
`c j` natural, and the second bounds the resulting Cartan expression `∑ j, c j ⟨αⱼ, αᵢ^∨⟩` above.
Positive definiteness of the symmetrized Cartan matrix
(`TauCeti.finite_setOf_forall_sum_mul_le`) leaves only finitely many such `c`. -/
theorem finite_setOf_dominant_sub_mem_posRootCone (lam : M) :
    {mu : M | lam - mu ∈ posRootCone P b ∧
      ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i mu = (n : R)}.Finite := by
  classical
  set D : Set M := {mu : M | lam - mu ∈ posRootCone P b ∧
    ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i mu = (n : R)}
  rcases D.eq_empty_or_nonempty with hempty | ⟨mu₀, hmu₀⟩
  · rw [hempty]
    exact Set.finite_empty
  -- The right-hand side of the Cartan inequality is read off a chosen member of the set.
  choose n₀ hn₀ using fun i : b.support ↦ hmu₀.2 i i.2
  obtain ⟨f₀, hf₀⟩ := (mem_posRootCone P b).mp hmu₀.1
  set y : b.support → ℤ :=
    fun i ↦ (n₀ i : ℤ) + ∑ j : b.support, P.pairingIn ℤ j i * (f₀ j : ℤ) with hydef
  have hlam : ∀ i : b.support, P.coroot' i lam = ((y i : ℤ) : R) := by
    intro i
    have h := coroot'_sum_nsmul_root b f₀ i
    rw [← hf₀, map_sub] at h
    have hsplit : P.coroot' i lam
        = P.coroot' i mu₀ + ((∑ j : b.support, P.pairingIn ℤ j i * (f₀ j : ℤ) : ℤ) : R) := by
      rw [← h]
      ring
    rw [hsplit, hn₀ i]
    simp only [hydef]
    push_cast
    ring
  obtain ⟨d, hd, hpd⟩ := (isFiniteType_cartanMatrix b).transpose.exists_symmetrizer
  refine Set.Finite.subset
    ((finite_setOf_forall_sum_mul_le d hd hpd y).image
      fun c : b.support → ℕ ↦ lam - ∑ j : b.support, c j • P.root j) ?_
  rintro mu ⟨hcone, hdom⟩
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp hcone
  choose n hn using fun i : b.support ↦ hdom i i.2
  refine ⟨fun j : b.support ↦ f j, fun i ↦ ?_, ?_⟩
  · have h := coroot'_sum_nsmul_root b f i
    rw [← hf, map_sub, hlam i, hn i] at h
    have hcast : ((∑ j : b.support, P.pairingIn ℤ j i * (f j : ℤ) : ℤ) : R)
        = ((y i - n i : ℤ) : R) := by
      rw [← h]
      push_cast
      ring
    have heqZ := Int.cast_injective (α := R) hcast
    simp only [Matrix.transpose_apply, RootPairing.Base.cartanMatrixIn_def]
    rw [heqZ]
    omega
  · rw [← Finset.sum_coe_sort b.support fun j ↦ f j • P.root j] at hf
    dsimp only
    rw [← hf]
    abel

/-- **A reflection-stable set of weights below a weight is finite.** Let `S` be a set of weights
with `lam - mu` in the positive root cone for every `mu ∈ S`, on which every simple coroot takes
integer values, and which every simple reflection carries into itself. Then `S` is finite.

Stability is what replaces dominance in
`TauCeti.finite_setOf_dominant_sub_mem_posRootCone`: a member on which some simple coroot is
negative is moved by the corresponding reflection to a member strictly closer to `lam`, so
induction on the height of `lam - mu` exhibits every member as a Weyl translate of a dominant
member, and both the dominant members and the Weyl group are finite. -/
theorem finite_of_forall_reflection_mem_of_sub_mem_posRootCone {lam : M} {S : Set M}
    (hcone : ∀ mu ∈ S, lam - mu ∈ posRootCone P b)
    (hint : ∀ mu ∈ S, ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i mu = (z : R))
    (hrefl : ∀ mu ∈ S, ∀ i ∈ b.support, P.reflection i mu ∈ S) :
    S.Finite := by
  classical
  have : Finite P.weylGroup := RootPairing.finite_weylGroup P
  set D : Set M := {mu : M | lam - mu ∈ posRootCone P b ∧
    ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i mu = (n : R)}
  set T : Set M := ⋃ w : P.weylGroup, (fun x ↦ w • x) '' D with hTdef
  have hT : T.Finite :=
    Set.finite_iUnion fun w ↦ (finite_setOf_dominant_sub_mem_posRootCone b lam).image _
  -- The union of the Weyl translates of the dominant members is reflection stable.
  have hTrefl : ∀ (i : ι) (x : M), x ∈ T → P.reflection i x ∈ T := by
    intro i x hx
    simp only [hTdef, Set.mem_iUnion, Set.mem_image] at hx ⊢
    obtain ⟨w, v, hv, rfl⟩ := hx
    refine ⟨RootPairing.weylGroup.ofIdx P i * w, v, hv, ?_⟩
    rw [mul_smul]
    simp
  -- The simple roots are linearly independent, so the coefficients of a member are determined.
  have hli : LinearIndepOn ℤ P.root (b.support : Set ι) :=
    b.linearIndepOn_root.restrict_scalars' ℤ
  have main : ∀ k : ℕ, ∀ mu ∈ S, ∀ f : ι → ℕ,
      lam - mu = ∑ j ∈ b.support, f j • P.root j → ∑ j ∈ b.support, f j = k → mu ∈ T := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro mu hmu f hf hsum
      by_cases hdom : ∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i mu = (n : R)
      · exact Set.mem_iUnion.mpr ⟨1, mu, ⟨hcone mu hmu, hdom⟩, one_smul _ _⟩
      push Not at hdom
      obtain ⟨i, hi, hnotnat⟩ := hdom
      obtain ⟨z, hz⟩ := hint mu hmu i hi
      have hzneg : z < 0 := by
        by_contra hc
        push Not at hc
        refine hnotnat z.toNat ?_
        rw [hz, ← Int.cast_natCast (R := R) z.toNat, Int.toNat_of_nonneg hc]
      -- Reflecting in `αᵢ` raises `mu`, so it lowers the height of `lam - mu`.
      have hnu : P.reflection i mu ∈ S := hrefl mu hmu i hi
      obtain ⟨g, hg⟩ := (mem_posRootCone P b).mp (hcone _ hnu)
      have hrel : ∑ j ∈ b.support, (g j : ℤ) • P.root j
          = ∑ j ∈ b.support, (f j : ℤ) • P.root j + z • P.root i := by
        have h₁ : lam - P.reflection i mu = (lam - mu) + z • P.root i := by
          rw [P.reflection_apply, hz, Int.cast_smul_eq_zsmul]
          abel
        simp only [natCast_zsmul]
        rw [← hg, h₁, hf]
      have hcoeff : ∀ j ∈ b.support,
          ((g j : ℤ) - (f j : ℤ) - (if j = i then z else 0)) = 0 := by
        refine linearIndepOn_iff'.mp hli b.support _ subset_rfl ?_
        have hsingle : ∑ j ∈ b.support, (if j = i then z else 0) • P.root j = z • P.root i := by
          rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) fun hni ↦ absurd hi hni]
          simp
        simp only [sub_smul]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsingle, hrel]
        abel
      have hgsum : ((∑ j ∈ b.support, g j : ℕ) : ℤ) = ((∑ j ∈ b.support, f j : ℕ) : ℤ) + z := by
        have hsplit : ∀ j ∈ b.support, (g j : ℤ) = (f j : ℤ) + (if j = i then z else 0) := by
          intro j hj
          have := hcoeff j hj
          omega
        push_cast
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) fun hni ↦ absurd hi hni]
        simp
      have hlt : ∑ j ∈ b.support, g j < k := by omega
      have hmem := ih _ hlt _ hnu g hg rfl
      have hback : P.reflection i (P.reflection i mu) = mu := P.reflection_same i mu
      exact hback ▸ hTrefl i _ hmem
  refine hT.subset fun mu hmu ↦ ?_
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp (hcone mu hmu)
  exact main _ mu hmu f hf rfl

end TauCeti
