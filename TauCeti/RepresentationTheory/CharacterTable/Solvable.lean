/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import Mathlib.GroupTheory.Solvable
import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.CharacterTable.Vanishing
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

/-!
# Burnside's `pᵃqᵇ` theorem

A finite group whose order has at most two prime divisors is solvable. The proof is the classical
character-theoretic one, and it runs through the statement that a **conjugacy class of prime-power
size larger than one forces a proper nontrivial normal subgroup**
(`TauCeti.not_isSimpleGroup_of_card_carrier_eq_prime_pow`), which is where all the representation
theory is spent.

## The class-size step

Let `g` have a conjugacy class of size `p ^ k` with `k ≠ 0`, and suppose `G` were simple. Column
orthogonality at the classes of `g` and of `1` reads `∑_χ χ(1) χ(g) = 0`, the sum being over the
irreducible characters. The trivial character contributes `1`. If every other irreducible character
either vanished at `g` or had degree divisible by `p`, the remaining terms would add up to `p` times
an algebraic integer, making `-1/p` an algebraic integer; it is rational and not an integer, so some
irreducible character `χ ≠ 1` has `χ(g) ≠ 0` and degree prime to `p`.

Its degree is then coprime to the class size, so Burnside's vanishing theorem
(`Representation.char_eq_zero_or_norm_char_eq_finrank`) applies and gives `‖χ(g)‖ = χ(1)`.
That is the equality case of the bound on a character value, so the affording representation sends
`g` to a scalar (`Representation.exists_apply_eq_smul_of_norm_char_eq_finrank`). Its kernel
is normal, hence trivial or everything: if it is everything the character is constant and row
orthogonality against the trivial character makes its degree `0`, which is absurd; and if it is
trivial the representation is faithful, so `g` commutes with everything and its class is a single
point, contradicting `k ≠ 0`.

## The induction

`TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow` follows by induction on the order. A group
with a proper nontrivial normal subgroup is solvable as soon as that subgroup and the quotient are,
and both are smaller. A simple group with no `q`-torsion is a `p`-group, hence nilpotent. Otherwise
the centre of a Sylow `q`-subgroup `Q` supplies a nontrivial `g` whose centralizer contains `Q`, so
its class has size dividing the index of `Q`, a power of `p`. A class of size one puts `g` in the
centre, which simplicity then makes all of `G`, and a larger one contradicts the class-size step.

## Main results

* `TauCeti.not_isSimpleGroup_of_card_carrier_eq_prime_pow`: **a conjugacy class of prime-power size
  larger than one forces a proper nontrivial normal subgroup.**
* `TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow`: **Burnside's `pᵃqᵇ` theorem**, that a
  finite group of order `pᵃqᵇ` is solvable, with
  `TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow` the divisibility form that the induction
  runs in.

## References

* W. Burnside, *Theory of Groups of Finite Order*, 2nd ed. (1911).
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 3.8 and its corollaries.
-/

public section

namespace TauCeti

open Module

universe u

section ClassSize

variable {G : Type u} [Group G] [Finite G]

/-- **Column orthogonality supplies a nontrivial irreducible character that neither vanishes at
`g` nor has degree divisible by `p`.** Summing the column at `g` against the column at `1` gives
`0`, and the trivial character `i₀` contributes `1`; were every other contribution `0` or a
multiple of `p`, the identity would exhibit `-1/p` as an algebraic integer. -/
private theorem exists_ne_of_not_dvd_characterDegree [Invertible (Nat.card G : ℂ)]
    {g : G} (hg1 : g ≠ 1) {p : ℕ} (hp : p.Prime)
    {i₀ : Fin (Nat.card (ConjClasses G))} (hi₀ : irreducibleCharacter ℂ i₀ = fun _ : G => (1 : ℂ)) :
    ∃ i, i ≠ i₀ ∧ irreducibleCharacter ℂ i g ≠ 0 ∧ ¬ p ∣ characterDegree ℂ i := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hd₀ : characterDegree ℂ i₀ = 1 := by
    have h1 : ((characterDegree ℂ i₀ : ℕ) : ℂ) = 1 := by
      rw [← irreducibleCharacter_one (k := ℂ) i₀, hi₀]
    exact_mod_cast h1
  have hsum : ∑ i, irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ) = 0 := by
    simpa [hg1] using sum_characterTable_mul_characterTable_inv (k := ℂ) (G := G) g 1
  by_contra hcon
  push Not at hcon
  set z : ℂ := ∑ i ∈ Finset.univ.erase i₀,
    irreducibleCharacter ℂ i g * ((characterDegree ℂ i / p : ℕ) : ℂ) with hzdef
  have hpz : (p : ℂ) * z = ∑ i ∈ Finset.univ.erase i₀,
      irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ) := by
    rw [hzdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases eq_or_ne (irreducibleCharacter ℂ i g) 0 with h0 | h0
    · rw [h0]; ring
    · have hdvd := hcon i (Finset.mem_erase.1 hi).1 h0
      have hcancel : (p : ℂ) * ((characterDegree ℂ i / p : ℕ) : ℂ)
          = (characterDegree ℂ i : ℂ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      linear_combination irreducibleCharacter ℂ i g * hcancel
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun i => irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ))
    (Finset.mem_univ i₀)).trans hsum
  rw [hi₀, hd₀] at hsplit
  have hone : (1 : ℂ) + (p : ℂ) * z = 0 := by rw [hpz]; simpa using hsplit
  have hzint : IsIntegral ℤ z := by
    rw [hzdef]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_natCast _)
    rw [← character_irreducibleRepresentation ℂ i]
    exact Representation.isIntegral_char _ (isOfFinOrder_of_finite g).orderOf_pos.ne'
      (pow_orderOf_eq_one g)
  -- `p · (-z) = 1` with `-z` an algebraic integer makes `p` divide `1`
  exact hp.ne_one (Nat.dvd_one.1 (dvd_of_isIntegral_of_natCast_mul_eq (m := 1) hzint.neg
    (by push_cast; linear_combination -hone) hp.pos.ne'))

/-- **A conjugacy class of prime-power size larger than one forces a proper normal subgroup.** If
some element of a finite group has a conjugacy class of size `p ^ k` with `p` prime and `k ≠ 0`,
then the group is not simple.

This is the character-theoretic heart of Burnside's `pᵃqᵇ` theorem: it is what a Sylow argument is
fed into. -/
theorem not_isSimpleGroup_of_card_carrier_eq_prime_pow {g : G} {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) (hcard : Nat.card (ConjClasses.mk g).carrier = p ^ k) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  let : Fintype G := Fintype.ofFinite G
  have hcardC : ((Nat.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible ((Nat.card G : ℕ) : ℂ) := invertibleOfNonzero hcardC
  have hpk : p ^ k ≠ 1 := (Nat.one_lt_pow hk hp.one_lt).ne'
  have hgcenter : g ∉ Subgroup.center G := fun hg =>
    hpk (by rw [← hcard, Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center hg])
  have hg1 : g ≠ 1 := fun h => hgcenter (by rw [h]; exact Subgroup.one_mem _)
  -- the trivial character, and its index in the enumeration of the irreducible characters
  obtain ⟨i₀, hi₀⟩ : ∃ i, irreducibleCharacter ℂ i = fun _ : G => (1 : ℂ) := by
    have hchar : (Representation.trivial ℂ G ℂ).character = fun _ : G => (1 : ℂ) := by
      funext x
      have hx : (Representation.trivial ℂ G ℂ) x = LinearMap.id := LinearMap.ext fun v => by simp
      simp [Representation.character, hx]
    have hmem : (fun _ : G => (1 : ℂ)) ∈ irreducibleCharacters ℂ G := by
      rw [← hchar]
      exact character_mem_irreducibleCharacters (Representation.trivial ℂ G ℂ)
    exact exists_irreducibleCharacter_eq ℂ hmem
  -- some nontrivial irreducible character survives at `g` with degree prime to `p`
  obtain ⟨i, hne, hchi, hpdvd⟩ := exists_ne_of_not_dvd_characterDegree hg1 hp hi₀
  -- its degree is coprime to the class size, so Burnside's vanishing theorem applies
  have hcop : (Nat.card (ConjClasses.mk g).carrier).Coprime
      (finrank ℂ (Fin (characterDegree ℂ i) → ℂ)) := by
    rw [hcard]
    simpa using Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpdvd)
  have hdich := Representation.char_eq_zero_or_norm_char_eq_finrank
    (irreducibleRepresentation ℂ i) hcop
  rw [character_irreducibleRepresentation] at hdich
  rcases hdich with h0 | hnorm
  · exact hchi h0
  obtain ⟨μ, -, hμ⟩ := Representation.exists_apply_eq_smul_of_norm_char_eq_finrank
    (irreducibleRepresentation ℂ i) (isOfFinOrder_of_finite g).orderOf_pos.ne'
    (pow_orderOf_eq_one g) (by rw [character_irreducibleRepresentation]; exact hnorm)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (MonoidHom.ker (irreducibleRepresentation ℂ i)) inferInstance with hker | hker
  · -- the representation is faithful, so a scalar value makes `g` central
    have hinj : Function.Injective (irreducibleRepresentation ℂ i) :=
      (MonoidHom.ker_eq_bot_iff _).1 hker
    refine hgcenter (Subgroup.mem_center_iff.2 fun h => hinj ?_)
    rw [map_mul, map_mul, hμ, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  · -- the representation is trivial, so its character is constant, and row orthogonality
    -- against the trivial character makes its degree zero
    have htriv : ∀ h : G, irreducibleCharacter ℂ i h = (characterDegree ℂ i : ℂ) := by
      intro h
      have hone : (irreducibleRepresentation ℂ i) h = 1 :=
        MonoidHom.mem_ker.mp (by rw [hker]; exact Subgroup.mem_top h)
      rw [← character_irreducibleRepresentation ℂ i]
      simp [Representation.character, hone]
    have horth := card_inv_mul_sum_characterTable_mul_conj (G := G) i i₀
    simp only [hne, ite_false] at horth
    have hval : ∀ g' : G, characterTable ℂ G i (ConjClasses.mk g') *
        (starRingEnd ℂ) (characterTable ℂ G i₀ (ConjClasses.mk g'))
          = (characterDegree ℂ i : ℂ) := by
      intro g'
      rw [characterTable_apply, characterTable_apply, htriv, hi₀]
      simp
    simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at horth
    have hcardG : ((Fintype.card G : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hinv : ((Nat.card G : ℕ) : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hzero : (characterDegree ℂ i : ℂ) = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 horth).resolve_left hinv)).resolve_left hcardG
    exact absurd hzero (by exact_mod_cast (characterDegree_pos (k := ℂ) i).ne')

end ClassSize

section Burnside

/-- The induction behind Burnside's `pᵃqᵇ` theorem, on the order of the group. -/
private theorem isSolvable_aux {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Nat.card G ∣ p ^ a * q ^ b →
      Group.IsSolvable G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hdvd
    have : Fact p.Prime := ⟨hp⟩
    have : Fact q.Prime := ⟨hq⟩
    rcases subsingleton_or_nontrivial G with hsub | hnt
    · exact inferInstance
    by_cases hN : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · -- split along a proper nontrivial normal subgroup
      obtain ⟨N, hnorm, hbot, htop⟩ := hN
      have := hnorm
      have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hbot
      have hmul : Nat.card N * N.index = Nat.card G := N.card_mul_index
      have hidx : 2 ≤ N.index := by
        have h1 : N.index ≠ 1 := fun hi => htop (Subgroup.index_eq_one.1 hi)
        have h0 : 0 < N.index := by rw [Subgroup.index_eq_card]; exact Nat.card_pos
        omega
      have hsub : 2 ≤ Nat.card N := Finite.one_lt_card
      refine (Group.isSolvable_iff_subgroup_quotient N).2 ⟨ih (Nat.card N) ?_ N rfl ?_,
        ih (Nat.card (G ⧸ N)) ?_ (G ⧸ N) rfl ?_⟩
      · subst hn; nlinarith
      · exact (Subgroup.card_subgroup_dvd_card N).trans hdvd
      · rw [← Subgroup.index_eq_card]; subst hn; nlinarith
      · exact (Subgroup.card_quotient_dvd_card N).trans hdvd
    · -- no such subgroup: the group is simple
      push Not at hN
      have hsimple : IsSimpleGroup G :=
        { eq_bot_or_eq_top_of_normal := fun N hnorm =>
            (em (N = ⊥)).imp id fun h => hN N hnorm h }
      by_cases hqdvd : q ∣ Nat.card G
      · -- a Sylow `q`-subgroup is nontrivial, and the centre of it supplies the element
        obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
        have hQbot : (Q : Subgroup G) ≠ ⊥ := fun h =>
          Q.not_dvd_index (by rw [h, Subgroup.index_bot]; exact hqdvd)
        have : Nontrivial (Q : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hQbot
        have : Nontrivial (Subgroup.center (Q : Subgroup G)) := Q.isPGroup'.center_nontrivial
        obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ((Q : Subgroup G)))
        set g : G := ((z : (Q : Subgroup G)) : G) with hgdef
        have hgne : g ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
        have hle : (Q : Subgroup G) ≤ Subgroup.centralizer {g} := by
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          rintro m rfl
          simpa [hgdef] using
            (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)).symm
        have hQidx : (Q : Subgroup G).index ∣ p ^ a := by
          have hcop : ((Q : Subgroup G).index).Coprime (q ^ b) :=
            Nat.Coprime.pow_right b ((hq.coprime_iff_not_dvd.2 Q.not_dvd_index).symm)
          exact hcop.dvd_of_dvd_mul_right ((Subgroup.index_dvd_card _).trans hdvd)
        obtain ⟨k, -, hk⟩ :=
          (Nat.dvd_prime_pow hp).1 ((Subgroup.index_dvd_of_le hle).trans hQidx)
        have hclass : Nat.card (ConjClasses.mk g).carrier = p ^ k := by
          rw [ConjClasses.card_carrier_mk, hk]
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · -- the class is a point, so `g` is central and simplicity makes `G` abelian
          have htop : Subgroup.centralizer {g} = ⊤ := Subgroup.index_eq_one.1 (by
            rw [← ConjClasses.card_carrier_mk, hclass, pow_zero])
          have hgc : g ∈ Subgroup.center G :=
            Subgroup.centralizer_eq_top_iff_subset.1 htop (Set.mem_singleton g)
          have hcenter : Subgroup.center G = ⊤ := by
            rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
            · exact absurd (by rw [h] at hgc; simpa using hgc) hgne
            · exact h
          exact Group.isSolvable_of_comm fun x y => by
            have hy : y ∈ Subgroup.center G := by rw [hcenter]; exact Subgroup.mem_top y
            exact Subgroup.mem_center_iff.1 hy x
        · exact absurd hsimple
            (not_isSimpleGroup_of_card_carrier_eq_prime_pow hp hkpos.ne' hclass)
      · -- no `q`-torsion: the group is a `p`-group, hence nilpotent
        have hcop : (Nat.card G).Coprime (q ^ b) :=
          Nat.Coprime.pow_right b ((hq.coprime_iff_not_dvd.2 hqdvd).symm)
        have hpg := IsPGroup.of_card_dvd_pow (p := p) (hcop.dvd_of_dvd_mul_right hdvd)
        have := hpg.isNilpotent
        exact inferInstance

/-- **Burnside's `pᵃqᵇ` theorem**, in the form the induction runs in: a finite group whose order
divides a product of two prime powers is solvable. -/
theorem isSolvable_of_card_dvd_prime_pow_mul_prime_pow {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (h : Nat.card G ∣ p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_aux hp hq a b (Nat.card G) G rfl h

/-- **Burnside's `pᵃqᵇ` theorem**: a finite group of order `pᵃqᵇ`, for primes `p` and `q`, is
solvable. -/
theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_dvd_prime_pow_mul_prime_pow hp hq (by rw [h])

end Burnside

end TauCeti
