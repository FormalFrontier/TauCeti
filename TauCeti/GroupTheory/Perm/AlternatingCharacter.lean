/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# An odd permutation inverts every linear character of the alternating group

Let `α` be a finite type and let `χ` be a homomorphism from `alternatingGroup α` to a commutative
group. Conjugation by an *even* permutation cannot move `χ`, the target being commutative. This
file proves that conjugation by an **odd** permutation inverts it:

`χ (s x s⁻¹) = (χ x)⁻¹` for every `s ∉ alternatingGroup α` and every `x`.

The argument is short and uniform in `α`. The product of `χ` with its conjugate by `s` is fixed by
conjugation by `s`, because `s * s` is even; and a character fixed by conjugation by *one* odd
permutation is fixed by conjugation by *every* permutation, since the odd permutations form a
single coset of the even ones. Such a character kills every three-cycle `c`, because `c` is
conjugate in `Equiv.Perm α` to its own inverse, so the value at `c` is its own inverse while also
cubing to `1`. Three-cycles generate the alternating group, so the character is trivial, which is
the claim.

The consequence the file exists for is that a **nontrivial** linear character `χ` satisfies
`χ ∘ conj s ≠ χ` for every odd `s`: otherwise `χ` would be its own inverse and the same lemma would
make it trivial. So the odd permutations move `χ`, and `{χ, χ⁻¹}` is a single orbit of two
characters under the conjugation action of `Equiv.Perm α`. That is exactly the hypothesis of the
Mackey irreducibility criterion for an induced linear character, applied to `A₄ ◁ S₄` in
`TauCeti.RepresentationTheory.Induction.Clifford.Alternating`.

For that application to be about something, `alternatingGroup α` must *have* a nontrivial linear
character, which for `Nat.card α = 4` it does: Mathlib's `alternatingGroup.kleinFour_eq_commutator`
identifies the commutator subgroup of `A₄` with the Klein four subgroup, of order `4` inside a
group of order `12`, so the commutator subgroup is proper and the duality of finite abelian groups
produces a character of the abelianization that does not kill it. For `4 < Nat.card α` the
alternating group is perfect instead, and the statements above are then all vacuously about the
trivial character.

## Main statements

* `TauCeti.eq_one_of_map_conjNormal_eq_alternatingGroup`: **a linear character of the alternating
  group fixed by conjugation by an odd permutation is trivial.**
* `TauCeti.map_conjNormal_alternatingGroup_eq_inv`: **an odd permutation inverts every linear
  character of the alternating group**, with `TauCeti.comp_conjNormal_alternatingGroup_eq_inv` its
  form as an equality of homomorphisms.
* `TauCeti.exists_map_conjNormal_alternatingGroup_ne`: an odd permutation moves every nontrivial
  linear character -- the hypothesis of the Mackey irreducibility criterion.
* `TauCeti.comp_conjNormal_alternatingGroup_ne`: the same as an inequality of homomorphisms, so
  that a nontrivial linear character and its conjugate by an odd permutation are two distinct
  members of one orbit.
* `TauCeti.exists_monoidHom_alternatingGroup_ne_one`: **`A₄` has a nontrivial linear character.**

## References

The group theory behind the "Clifford on `A₄ ◁ S₄`" worked example of
[the induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md).

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 5.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

section Character

variable {M : Type*} [CommGroup M] (χ : alternatingGroup α →* M)

/-- Conjugation by an element of a normal subgroup does not move a homomorphism from that subgroup
to a commutative group: it conjugates the value, which is the value. -/
private theorem map_conjNormal_of_mem_subgroup {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (ψ : N →* M) (a x : N) : ψ (MulAut.conjNormal (a : G) x) = ψ x := by
  rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
    mul_comm (ψ a) (ψ x), mul_assoc, mul_inv_cancel, mul_one]

/-- Two odd permutations differ by an even one. -/
private theorem mul_inv_mem_alternatingGroup {g s : Perm α} (hg : g ∉ alternatingGroup α)
    (hs : s ∉ alternatingGroup α) : g * s⁻¹ ∈ alternatingGroup α := by
  simp only [mem_alternatingGroup] at hg hs ⊢
  rw [map_mul, map_inv]
  rcases Int.units_eq_one_or (sign g) with h | h
  · exact absurd h hg
  · rcases Int.units_eq_one_or (sign s) with h' | h'
    · exact absurd h' hs
    · rw [h, h']
      decide

/-- The square of an odd permutation is even. -/
private theorem mul_self_mem_alternatingGroup {s : Perm α} (hs : s ∉ alternatingGroup α) :
    s * s ∈ alternatingGroup α := by
  simp only [mem_alternatingGroup] at hs ⊢
  rw [map_mul]
  rcases Int.units_eq_one_or (sign s) with h | h
  · exact absurd h hs
  · rw [h]
    decide

/-- A linear character fixed by conjugation by one odd permutation is fixed by conjugation by
every permutation: the even ones fix it because the target is commutative, and every odd one is an
even one times the given one. -/
private theorem map_conjNormal_alternatingGroup_of_fixed {s : Perm α}
    (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) (g : Perm α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal g x) = χ x := by
  by_cases hg : g ∈ alternatingGroup α
  · exact map_conjNormal_of_mem_subgroup χ ⟨g, hg⟩ x
  · have hgs : g * s⁻¹ ∈ alternatingGroup α := mul_inv_mem_alternatingGroup hg hs
    have hfac : (MulAut.conjNormal g : MulAut (alternatingGroup α)) =
        MulAut.conjNormal ((⟨g * s⁻¹, hgs⟩ : alternatingGroup α) : Perm α) *
          MulAut.conjNormal s := by
      rw [← map_mul]
      congr 1
      simp
    rw [hfac]
    exact (map_conjNormal_of_mem_subgroup χ ⟨g * s⁻¹, hgs⟩ _).trans (h x)

/-- **A linear character of the alternating group fixed by conjugation by an odd permutation is
trivial.** Such a character is fixed by conjugation by every permutation, hence takes the same
value at a three-cycle and at its inverse; that value is therefore its own inverse while also
cubing to `1`, so it is `1`, and the three-cycles generate the alternating group. -/
theorem eq_one_of_map_conjNormal_eq_alternatingGroup {s : Perm α} (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) : χ = 1 := by
  have hall := map_conjNormal_alternatingGroup_of_fixed χ hs h
  -- The character kills every three-cycle.
  have hthree : ∀ c : Perm α, c.IsThreeCycle → ∀ hc : c ∈ alternatingGroup α, χ ⟨c, hc⟩ = 1 := by
    intro c hc hcmem
    -- Every permutation is conjugate to its inverse: the two have the same cycle type.
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv c).symm)
    have hconj : MulAut.conjNormal g (⟨c, hcmem⟩ : alternatingGroup α) = (⟨c, hcmem⟩)⁻¹ :=
      Subtype.ext (by simpa using hg)
    have hinv : (χ (⟨c, hcmem⟩ : alternatingGroup α))⁻¹ = χ ⟨c, hcmem⟩ := by
      rw [← map_inv, ← hconj]
      exact hall g _
    have hsq : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hinv.symm
    have hpow : (⟨c, hcmem⟩ : alternatingGroup α) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [Subgroup.orderOf_mk, hc.orderOf])
    have hcube : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 3 = 1 := by
      rw [← map_pow, hpow, map_one]
    have hstep : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 2 * χ (⟨c, hcmem⟩ : alternatingGroup α)
        = 1 := by
      rw [← pow_succ]
      exact hcube
    rwa [hsq, one_mul] at hstep
  -- Three-cycles generate the alternating group, so the kernel is everything.
  have hle : alternatingGroup α ≤ χ.ker.map (alternatingGroup α).subtype := by
    refine le_trans (le_of_eq closure_three_cycles_eq_alternating.symm) ?_
    rw [Subgroup.closure_le]
    rintro c (hc : c.IsThreeCycle)
    exact Subgroup.mem_map.mpr ⟨⟨c, hc.mem_alternatingGroup⟩, hthree c hc _, rfl⟩
  ext x
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hle x.2)
  rw [MonoidHom.one_apply, ← show y = x from Subtype.ext hxy]
  exact hy

/-- **An odd permutation inverts every linear character of the alternating group.** The product of
`χ` with its conjugate by `s` is fixed by conjugation by `s`, because `s * s` is even, hence
trivial. -/
theorem map_conjNormal_alternatingGroup_eq_inv {s : Perm α} (hs : s ∉ alternatingGroup α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal s x) = (χ x)⁻¹ := by
  have hsq : s * s ∈ alternatingGroup α := mul_self_mem_alternatingGroup hs
  have hcomp : ∀ y : alternatingGroup α,
      (MulAut.conjNormal s) ((MulAut.conjNormal s) y) = MulAut.conjNormal (s * s) y := by
    intro y
    rw [map_mul]
    rfl
  have hfix : ∀ y : alternatingGroup α,
      (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ)
          (MulAut.conjNormal s y) =
        (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ) y := by
    intro y
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [hcomp y, show χ (MulAut.conjNormal (s * s) y) = χ y from
      map_conjNormal_of_mem_subgroup χ ⟨s * s, hsq⟩ y, mul_comm]
  have hone := eq_one_of_map_conjNormal_eq_alternatingGroup _ hs hfix
  have hx : (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ) x = 1 := by
    rw [hone]
    rfl
  simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom] at hx
  exact eq_inv_of_mul_eq_one_left hx

/-- **An odd permutation inverts every linear character of the alternating group**, as an equality
of homomorphisms. -/
theorem comp_conjNormal_alternatingGroup_eq_inv {s : Perm α} (hs : s ∉ alternatingGroup α) :
    χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom = χ⁻¹ :=
  MonoidHom.ext fun x => map_conjNormal_alternatingGroup_eq_inv χ hs x

/-- **An odd permutation moves every nontrivial linear character of the alternating group.** This
is the hypothesis of the Mackey irreducibility criterion for an induced linear character, checked
at `A₄ ◁ S₄`. -/
theorem exists_map_conjNormal_alternatingGroup_ne (hχ : χ ≠ 1) {s : Perm α}
    (hs : s ∉ alternatingGroup α) : ∃ x : alternatingGroup α, χ (MulAut.conjNormal s x) ≠ χ x := by
  by_contra hcon
  push Not at hcon
  exact hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs hcon)

/-- **A nontrivial linear character of the alternating group and its conjugate by an odd
permutation are distinct**, so the two of them make up a single orbit of the conjugation action of
`Equiv.Perm α` on the characters. -/
theorem comp_conjNormal_alternatingGroup_ne (hχ : χ ≠ 1) {s : Perm α}
    (hs : s ∉ alternatingGroup α) :
    χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom ≠ χ := fun hcon =>
  hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs
    fun x => congrArg (fun f : alternatingGroup α →* M => f x) hcon)

end Character

section Existence

/-- The canonical map to the abelianization is surjective. -/
private theorem surjective_abelianization_of (G : Type*) [Group G] :
    Function.Surjective (Abelianization.of : G →* Abelianization G) := fun y =>
  QuotientGroup.induction_on y fun x => ⟨x, rfl⟩

/-- **The abelianization of `A₄` is nontrivial**, witnessed by an even permutation outside the
Klein four subgroup: that subgroup is the commutator subgroup of `A₄`, and it has order `4` inside
a group of order `12`. -/
theorem exists_abelianization_of_ne_one_alternatingGroup (hα : Nat.card α = 4) :
    ∃ x : alternatingGroup α, Abelianization.of x ≠ 1 := by
  have hne : alternatingGroup.kleinFour α ≠ ⊤ := by
    intro htop
    have hcard : Nat.card (alternatingGroup.kleinFour α) = Nat.card (alternatingGroup α) := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [alternatingGroup.kleinFour_card_of_card_eq_four hα,
      alternatingGroup.card_of_card_eq_four hα] at hcard
    omega
  obtain ⟨x, hx⟩ : ∃ x : alternatingGroup α, x ∉ alternatingGroup.kleinFour α := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_top_iff' _).mpr hcon)
  refine ⟨x, ?_⟩
  rw [Ne, ← MonoidHom.mem_ker, Abelianization.ker_of,
    ← alternatingGroup.kleinFour_eq_commutator hα]
  exact hx

variable (M : Type*) [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent (alternatingGroup α))]

/-- **`A₄` has a nontrivial linear character** valued in any commutative monoid with enough roots
of unity for the exponent of `A₄`; an algebraically closed field of characteristic zero supplies
one. The character comes from the abelianization `A₄ / V₄`, which
`TauCeti.exists_abelianization_of_ne_one_alternatingGroup` shows is nontrivial, by the duality of
finite abelian groups. -/
theorem exists_monoidHom_alternatingGroup_ne_one (hα : Nat.card α = 4) :
    ∃ χ : alternatingGroup α →* Mˣ, χ ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_abelianization_of_ne_one_alternatingGroup (α := α) hα
  have _ : Finite (Abelianization (alternatingGroup α)) :=
    Finite.of_surjective _ (surjective_abelianization_of (alternatingGroup α))
  have _ : HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (alternatingGroup α))) :=
    HasEnoughRootsOfUnity.of_dvd M
      (MonoidHom.exponent_dvd (surjective_abelianization_of (alternatingGroup α)))
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization (alternatingGroup α)) M
      hx
  refine ⟨φ.comp Abelianization.of, fun hcon => hφ ?_⟩
  simpa using congrArg (fun f : alternatingGroup α →* Mˣ => f x) hcon

end Existence

end TauCeti
