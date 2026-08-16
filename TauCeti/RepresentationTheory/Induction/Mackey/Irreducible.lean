/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.FinGroupCharZero
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.RepresentationTheory.Induction.Mackey.Intertwining

/-!
# The Mackey irreducibility criterion

Let `H` be a subgroup of a finite group `G` and let `A` be a finite-dimensional representation of
`H` over an algebraically closed field of characteristic zero.  The intertwining-number formula
`TauCeti.finrank_hom_indFDRep_mackey_erase` reads

`dim End_G(Ind_H^G A) = dim End_H A + ∑_{HsH ≠ H} dim Hom_{H ⊓ sHs⁻¹}(Res A, {}^s A)`,

a sum of natural numbers.  Over an algebraically closed field in which `|G|` is invertible a
finite-dimensional representation is irreducible exactly when its endomorphism algebra is a line
(Mathlib's `FDRep.simple_iff_end_is_rank_one`), so the left-hand side is `1` exactly when the first
summand is `1` and every other summand is `0`.  That reading is the **Mackey irreducibility
criterion**: `Ind_H^G A` is irreducible if and only if `A` is irreducible and, for every
double coset `HsH` other than `H` itself, the two restrictions `Res_{H ⊓ sHs⁻¹} A` and
`Res_{H ⊓ sHs⁻¹} ({}^s A)` are **disjoint**, that is, have no nonzero intertwiner.  Disjointness is
named here as `TauCeti.MackeyDisjoint`, and both forms of the criterion are stated through it.

The criterion comes in two forms.  The primary one, `TauCeti.simple_indFDRep_iff_doubleCoset`,
quantifies over the double cosets `H \ G / H` and, following the roadmap, reads each Mackey term at
the fixed representative `Quotient.out`.  The elementwise form, `TauCeti.simple_indFDRep_iff`,
quantifies over the group elements `s ∉ H` instead.

## Main definitions

* `TauCeti.MackeyDisjoint`: the restrictions of `A` and of `{}^s A` to the Mackey subgroup
  `H ⊓ sHs⁻¹` admit no nonzero intertwiner.

## Main statements

* `TauCeti.mackeyDisjoint_iff_subsingleton`, `TauCeti.MackeyDisjoint.eq_zero` and
  `TauCeti.mackeyDisjoint_of_forall_eq_zero`: the predicate read back as the vanishing of every
  intertwiner.
* `TauCeti.simple_indFDRep_iff_doubleCoset`: the Mackey irreducibility criterion over the double
  cosets.
* `TauCeti.simple_indFDRep_iff`: the same criterion quantified over the elements outside `H`.
* `TauCeti.simple_indFDRep_iff_of_normal`: for `H ◁ G`, induction of `A` is irreducible exactly
  when `A` is irreducible and no conjugate `{}^s A`, for `s ∉ H`, is isomorphic to `A`.
* `TauCeti.mackeyDisjoint_mul_left_mul_right_iff`: Mackey disjointness depends only on the double
  coset.

## Implementation notes

`TauCeti.MackeyDisjoint` is stated as `Subsingleton` of the intertwining space; the
intertwining-number formula produces the dimension of that space instead, and
`TauCeti.mackeyDisjoint_iff_finrank_eq_zero` is the bridge between the two readings, along which
the double-coset criterion is proved.  That bridge is deliberately not a `simp` lemma: the named
predicate is the form the criteria are stated in and the form its own API
(`TauCeti.mackeyDisjoint_mul_left_mul_right_iff`) applies to, so unfolding it to a dimension on
sight would be the wrong normal form.

The step in those proofs that the arithmetic does not hand over for free is that `dim End_H A`
cannot be `0`: a representation with no nonzero endomorphism is a zero object, and then every term
of the sum vanishes too, so the total could not be `1`.  That is what the two private helpers of
the `ZeroObject` section below record.

Passing between the two forms of the criterion needs the Mackey term to be constant on a double
coset, which is `TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`, proved with the formula it
belongs to; `TauCeti.mackeyDisjoint_mul_left_mul_right_iff` is its reading through the predicate.

The characteristic-zero hypothesis of the two criteria is inherited from
`TauCeti.finrank_hom_indFDRep_mackey_erase`: the intertwining-number formula is proved as an
identity in `k` of the casts of the dimensions, and reading it back as an identity of natural
numbers -- which is what lets the summands be compared one by one -- needs `ℕ → k` injective.  Only
those two statements carry it: `TauCeti.MackeyDisjoint` and its API hold over any field.

That is also where Mathlib puts a simplicity criterion obtained from a character identity:
`FDRep.simple_iff_char_is_norm_one` assumes `[CharZero k]`, and uses it for exactly this step
(`Nat.cast_inj`), even though the rank-one criterion `FDRep.simple_iff_end_is_rank_one` it is
derived from asks only for `[NeZero (Nat.card G : k)]`.  Reaching the criteria below over such a
field means proving the intertwining-number formula in `ℕ` from the Mackey decomposition as an
isomorphism of representations, which is a separate roadmap target (Layer 3a) and is not
formalized here.

For a normal subgroup the Mackey subgroup is all of `H`.  Restricting along
`TauCeti.mackeySubgroupNormalEquiv` shows that the corresponding Mackey term and
`Hom_H(A, {}^s A)` have equal dimensions, and `TauCeti.simple_indFDRep_iff_of_normal` gives the
resulting normal-subgroup corollary.  This is the form used by Clifford theory (Layer 5).

## References

Layer 4 of
[the induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
"the Mackey irreducibility criterion" and its "`∀ s ∉ H` corollary".

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.4, Proposition 23.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5, Theorem 5.6 and Corollary 5.7.
-/

public section

open scoped Pointwise

open CategoryTheory Limits

namespace TauCeti

universe u

section ZeroObject

variable {k : Type u} [Field k]

/-- A representation whose only endomorphism is `0` is a zero object: its identity is that
endomorphism. -/
private theorem isZero_of_finrank_end_eq_zero {S : Type u} [Monoid S] (A : FDRep k S)
    (h : Module.finrank k (A ⟶ A) = 0) : IsZero A :=
  have : Subsingleton (A ⟶ A) := Module.finrank_zero_iff.mp h
  (IsZero.iff_id_eq_zero A).mpr (Subsingleton.elim _ _)

/-- The intertwining space into a zero object is trivial. -/
private theorem finrank_hom_eq_zero_of_isZero {S : Type u} [Monoid S] {X Y : FDRep k S}
    (h : IsZero Y) :
    Module.finrank k (X ⟶ Y) = 0 :=
  have : Subsingleton (X ⟶ Y) :=
    ⟨fun f g => by rw [h.eq_zero_of_tgt f, h.eq_zero_of_tgt g]⟩
  Module.finrank_zero_of_subsingleton

end ZeroObject

section Disjoint

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G}

/-- **Mackey disjointness at `s`**: the restrictions of `A` and of its conjugate `{}^s A` to the
Mackey subgroup `H ⊓ sHs⁻¹` admit no nonzero intertwiner.  The conjugation and the restriction of
`{}^s A` are packaged into the single homomorphism `TauCeti.mackeyToH`.

This is the condition the Mackey irreducibility criterion imposes on every double coset other than
`H` itself. -/
def MackeyDisjoint (A : FDRep k H) (s : G) : Prop :=
  Subsingleton (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
    (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A)

/-- **Mackey disjointness unfolded.**  The body of `TauCeti.MackeyDisjoint` is not exposed, so
this is how a consumer reads the definition. -/
theorem mackeyDisjoint_iff_subsingleton (A : FDRep k H) (s : G) :
    MackeyDisjoint A s ↔
      Subsingleton (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) :=
  Iff.rfl

/-- An intertwiner between the two restrictions of a Mackey disjoint pair is zero. -/
theorem MackeyDisjoint.eq_zero {A : FDRep k H} {s : G} (h : MackeyDisjoint A s)
    (φ : resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) : φ = 0 :=
  @Subsingleton.elim _ h φ 0

/-- Mackey disjointness holds as soon as every intertwiner between the two restrictions is zero. -/
theorem mackeyDisjoint_of_forall_eq_zero {A : FDRep k H} {s : G}
    (h : ∀ φ : resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A, φ = 0) : MackeyDisjoint A s :=
  ⟨fun φ ψ => (h φ).trans (h ψ).symm⟩

/-- Mackey disjointness read as the vanishing of a dimension, which is the shape in which the
intertwining-number formula produces it. -/
theorem mackeyDisjoint_iff_finrank_eq_zero (A : FDRep k H) (s : G) :
    MackeyDisjoint A s ↔
      Module.finrank k (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) = 0 :=
  Module.finrank_zero_iff.symm

/-- **Mackey disjointness depends only on the double coset**: it holds at `h₁ s h₂` with
`h₁, h₂ ∈ H` exactly when it holds at `s`.  This is the predicate form of
`TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`, and is what moves the criterion between
its double-coset and its elementwise reading. -/
theorem mackeyDisjoint_mul_left_mul_right_iff (A : FDRep k H) {h₁ h₂ : G} (hh₁ : h₁ ∈ H)
    (hh₂ : h₂ ∈ H) (s : G) : MackeyDisjoint A (h₁ * s * h₂) ↔ MackeyDisjoint A s := by
  rw [mackeyDisjoint_iff_finrank_eq_zero, mackeyDisjoint_iff_finrank_eq_zero,
    finrank_hom_res_mackeyToH_mul_left_mul_right A A hh₁ hh₂ s]

end Disjoint

section NormalDisjoint

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G} [H.Normal]

/-- For a normal subgroup and an irreducible `A`, Mackey disjointness at `s` says exactly that
the conjugate `{}^s A` is not isomorphic to `A`. -/
theorem mackeyDisjoint_iff_isEmpty_iso_of_normal (A : FDRep k H) [Simple A] (s : G) :
    MackeyDisjoint A s ↔ IsEmpty (conjNormalFDRep s A ≅ A) := by
  have hsimple : Simple (conjNormalFDRep s A) := by
    rw [conjNormalFDRep, ← conjNormalFDRepEquiv_functor]
    exact CategoryTheory.simple_obj _ A
  let _ := hsimple
  rw [mackeyDisjoint_iff_finrank_eq_zero, finrank_hom_res_mackeyToH_of_normal]
  constructor
  · intro h
    have hsubsingleton : Subsingleton (A ⟶ conjNormalFDRep s A) :=
      Module.finrank_zero_iff.mp h
    exact ⟨fun e ↦ (CategoryTheory.isIso_iff_nonzero e.symm.hom).mp inferInstance
      (hsubsingleton.elim e.symm.hom 0)⟩
  · intro h
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun e ↦ h.false e.symm

end NormalDisjoint

section Criterion

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {H : Subgroup G}

/-- **The Mackey irreducibility criterion.**  The representation induced from `A` is irreducible
exactly when `A` is irreducible and every double coset `HsH` other than `H` itself, read at its
chosen representative, is Mackey disjoint. -/
theorem simple_indFDRep_iff_doubleCoset (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G), D ≠ DoubleCoset.mk H H 1 →
        MackeyDisjoint A D.out := by
  classical
  simp only [mackeyDisjoint_iff_finrank_eq_zero]
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have : NeZero (Nat.card H : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- The intertwining-number formula, read as an identity of natural numbers: the identity double
  -- coset contributes `dim End_H A` and every other summand is a Mackey term.
  rw [FDRep.simple_iff_end_is_rank_one, FDRep.simple_iff_end_is_rank_one,
    finrank_hom_indFDRep_mackey_erase A]
  constructor
  · intro h
    -- If `A` had no nonzero endomorphism it would be a zero object, and then every Mackey term
    -- would vanish as well, leaving `0 = 1`.
    have hA : Module.finrank k (A ⟶ A) ≠ 0 := by
      intro h0
      rw [h0, Finset.sum_eq_zero fun D _ =>
        finrank_hom_eq_zero_of_isZero ((Action.res (FGModuleCat k) _).map_isZero
          (isZero_of_finrank_end_eq_zero A h0))] at h
      exact absurd h (by norm_num)
    obtain ⟨h1, h2⟩ := (Nat.add_eq_one_iff.mp h).resolve_left fun hc => hA hc.1
    exact ⟨h1, fun D hD => Finset.sum_eq_zero_iff.mp h2 D (Finset.mem_erase.mpr ⟨hD, by simp⟩)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, Finset.sum_eq_zero fun D hD => h2 D (Finset.mem_erase.mp hD).1, add_zero]

/-- **The Mackey irreducibility criterion, elementwise.**  The disjointness condition of
`TauCeti.simple_indFDRep_iff_doubleCoset` may equally be asked of every element `s ∉ H` rather than
of one chosen representative of every non-identity double coset. -/
theorem simple_indFDRep_iff (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧ ∀ s ∉ H, MackeyDisjoint A s := by
  rw [simple_indFDRep_iff_doubleCoset]
  -- Disjointness is constant on a double coset, and the double cosets meeting `H` are the
  -- identity one.
  refine and_congr_right fun _ => ⟨fun h s hs => ?_, fun h D hD => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      (DoubleCoset.eq H H (DoubleCoset.mk H H s).out s).mp (DoubleCoset.out_eq' H H _)
    exact hab ▸ (mackeyDisjoint_mul_left_mul_right_iff A ha hb _).mpr
      (h _ fun hc => hs ((doubleCosetMk_eq_mk_one_iff_mem H s).mp hc))
  · exact h D.out fun hmem =>
      hD ((DoubleCoset.out_eq' H H D).symm.trans
        ((doubleCosetMk_eq_mk_one_iff_mem H D.out).mpr hmem))

/-- **The Mackey irreducibility criterion for a normal subgroup.**  If `H ◁ G`, then the
representation induced from `A` is irreducible exactly when `A` is irreducible and none of its
conjugates `{}^s A`, for `s ∉ H`, is isomorphic to `A`. -/
theorem simple_indFDRep_iff_of_normal [H.Normal] (A : FDRep k H) :
    Simple (indFDRep A) ↔
      Simple A ∧ ∀ s ∉ H, IsEmpty (conjNormalFDRep s A ≅ A) := by
  rw [simple_indFDRep_iff]
  refine and_congr_right fun hA ↦ ?_
  let _ := hA
  exact forall_congr' fun s ↦ forall_congr' fun _ ↦
    mackeyDisjoint_iff_isEmpty_iso_of_normal A s

end Criterion

end TauCeti
