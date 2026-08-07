/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.FinGroupCharZero
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
`Res_{H ⊓ sHs⁻¹} ({}^s A)` are **disjoint**, that is, have no nonzero intertwiner.

The one thing the arithmetic does not hand over for free is that `dim End_H A` cannot be `0`: a
representation with no nonzero endomorphism is a zero object, and then every term of the sum
vanishes too, so the total could not be `1`.  That is what the `ZeroObject` section below records.

The criterion comes in two forms.  The primary one quantifies over the double cosets
`H \ G / H` and, following the roadmap, reads each Mackey term at the fixed representative
`Quotient.out`.  The elementwise form quantifies over the group elements `s ∉ H` instead; passing
between them is `TauCeti.finrank_hom_res_mackeyToH_conj`, the statement that the Mackey term is
unchanged when `s` is replaced by `h₁ s h₂` with `h₁, h₂ ∈ H`.  That invariance is proved on class
functions, where it is a reindexing of the pairing along conjugation by `h₁`
(`TauCeti.mackeySubgroupOfCongr`) together with the fact that a class function is blind to
conjugation by `h₂`.

## Main statements

* `TauCeti.simple_indFDRep_iff`: the Mackey irreducibility criterion over the double cosets.
* `TauCeti.simple_indFDRep_iff_forall_notMem`: the same criterion quantified over the elements
  outside `H`.
* `TauCeti.simple_indFDRep_iff_subsingleton`: the same criterion with disjointness read as the
  absence of a nonzero intertwiner.
* `TauCeti.finrank_hom_res_mackeyToH_conj`: the Mackey term depends only on the double coset.
* `TauCeti.characterPairing_mackeyClassFunction_conj`: the class-function form of that invariance,
  which needs neither an algebraically closed field nor a representation.
* `TauCeti.doubleCoset_mk_eq_mk_one_iff`: a double coset is the identity one exactly when its
  elements lie in `H`.

## Implementation notes

Disjointness of the two restrictions is expressed as the vanishing of `Module.finrank` of the
intertwining space, which is the quantity the intertwining-number formula produces; by
`Module.finrank_zero_iff` that is the same thing as the intertwining space being trivial.

The characteristic-zero hypothesis is inherited from
`TauCeti.finrank_hom_indFDRep_mackey_erase`: the intertwining-number formula is proved as an
identity in `k` of the casts of the dimensions, and reading it back as an identity of natural
numbers -- which is what lets the summands be compared one by one -- needs `ℕ → k` injective.  The
invariance `TauCeti.characterPairing_mackeyClassFunction_conj` itself is free of that hypothesis.

The normal-subgroup corollary -- for `H ◁ G`, irreducibility of `Ind_H^G A` is equivalent to
irreducibility of `A` together with `{}^s A ≇ A` for every `s ∉ H` -- is not proved here.  It needs
the Mackey terms to be identified with `Hom_H(A, {}^s A)` across the identification of
`(H ⊓ sHs⁻¹).subgroupOf H` with `⊤`, which is a transport along an equivalence of representation
categories rather than a character computation, and is left for the Clifford-theory layer that
consumes it.

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

universe u v

section ZeroObject

variable {k : Type u} [Field k]

/-- A representation whose only endomorphism is `0` is a zero object: its identity is that
endomorphism. -/
theorem isZero_of_finrank_end_eq_zero {S : Type u} [Monoid S] (A : FDRep k S)
    (h : Module.finrank k (A ⟶ A) = 0) : IsZero A :=
  have : Subsingleton (A ⟶ A) := Module.finrank_zero_iff.mp h
  (IsZero.iff_id_eq_zero A).mpr (Subsingleton.elim _ _)

/-- Restriction along a monoid homomorphism carries a zero object to a zero object: it leaves the
underlying object, and hence the identity morphism, untouched.

Mathlib's `Rep.isZero_res_iff` is the same statement one category over; it does not transfer to
`FDRep`, which is an `Action` on `FGModuleCat` rather than a structure, so the two-line proof is
repeated here. -/
theorem isZero_res_obj {S T : Type u} [Monoid S] [Monoid T] (φ : S →* T) {A : FDRep k T}
    (h : IsZero A) : IsZero ((Action.res (FGModuleCat k) φ).obj A) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact Action.hom_ext _ _ (show (𝟙 A : A ⟶ A).hom = (0 : A ⟶ A).hom by rw [h])

/-- The intertwining space into a zero object is trivial. -/
theorem finrank_hom_eq_zero_of_isZero {S : Type u} [Monoid S] {X Y : FDRep k S} (h : IsZero Y) :
    Module.finrank k (X ⟶ Y) = 0 :=
  have : Subsingleton (X ⟶ Y) :=
    ⟨fun f g => by rw [h.eq_zero_of_tgt f, h.eq_zero_of_tgt g]⟩
  Module.finrank_zero_of_subsingleton

end ZeroObject

section Representative

variable {k : Type u} {G : Type v} [Field k] [Group G] {H : Subgroup G}

/-- **Changing the representative of a double coset conjugates the Mackey subgroup**, read inside
`H`.  This is `TauCeti.mackeySubgroupCongr` transported along `Subgroup.subgroupOfEquivOfLe`, so
that both sides are subgroups of `H`: that is where the Mackey terms of the intertwining-number
formula live. -/
def mackeySubgroupOfCongr {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) (s : G) :
    (mackeySubgroup s H H).subgroupOf H ≃* (mackeySubgroup (h₁ * s * h₂) H H).subgroupOf H :=
  ((Subgroup.subgroupOfEquivOfLe (mackeySubgroup_le_right (s := s) (H := H) (K := H))).trans
      (mackeySubgroupCongr hh₁ hh₂ s)).trans
    (Subgroup.subgroupOfEquivOfLe
      (mackeySubgroup_le_right (s := h₁ * s * h₂) (H := H) (K := H))).symm

@[simp]
theorem coe_mackeySubgroupOfCongr_apply {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) (s : G)
    (y : (mackeySubgroup s H H).subgroupOf H) :
    ((mackeySubgroupOfCongr hh₁ hh₂ s y : H) : G) = h₁ * ((y : H) : G) * h₁⁻¹ := by
  simp [mackeySubgroupOfCongr]

open scoped Classical in
/-- **The Mackey term of the intertwining-number formula depends only on the double coset.**
Replacing the representative `s` by `h₁ s h₂` with `h₁, h₂ ∈ H` reindexes the pairing along
conjugation by `h₁`; the conjugating element `h₁` then disappears because a class function is
constant on conjugacy classes, and so does `h₂`, which conjugates the argument of the twisted
factor.

This is the class-function shadow of `TauCeti.finrank_hom_res_mackeyToH_conj`; no representation,
no algebraic closure and no characteristic assumption enter. -/
theorem characterPairing_mackeyClassFunction_conj [Fintype H] {h₁ h₂ : G} (hh₁ : h₁ ∈ H)
    (hh₂ : h₂ ∈ H) (s : G) (f : ClassFunction k H) :
    ClassFunction.characterPairing (mackeyClassFunction (h₁ * s * h₂) H H f)
        (ClassFunction.comap ((mackeySubgroup (h₁ * s * h₂) H H).subgroupOf H).subtype f) =
      ClassFunction.characterPairing (mackeyClassFunction s H H f)
        (ClassFunction.comap ((mackeySubgroup s H H).subgroupOf H).subtype f) := by
  have hcard : Nat.card ((mackeySubgroup (h₁ * s * h₂) H H).subgroupOf H) =
      Nat.card ((mackeySubgroup s H H).subgroupOf H) :=
    Nat.card_congr (mackeySubgroupOfCongr hh₁ hh₂ s).symm.toEquiv
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply, hcard]
  congr 1
  refine (Fintype.sum_equiv (mackeySubgroupOfCongr hh₁ hh₂ s).toEquiv _ _ fun y => ?_).symm
  -- Conjugating `y` by `h₁` conjugates `s⁻¹ y s` by `h₂` instead.
  have hconj : mackeyToH (h₁ * s * h₂) H H (mackeySubgroupOfCongr hh₁ hh₂ s y) =
      (⟨h₂, hh₂⟩ : H)⁻¹ * mackeyToH s H H y * (⟨h₂, hh₂⟩ : H)⁻¹⁻¹ :=
    Subtype.ext (by
      push_cast [coe_mackeyToH_apply, coe_mackeySubgroupOfCongr_apply]
      group)
  have hinv : ((mackeySubgroupOfCongr hh₁ hh₂ s y : H))⁻¹ =
      (⟨h₁, hh₁⟩ : H) * ((y : H))⁻¹ * (⟨h₁, hh₁⟩ : H)⁻¹ :=
    Subtype.ext (by
      push_cast [coe_mackeySubgroupOfCongr_apply]
      group)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, mackeyClassFunction_coe,
    mackeyClassFun_apply, ClassFunction.comap_apply, Subgroup.coe_subtype, Subgroup.coe_inv,
    hconj, hinv]
  rw [ClassFunction.mem_iff.mp f.2, ClassFunction.mem_iff.mp f.2]

/-- **The identity double coset is `H` itself**: `HsH = H · 1 · H` exactly when `s ∈ H`.  This is
what makes "the non-identity double cosets" and "the elements outside `H`" index the same Mackey
terms. -/
theorem doubleCoset_mk_eq_mk_one_iff (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [DoubleCoset.eq]
  refine ⟨fun ⟨a, ha, b, hb, hab⟩ => ?_, fun hs => ⟨1, H.one_mem, s⁻¹, H.inv_mem hs, by group⟩⟩
  have hs : s = a⁻¹ * b⁻¹ := by
    have h' : a⁻¹ * (a * s * b) * b⁻¹ = a⁻¹ * (1 : G) * b⁻¹ := by rw [hab]
    simpa [mul_assoc] using h'
  exact hs ▸ H.mul_mem (H.inv_mem ha) (H.inv_mem hb)

end Representative

section Criterion

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {H : Subgroup G}

omit [IsAlgClosed k] in
/-- **The Mackey term depends only on the double coset**, as a dimension: the intertwining space
`Hom_{H ⊓ sHs⁻¹}(Res A, {}^s A)` has the same dimension at `s` and at `h₁ s h₂` for `h₁, h₂ ∈ H`.

This is `TauCeti.characterPairing_mackeyClassFunction_conj` read through the identification of the
character pairing with an intertwining-space dimension. -/
theorem finrank_hom_res_mackeyToH_conj (A : FDRep k H) {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (s : G) :
    Module.finrank k (resFDRep ((mackeySubgroup (h₁ * s * h₂) H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH (h₁ * s * h₂) H H)).obj A) =
      Module.finrank k (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) := by
  classical
  let := Fintype.ofFinite H
  have key : ∀ t : G,
      ClassFunction.characterPairing (mackeyClassFunction t H H (ClassFunction.ofFDRep A))
          (ClassFunction.comap ((mackeySubgroup t H H).subgroupOf H).subtype
            (ClassFunction.ofFDRep A)) =
        (Module.finrank k (resFDRep ((mackeySubgroup t H H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH t H H)).obj A) : k) := by
    intro t
    let : Invertible (Nat.card ((mackeySubgroup t H H).subgroupOf H) : k) :=
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne')).invertible
    rw [← ofFDRep_res_mackeyToH, ClassFunction.comap_subtype_ofFDRep,
      ClassFunction.characterPairing_ofFDRep_eq_finrank]
  have hpair := characterPairing_mackeyClassFunction_conj hh₁ hh₂ s (ClassFunction.ofFDRep A)
  rw [key, key] at hpair
  exact_mod_cast hpair

/-- **The Mackey irreducibility criterion.**  The representation induced from `A` is irreducible
exactly when `A` is irreducible and, for every double coset `HsH` other than `H` itself, the
restrictions of `A` and of its conjugate `{}^s A` to the Mackey subgroup `H ⊓ sHs⁻¹` are disjoint:
they admit no nonzero intertwiner.

The proof reads the intertwining-number formula
`TauCeti.finrank_hom_indFDRep_mackey_erase` as an identity of natural numbers.  The identity double
coset contributes `dim End_H A`, which is `1` exactly when `A` is irreducible, and every remaining
summand is a dimension, so their total is `0` exactly when each of them is. -/
theorem simple_indFDRep_iff (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G), D ≠ DoubleCoset.mk H H 1 →
        Module.finrank k (resFDRep ((mackeySubgroup D.out H H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH D.out H H)).obj A) = 0 := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have : NeZero (Nat.card H : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [FDRep.simple_iff_end_is_rank_one, FDRep.simple_iff_end_is_rank_one,
    finrank_hom_indFDRep_mackey_erase A]
  constructor
  · intro h
    -- If `A` had no nonzero endomorphism it would be a zero object, and then every Mackey term
    -- would vanish as well, leaving `0 = 1`.
    have hA : Module.finrank k (A ⟶ A) ≠ 0 := by
      intro h0
      rw [h0, Finset.sum_eq_zero fun D _ =>
        finrank_hom_eq_zero_of_isZero (isZero_res_obj _ (isZero_of_finrank_end_eq_zero A h0))] at h
      exact absurd h (by norm_num)
    obtain ⟨h1, h2⟩ := (Nat.add_eq_one_iff.mp h).resolve_left fun hc => hA hc.1
    exact ⟨h1, fun D hD => Finset.sum_eq_zero_iff.mp h2 D (Finset.mem_erase.mpr ⟨hD, by simp⟩)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, Finset.sum_eq_zero fun D hD => h2 D (Finset.mem_erase.mp hD).1, add_zero]

/-- **The Mackey irreducibility criterion, elementwise.**  The disjointness condition of
`TauCeti.simple_indFDRep_iff` may equally be asked of every element `s ∉ H` rather than of one
chosen representative of every non-identity double coset, because the Mackey term is constant on a
double coset (`TauCeti.finrank_hom_res_mackeyToH_conj`) and the double cosets meeting `H` are the
identity one (`TauCeti.doubleCoset_mk_eq_mk_one_iff`). -/
theorem simple_indFDRep_iff_forall_notMem (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ s ∉ H, Module.finrank k (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) = 0 := by
  rw [simple_indFDRep_iff]
  refine and_congr_right fun _ => ⟨fun h s hs => ?_, fun h D hD => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      (DoubleCoset.eq H H (DoubleCoset.mk H H s).out s).mp (DoubleCoset.out_eq' H H _)
    exact hab ▸ (finrank_hom_res_mackeyToH_conj A ha hb _).trans
      (h _ fun hc => hs ((doubleCoset_mk_eq_mk_one_iff H s).mp hc))
  · exact h D.out fun hmem =>
      hD ((DoubleCoset.out_eq' H H D).symm.trans ((doubleCoset_mk_eq_mk_one_iff H D.out).mpr hmem))

/-- **The Mackey irreducibility criterion**, with the disjointness of the two restrictions in the
form the name suggests: they admit no nonzero intertwiner at all. -/
theorem simple_indFDRep_iff_subsingleton (A : FDRep k H) :
    Simple (indFDRep A) ↔ Simple A ∧
      ∀ s ∉ H, Subsingleton (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) := by
  rw [simple_indFDRep_iff_forall_notMem]
  exact and_congr_right fun _ =>
    forall_congr' fun _ => imp_congr_right fun _ => Module.finrank_zero_iff

end Criterion

end TauCeti
