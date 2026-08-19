/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Finite
public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.Conjugate
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup

/-!
# The Mackey decomposition formula

Let `H` and `K` be subgroups of a group `G`, with `H` of finite index.  Restricting to `K` a
representation induced from `H` decomposes as a sum indexed by the double cosets `K \ G / H`: the
summand attached to a representative `s` is the conjugate `{}^s A`, a representation of `sHs⁻¹`,
restricted to the Mackey subgroup `K ⊓ sHs⁻¹` and induced back up to `K`.

This file proves that decomposition on characters, and on the class functions underneath them.
The combinatorial spine is `TauCeti.mackeyQuotientEquiv`: the left cosets `G ⧸ H` are the disjoint
union, over the double cosets `K \ G / H`, of the `K`-orbits, and the orbit of `sH` is a copy of
`K ⧸ (K ⊓ sHs⁻¹)` because `K ⊓ sHs⁻¹` is the stabilizer of `sH`
(`TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`).  Sorting the induced-character sum
`TauCeti.character_indFDRep_sum_quotient` along that bijection is the whole proof: the coset
`u s H` contributes `χ(s⁻¹ u⁻¹ x u s)` exactly when `u⁻¹ x u` lies in the Mackey subgroup, which is
the summand of the induced class function on `K`.

Counting the same bijection instead of summing over it gives the classical index formula
`[G : H] = ∑_{KsH} [K : K ⊓ sHs⁻¹]` (`TauCeti.index_eq_sum_relIndex_mackeySubgroup`), the
dimension shadow of the decomposition.

The summands are built from the fixed representatives `Quotient.out`, as the roadmap prescribes:
no representative-independent summand is asserted, only that a different representative gives a
conjugate Mackey subgroup (`TauCeti.mackeySubgroup_conj`).

## Main definitions

* `TauCeti.mackeyCoset`: the injection `K ⧸ (K ⊓ sHs⁻¹) → G ⧸ H`, `u ↦ u s H`, whose image is the
  `K`-orbit of `sH`.
* `TauCeti.mackeyQuotientEquiv`: the resulting bijection
  `(Σ KsH ∈ K \ G / H, K ⧸ (K ⊓ sHs⁻¹)) ≃ G ⧸ H`.
* `TauCeti.mackeyToH`: the homomorphism `K ⊓ sHs⁻¹ → H`, `y ↦ s⁻¹ y s`, along which the Mackey
  summand pulls a representation of `H` back to the Mackey subgroup.
* `TauCeti.mackeyClassFun`: the conjugated function `y ↦ f (s⁻¹ y s)` on the Mackey subgroup; it is
  a class function as soon as `f` is one, and inducing it up to `K` gives the character of the
  Mackey summand when `f` is a character.
* `TauCeti.mackeyClassFunction`: the same conjugated class function, bundled as an element of
  `TauCeti.ClassFunction`.
* `TauCeti.mackeySummand`: the Mackey summand `Ind_{K ⊓ sHs⁻¹}^K Res ({}^s A)` as an `FDRep k K`.

## Main statements

* `TauCeti.index_eq_sum_relIndex_mackeySubgroup`: `[G : H] = ∑_{KsH} [K : K ⊓ sHs⁻¹]`.
* `TauCeti.mackeyClassFun_mem_classFunction`: the conjugate of a class function is one.
* `TauCeti.indClassFun_mackey`: the Mackey decomposition for induced class functions.
* `TauCeti.comap_subtype_ind_mackey`: the same decomposition as an identity of bundled class
  functions.
* `TauCeti.character_resFDRep_indFDRep_mackey`: the Mackey decomposition for the character of
  `Res_K (Ind_H^G A)`.

## Implementation notes

The formulas summed over `K \ G / H` are stated with `H` of finite index and **no finiteness
hypothesis on `G` or `K`**: that is all the induced class function needs, it makes `K \ G / H`
finite (`TauCeti.finite_doubleCosetQuotient`) and the Mackey subgroup of finite index in `K`
(`TauCeti.instIsFiniteRelIndexMackeySubgroup`), and it is the hypothesis the induced-character
formula carries.  An individual summand needs less: `TauCeti.mackeySummand` and its companions
assume only `[(mackeySubgroup s H K).IsFiniteRelIndex K]`, the finiteness that inducing from the
Mackey subgroup up to `K` actually uses.

The Mackey subgroup `K ⊓ sHs⁻¹` is a subgroup of `G`; inducing from it up to `K` means inducing
along the subtype of `(K ⊓ sHs⁻¹).subgroupOf K : Subgroup ↥K`, so that is the subgroup the sums
below are indexed by.  `TauCeti.mackeyToH` absorbs the passage back and forth, and
`TauCeti.mackeySummand_eq_indFDRep_res_conjFDRep` records that the summand really is the
restriction of the conjugate representation that the roadmap describes.

Only the character form is proved here; the isomorphism of representations
`Res_K (Ind_H^G A) ≅ ⨁_{KsH} Ind_{K ⊓ sHs⁻¹}^K Res ({}^s A)` refining it is not.

## References

Layer 3b of
[the induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md).

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.3.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u

section Coset

variable {G : Type*} [Group G]

/-- The left cosets of `H` in the double coset `KsH`, indexed by the Mackey subgroup:
`u (K ⊓ sHs⁻¹) ↦ u s H`.  It is well defined because `K ⊓ sHs⁻¹` is the stabilizer of `sH` for the
translation action of `K` on `G ⧸ H` (`TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`). -/
def mackeyCoset (s : G) (H K : Subgroup G) :
    K ⧸ (mackeySubgroup s H K).subgroupOf K → G ⧸ H :=
  Quotient.map' (fun u : K => (u : G) * s) fun u v huv => by
    have hmem := (mem_mackeySubgroup_iff.mp
      (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv))).2
    have heq : ((u : G) * s)⁻¹ * ((v : G) * s) = s⁻¹ * ((u⁻¹ * v : K) : G) * s := by
      push_cast
      group
    rw [QuotientGroup.leftRel_apply, heq]
    exact hmem

@[simp]
theorem mackeyCoset_mk (s : G) (H K : Subgroup G) (u : K) :
    mackeyCoset s H K (QuotientGroup.mk u) = QuotientGroup.mk ((u : G) * s) :=
  (rfl)

/-- `TauCeti.mackeyCoset` evaluated at the chosen representative of a coset. -/
theorem mackeyCoset_out (s : G) (H K : Subgroup G)
    (u : K ⧸ (mackeySubgroup s H K).subgroupOf K) :
    mackeyCoset s H K u = QuotientGroup.mk ((u.out : G) * s) := by
  rw [← mackeyCoset_mk s H K u.out, QuotientGroup.out_eq']

/-- **The double-coset splitting of `G ⧸ H`.**  Sorting the left cosets of `H` by the double coset
they lie in, `G ⧸ H` is the disjoint union over `K \ G / H` of the `K`-orbits, and the orbit of
`sH` is a copy of `K ⧸ (K ⊓ sHs⁻¹)`.

This is the combinatorial content of the Mackey decomposition; the representatives are the fixed
`Quotient.out` ones. -/
noncomputable def mackeyQuotientEquiv (H K : Subgroup G) :
    (Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        K ⧸ (mackeySubgroup D.out H K).subgroupOf K) ≃ G ⧸ H :=
  Equiv.ofBijective (fun p => mackeyCoset p.1.out H K p.2) (by
    constructor
    · rintro ⟨D, u⟩ ⟨D', v⟩ hp
      simp only [mackeyCoset_out, QuotientGroup.eq] at hp
      -- The two representatives lie in one double coset, so the double cosets agree.
      have hD : D = D' := by
        have hmk := (DoubleCoset.eq K H D.out D'.out).mpr
          ⟨(v.out : G)⁻¹ * (u.out : G),
            K.mul_mem (K.inv_mem (SetLike.coe_mem v.out)) (SetLike.coe_mem u.out), _, hp, by
              group⟩
        rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at hmk
      subst hD
      -- With one representative fixed, the two cosets of the Mackey subgroup agree.
      have huv : u = v := by
        rw [← QuotientGroup.out_eq' u, ← QuotientGroup.out_eq' v, QuotientGroup.eq,
          Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]
        refine ⟨?_, ?_⟩
        · exact SetLike.coe_mem _
        · have heq : (D.out)⁻¹ * ((u.out⁻¹ * v.out : K) : G) * D.out
              = ((u.out : G) * D.out)⁻¹ * ((v.out : G) * D.out) := by
            push_cast
            group
          rw [heq]
          exact hp
      rw [huv]
    · intro t
      obtain ⟨a, ha, b, hb, hab⟩ :=
        (DoubleCoset.eq K H (DoubleCoset.mk K H t.out).out t.out).mp
          (DoubleCoset.out_eq' K H (DoubleCoset.mk K H t.out))
      refine ⟨⟨DoubleCoset.mk K H t.out, QuotientGroup.mk ⟨a, ha⟩⟩, ?_⟩
      simp only [mackeyCoset_mk]
      conv_rhs => rw [← QuotientGroup.out_eq' t]
      rw [QuotientGroup.eq]
      -- `t.out = a * s * b` with `b ∈ H`, so the two cosets differ by `b`.
      have hrw : (a * (DoubleCoset.mk K H t.out).out)⁻¹ * t.out = b :=
        (congrArg (fun z => (a * (DoubleCoset.mk K H t.out).out)⁻¹ * z) hab).trans (by group)
      rw [hrw]
      exact hb)

@[simp]
theorem mackeyQuotientEquiv_apply (H K : Subgroup G)
    (p : Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        K ⧸ (mackeySubgroup D.out H K).subgroupOf K) :
    mackeyQuotientEquiv H K p = mackeyCoset p.1.out H K p.2 :=
  (rfl)

/-- **The double-coset index formula** `[G : H] = ∑_{KsH ∈ K \ G / H} [K : K ⊓ sHs⁻¹]`, obtained by
counting `TauCeti.mackeyQuotientEquiv`.  It is the dimension shadow of the Mackey decomposition:
applying `TauCeti.character_resFDRep_indFDRep_mackey` at the identity recovers it, multiplied by
`finrank k A`. -/
theorem index_eq_sum_relIndex_mackeySubgroup (H K : Subgroup G) [H.FiniteIndex] :
    H.index =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        (mackeySubgroup D.out H K).relIndex K := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  let (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) :
      Fintype (K ⧸ (mackeySubgroup D.out H K).subgroupOf K) := Fintype.ofFinite _
  calc H.index
      = Nat.card (G ⧸ H) := H.index_eq_card
    _ = Nat.card (Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          K ⧸ (mackeySubgroup D.out H K).subgroupOf K) :=
        (Nat.card_congr (mackeyQuotientEquiv H K)).symm
    _ = Fintype.card (Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          K ⧸ (mackeySubgroup D.out H K).subgroupOf K) := Nat.card_eq_fintype_card
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          Fintype.card (K ⧸ (mackeySubgroup D.out H K).subgroupOf K) := Fintype.card_sigma
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          (mackeySubgroup D.out H K).relIndex K :=
        Finset.sum_congr rfl fun D _ => by
          rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

variable (s : G) (H K : Subgroup G)

/-- The homomorphism `K ⊓ sHs⁻¹ → H`, `y ↦ s⁻¹ y s`, along which the Mackey summand pulls a
representation of `H` back to the Mackey subgroup: the Mackey subgroup sits inside `sHs⁻¹`
(`TauCeti.mackeyToConjH`) and `TauCeti.conjSubgroupEquiv` carries `sHs⁻¹` back to `H`.

Its source is `(K ⊓ sHs⁻¹).subgroupOf K`, the Mackey subgroup read as a subgroup of `K`, since
that is the subgroup the Mackey summand is induced along. -/
def mackeyToH : ((mackeySubgroup s H K).subgroupOf K) →* H :=
  ((conjSubgroupEquiv s H).toMonoidHom.comp (mackeyToConjH s H K)).comp
    (Subgroup.subgroupOfEquivOfLe mackeySubgroup_le_right).toMonoidHom

@[simp]
theorem coe_mackeyToH_apply (y : (mackeySubgroup s H K).subgroupOf K) :
    (mackeyToH s H K y : G) = s⁻¹ * ((y : K) : G) * s := by
  simp [mackeyToH]

end Coset

section ClassFun

variable {k : Type*} [Semiring k] {G : Type*} [Group G] {H K : Subgroup G}

/-- The function on the Mackey subgroup obtained from an arbitrary function `f` on `H` by
conjugating: `y ↦ f (s⁻¹ y s)`, that is, the pullback of `f` along `TauCeti.mackeyToH`.

It is a class function whenever `f` is one (`TauCeti.mackeyClassFun_mem_classFunction`), and when
`f` is the character of a representation `A` its induction to `K` is the character of the Mackey
summand attached to `s` (`TauCeti.character_mackeySummand`); nothing is assumed of `f` here. -/
def mackeyClassFun (s : G) (H K : Subgroup G) (f : H → k) :
    ((mackeySubgroup s H K).subgroupOf K) → k :=
  f ∘ mackeyToH s H K

omit [Semiring k] in
@[simp]
theorem mackeyClassFun_apply (s : G) (H K : Subgroup G) (f : H → k)
    (y : (mackeySubgroup s H K).subgroupOf K) :
    mackeyClassFun s H K f y = f (mackeyToH s H K y) :=
  (rfl)

/-- Conjugating a class function on `H` gives a class function on the Mackey subgroup: it is the
pullback of `f` along the homomorphism `TauCeti.mackeyToH`. -/
theorem mackeyClassFun_mem_classFunction (s : G) (H K : Subgroup G) {f : H → k}
    (hf : f ∈ ClassFunction k H) :
    mackeyClassFun s H K f ∈ ClassFunction k ((mackeySubgroup s H K).subgroupOf K) :=
  ClassFunction.mem_iff.mpr fun y c => by
    rw [mackeyClassFun_apply, mackeyClassFun_apply, map_mul, map_mul, map_inv]
    exact ClassFunction.mem_iff.mp hf _ _

/-- The conjugated class function `TauCeti.mackeyClassFun` on the Mackey subgroup, bundled as an
element of `TauCeti.ClassFunction`. -/
def mackeyClassFunction (s : G) (H K : Subgroup G) (f : ClassFunction k H) :
    ClassFunction k ((mackeySubgroup s H K).subgroupOf K) :=
  ⟨mackeyClassFun s H K f.1, mackeyClassFun_mem_classFunction s H K f.2⟩

@[simp]
theorem mackeyClassFunction_coe (s : G) (H K : Subgroup G) (f : ClassFunction k H) :
    (mackeyClassFunction s H K f).1 = mackeyClassFun s H K f.1 :=
  (rfl)

/-- **The Mackey subgroup sees the induced summand.**  The summand of the class function induced
from `H` to `G`, taken at the representative `u s` and at an element of `K`, is the summand of the
class function induced from the Mackey subgroup to `K`, taken at the representative `u`.

This single identity is where the conjugation `s⁻¹ (·) s` enters the Mackey decomposition.  It is
private: it speaks about the individual representatives that `TauCeti.indClassFun_mackey` sums
over, and that sum is the interface. -/
private theorem indTerm_mackeyClassFun (s : G) (H K : Subgroup G) (f : H → k) (x u : K) :
    indTerm f (x : G) ((u : G) * s) = indTerm (mackeyClassFun s H K f) x u := by
  classical
  have hconj : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s)
      = s⁻¹ * ((u⁻¹ * x * u : K) : G) * s := by
    push_cast
    group
  have hiff : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s) ∈ H ↔
      u⁻¹ * x * u ∈ (mackeySubgroup s H K).subgroupOf K := by
    rw [hconj, Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]
    exact ⟨fun h => ⟨SetLike.coe_mem _, h⟩, fun h => h.2⟩
  rw [indTerm_apply, indTerm_apply]
  by_cases hmem : ((u : G) * s)⁻¹ * (x : G) * ((u : G) * s) ∈ H
  · rw [dite_eq_left hmem, dite_eq_left (hiff.mp hmem), mackeyClassFun_apply]
    exact congrArg f (Subtype.ext (by rw [coe_mackeyToH_apply]; exact hconj))
  · rw [dite_eq_right hmem, dite_eq_right fun h => hmem (hiff.mpr h)]

/-- **The Mackey decomposition formula for class functions.**  For a class function `f` on a
finite-index subgroup `H` and an element `x` of a subgroup `K`, the induced class function
`Ind_H^G f` evaluated at `x` is the sum, over the double cosets `K \ G / H`, of the class functions
induced to `K` from the Mackey subgroups.

The character form is `TauCeti.character_resFDRep_indFDRep_mackey`. -/
theorem indClassFun_mackey [H.FiniteIndex] {f : H → k} (hf : f ∈ ClassFunction k H) (x : K) :
    indClassFun H f (x : G) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        indClassFun ((mackeySubgroup D.out H K).subgroupOf K)
          (mackeyClassFun D.out H K f) x := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  let := Fintype.ofFinite (G ⧸ H)
  let (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) :
      Fintype (K ⧸ (mackeySubgroup D.out H K).subgroupOf K) := Fintype.ofFinite _
  calc indClassFun H f (x : G)
      = ∑ t : G ⧸ H, indTerm f (x : G) t.out := by
        rw [indClassFun_apply]
        exact Finset.sum_congr rfl fun t _ => (indTerm_apply _ _ _).symm
    _ = ∑ p : Σ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
            K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
          indTerm f (x : G) (mackeyQuotientEquiv H K p).out :=
        (Equiv.sum_comp (mackeyQuotientEquiv H K) _).symm
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          ∑ u : K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
            indTerm f (x : G) ((u.out : G) * D.out) := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun u _ => ?_
        -- The two representatives `(Φ ⟨D, u⟩).out` and `u.out * D.out` span one coset of `H`.
        refine indTerm_eq_of_mk_eq hf _ _ _ ?_
        rw [QuotientGroup.out_eq']
        exact (mackeyQuotientEquiv_apply H K ⟨D, u⟩).trans (mackeyCoset_out _ _ _ _)
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          ∑ u : K ⧸ (mackeySubgroup D.out H K).subgroupOf K,
            indTerm (mackeyClassFun D.out H K f) x u.out :=
        Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun u _ =>
          indTerm_mackeyClassFun _ _ _ _ _ _
    _ = ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
          indClassFun ((mackeySubgroup D.out H K).subgroupOf K)
            (mackeyClassFun D.out H K f) x :=
        Finset.sum_congr rfl fun D _ => by
          rw [indClassFun_apply]
          exact Finset.sum_congr rfl fun u _ => indTerm_apply _ _ _

/-- **The Mackey decomposition of a restricted induced class function.**  Restricting to `K` a
class function induced from `H` gives the sum, over the double cosets `K \ G / H`, of the class
functions induced to `K` from the Mackey subgroups.

This is `TauCeti.indClassFun_mackey` rewritten as an identity of bundled class functions, which is
the form the character pairing consumes. -/
theorem comap_subtype_ind_mackey (K : Subgroup G) [H.FiniteIndex] (f : ClassFunction k H) :
    ClassFunction.comap K.subtype (ClassFunction.ind H f) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        ClassFunction.ind ((mackeySubgroup D.out H K).subgroupOf K)
          (mackeyClassFunction D.out H K f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  refine Subtype.ext (funext fun x => ?_)
  rw [ClassFunction.comap_apply, ClassFunction.ind_apply, Subgroup.coe_subtype]
  simp only [Submodule.coe_sum, Finset.sum_apply, ClassFunction.ind_apply,
    mackeyClassFunction_coe]
  exact indClassFun_mackey f.2 x

end ClassFun

section Character

variable {k G : Type u} [Field k] [Group G] {H K : Subgroup G}

/-- **The Mackey summand** attached to a representative `s` of a double coset in `K \ G / H`: the
conjugate representation `{}^s A` of `sHs⁻¹`, restricted to the Mackey subgroup `K ⊓ sHs⁻¹` and
induced back up to `K`.

The restriction and the conjugation are packaged into the single homomorphism
`TauCeti.mackeyToH`; `TauCeti.mackeySummand_eq_indFDRep_res_conjFDRep` unfolds it into the two
steps the roadmap names.

Only the Mackey subgroup is assumed of finite index in `K`, which is what inducing up to `K`
uses; `H` of finite index in `G` gives that for every `s`
(`TauCeti.instIsFiniteRelIndexMackeySubgroup`). -/
noncomputable def mackeySummand (s : G) [(mackeySubgroup s H K).IsFiniteRelIndex K]
    (A : FDRep k H) : FDRep k K :=
  indFDRep ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A)

/-- The Mackey summand is what its name says: restrict the conjugate representation `{}^s A` along
the inclusion of the Mackey subgroup into `sHs⁻¹`, then induce up to `K`.  The remaining
restriction is along the identification of `K ⊓ sHs⁻¹` with its copy inside `K`. -/
theorem mackeySummand_eq_indFDRep_res_conjFDRep (s : G)
    [(mackeySubgroup s H K).IsFiniteRelIndex K] (A : FDRep k H) :
    mackeySummand (K := K) s A =
      indFDRep ((Action.res (FGModuleCat k)
          (Subgroup.subgroupOfEquivOfLe
            (mackeySubgroup_le_right (s := s) (H := H) (K := K))).toMonoidHom).obj
        ((Action.res (FGModuleCat k) (mackeyToConjH s H K)).obj (conjFDRep s A))) := by
  -- `mackeyToH` is a composite of three homomorphisms; `actionRes_comp` splits its restriction
  -- into the corresponding three restrictions, the outer two of which are the ones stated.
  simp only [mackeySummand, mackeyToH, actionRes_comp, CategoryTheory.Functor.comp_obj,
    MulEquiv.toMonoidHom_eq_coe, res_obj_eq_conjFDRep]

/-- The character of the representation the Mackey summand is induced from: pulling `A` back along
`TauCeti.mackeyToH` conjugates its character, `y ↦ χ_A (s⁻¹ y s)`.  Naming this identification
keeps `Action.res` out of the character computations below. -/
@[simp]
theorem character_res_mackeyToH (s : G) (A : FDRep k H) :
    FDRep.character ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A) =
      mackeyClassFun s H K A.character := by
  funext y
  rw [mackeyClassFun_apply, FDRep.character, FDRep.character]
  congr 1

/-- The character of a Mackey summand is the induced class function of the conjugated character. -/
@[simp]
theorem character_mackeySummand (s : G) [(mackeySubgroup s H K).IsFiniteRelIndex K]
    (A : FDRep k H) (x : K) :
    (mackeySummand (K := K) s A).character x =
      indClassFun ((mackeySubgroup s H K).subgroupOf K)
        (mackeyClassFun s H K A.character) x := by
  rw [mackeySummand, ← indClassFun_ofFDRep_character, character_res_mackeyToH]

/-- **The Mackey decomposition formula, character form.**  For a finite-dimensional representation
`A` of a finite-index subgroup `H` and an element `x` of a subgroup `K`, the character of
`Res_K (Ind_H^G A)` at `x` is the sum, over the double cosets `K \ G / H`, of the characters of
the Mackey summands.

This is the formula the roadmap states.  The character of `Ind_H^G A` at `x : K`, read on `G`, is
the same number: `TauCeti.character_resFDRep` is a `simp` lemma rewriting the left-hand side into
it. -/
theorem character_resFDRep_indFDRep_mackey [H.FiniteIndex] (A : FDRep k H) (x : K) :
    (resFDRep K (indFDRep A)).character x =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
      ∑ D : DoubleCoset.Quotient (K : Set G) (H : Set G),
        (mackeySummand (K := K) D.out A).character x := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (K : Set G) (H : Set G))
  rw [character_resFDRep]
  simp only [character_mackeySummand]
  rw [← indClassFun_ofFDRep_character]
  exact indClassFun_mackey (ClassFunction.mem_iff.mpr A.char_conj) x

end Character

end TauCeti
