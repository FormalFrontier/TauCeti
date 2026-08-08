/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Trivial-intersection subgroups and Frobenius complements

A subgroup `H` of `G` is a **trivial-intersection subgroup** when it meets each of its distinct
conjugates trivially: `H ⊓ g H g⁻¹ = ⊥` whenever `g ∉ H`.  Equivalently `H` is *malnormal*: a
nonidentity element of `H` is conjugated out of `H` by every `g ∉ H`.  A **Frobenius complement**
is such a subgroup that is in addition proper and nontrivial, and `G` is then called a Frobenius
group with complement `H`.

The elementwise form is the definition taken here, because it is what every proof uses; the
lattice form is `TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot`.

Alongside the subgroup notion there is a set-level one.  A **trivial-intersection set** for `H` is
a subset `S ⊆ H` normalized by `H` whose distinct `G`-conjugates are pairwise disjoint.  The
example that matters is the nonidentity part `H# = (H : Set G) \ {1}` of a Frobenius complement
(`TauCeti.IsFrobeniusComplement.isTISet_diff_one`): a class function on `H` supported on such an
`S` induces to `G` without changing its norm, which is the input to the exceptional-character
argument for Frobenius's theorem.  That induction statement is
`TauCeti.characterPairing_ind_ind_of_isTISet`, in
`TauCeti/RepresentationTheory/Induction/TrivialIntersection.lean`.

## Main definitions

* `TauCeti.IsTISubgroup`: `H` meets each of its distinct conjugates trivially.
* `TauCeti.IsTISet`: `S` is a trivial-intersection set relative to `H`.
* `TauCeti.IsFrobeniusComplement`: `H` is a proper nontrivial trivial-intersection subgroup.

## Main results

* `TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot`: the lattice form of the definition.
* `TauCeti.IsTISubgroup.normalizer_eq_self`: a nontrivial trivial-intersection subgroup is
  self-normalizing.
* `TauCeti.IsTISubgroup.isTISet`: an `H`-invariant subset of `H` avoiding the identity is a
  trivial-intersection set, and in particular so is the nonidentity part of `H`.
* `TauCeti.IsTISet.one_notMem`: conversely, a trivial-intersection set for a proper subgroup
  avoids the identity.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 7.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8 (`IsTISet`, `IsFrobeniusComplement`).
-/

public section

namespace TauCeti

open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G} {S : Set G}

/-! ### Trivial-intersection subgroups -/

/-- **A trivial-intersection subgroup**: `H` meets each of its distinct conjugates trivially.
Stated elementwise, as the malnormality condition that only the identity of `H` can be conjugated
back into `H` by an element outside `H`; `TauCeti.isTISubgroup_iff_inf_conj_smul_eq_bot` is the
equivalent statement `H ⊓ g H g⁻¹ = ⊥` about the subgroup lattice. -/
def IsTISubgroup (H : Subgroup G) : Prop :=
  ∀ ⦃g x : G⦄, g ∉ H → x ∈ H → g * x * g⁻¹ ∈ H → x = 1

namespace IsTISubgroup

/-- The defining property of a trivial-intersection subgroup, as a named lemma. -/
theorem eq_one (hH : IsTISubgroup H) {g x : G} (hg : g ∉ H) (hx : x ∈ H)
    (hgx : g * x * g⁻¹ ∈ H) : x = 1 :=
  hH hg hx hgx

/-- A nonidentity element of a trivial-intersection subgroup is conjugated out of it by every
element outside it. -/
theorem conj_notMem (hH : IsTISubgroup H) {g x : G} (hg : g ∉ H) (hx : x ∈ H) (hx1 : x ≠ 1) :
    g * x * g⁻¹ ∉ H :=
  fun h => hx1 (hH hg hx h)

/-- **A nontrivial trivial-intersection subgroup is self-normalizing.**  An element of the
normalizer conjugates a chosen nonidentity element of `H` back into `H`, so it cannot lie outside
`H`. -/
theorem normalizer_eq_self (hH : IsTISubgroup H) (hne : H ≠ ⊥) :
    Subgroup.normalizer (H : Set G) = H := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  by_contra hgH
  exact hx1 (Subtype.ext (hH hgH hx ((Subgroup.mem_normalizer_iff.mp hg x).mp hx)))

end IsTISubgroup

/-- **The lattice form of the trivial-intersection condition**: `H` meets each conjugate
`g H g⁻¹` with `g ∉ H` in the trivial subgroup.  This is how the condition is usually written; the
elementwise `TauCeti.IsTISubgroup` is the form the proofs use. -/
theorem isTISubgroup_iff_inf_conj_smul_eq_bot :
    IsTISubgroup H ↔ ∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥ := by
  have key : ∀ g y : G, y ∈ MulAut.conj g • H ↔ g⁻¹ * y * g ∈ H := by
    intro g y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  constructor
  · intro hH g hg
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    obtain ⟨hyH, hyc⟩ := Subgroup.mem_inf.mp hy
    exact hH (g := g⁻¹) (by simpa using hg) hyH (by simpa using (key g y).mp hyc)
  · intro hH g x hg hx hgx
    have hmem : g * x * g⁻¹ ∈ H ⊓ MulAut.conj g • H :=
      Subgroup.mem_inf.mpr ⟨hgx, (key g _).mpr (by simpa [mul_assoc] using hx)⟩
    have h1 : g * x * g⁻¹ = 1 := (Subgroup.eq_bot_iff_forall _).mp (hH g hg) _ hmem
    exact mul_eq_left.mp (mul_inv_eq_one.mp h1)

/-! ### Trivial-intersection sets -/

/-- **A trivial-intersection set** for `H`: a subset of `H`, normalized by `H`, whose
`G`-conjugates by elements outside `H` are disjoint from it.  Since conjugation by an element of
`H` fixes `S`, the conjugates of `S` are indexed by the cosets of `H`, and the condition says that
the distinct ones are pairwise disjoint.

The motivating example is the nonidentity part `(H : Set G) \ {1}` of a trivial-intersection
subgroup (`TauCeti.IsTISubgroup.isTISet_diff_one`). -/
structure IsTISet (S : Set G) (H : Subgroup G) : Prop where
  /-- A trivial-intersection set is contained in its subgroup. -/
  subset : S ⊆ (H : Set G)
  /-- A trivial-intersection set is normalized by its subgroup. -/
  conj_mem : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S
  /-- Conjugating a trivial-intersection set by an element outside its subgroup moves it off
  itself. -/
  disjoint_conj : ∀ g : G, g ∉ H → ∀ x ∈ S, g * x * g⁻¹ ∉ S

namespace IsTISet

/-- The image of a trivial-intersection set under conjugation by an element of its subgroup is the
set itself; the two inclusions come from `TauCeti.IsTISet.conj_mem` at `h` and at `h⁻¹`. -/
theorem conj_image_eq (hS : IsTISet S H) {h : G} (hh : h ∈ H) :
    (fun x => h * x * h⁻¹) '' S = S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hS.conj_mem h hh x hx
  · intro x hx
    refine ⟨h⁻¹ * x * h, ?_, ?_⟩
    · simpa using hS.conj_mem h⁻¹ (H.inv_mem hh) x hx
    · group

/-- **Distinct conjugates of a trivial-intersection set are disjoint**, in the form the name of the
notion refers to. -/
theorem disjoint_conj_image (hS : IsTISet S H) {g : G} (hg : g ∉ H) :
    Disjoint ((fun x => g * x * g⁻¹) '' S) S :=
  Set.disjoint_left.mpr <| by
    rintro _ ⟨x, hx, rfl⟩
    exact hS.disjoint_conj g hg x hx

/-- **A trivial-intersection set for a proper subgroup avoids the identity.**  The identity is
fixed by every conjugation, so it could not be moved off the set. -/
theorem one_notMem (hS : IsTISet S H) (hH : H ≠ ⊤) : (1 : G) ∉ S := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    exact hH ((Subgroup.eq_top_iff' H).mpr (by simpa using h))
  intro h1
  exact hS.disjoint_conj g hg 1 h1 (by simpa using h1)

end IsTISet

/-- **An `H`-invariant subset of `H` avoiding the identity is a trivial-intersection set.**  This
is where the trivial-intersection condition on the subgroup does the work: an element of `S`
conjugated by some `g ∉ H` back into `H` would have to be the identity. -/
theorem IsTISubgroup.isTISet (hH : IsTISubgroup H) (hS : S ⊆ (H : Set G)) (h1 : (1 : G) ∉ S)
    (hconj : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S) : IsTISet S H where
  subset := hS
  conj_mem := hconj
  disjoint_conj _g hg _x hx hmem :=
    hH.conj_notMem hg (hS hx) (fun h => h1 (h ▸ hx)) (hS hmem)

/-- **The nonidentity part of a trivial-intersection subgroup is a trivial-intersection set.**
This is the set `H#` the exceptional-character argument induces from. -/
theorem IsTISubgroup.isTISet_diff_one (hH : IsTISubgroup H) :
    IsTISet ((H : Set G) \ {1}) H := by
  refine hH.isTISet Set.sdiff_subset (by simp) fun h hh x hx => ⟨?_, ?_⟩
  · exact H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh)
  · simp only [Set.mem_singleton_iff]
    intro hcon
    exact hx.2 (mul_eq_left.mp (mul_inv_eq_one.mp hcon))

/-! ### Frobenius complements -/

/-- **A Frobenius complement**: a proper, nontrivial trivial-intersection subgroup.  A group with
such a subgroup is a *Frobenius group* with complement `H`; Frobenius's theorem says that the
elements lying in no conjugate of `H`, together with the identity, form a normal complement to
`H`. -/
structure IsFrobeniusComplement (H : Subgroup G) : Prop where
  /-- A Frobenius complement is nontrivial. -/
  ne_bot : H ≠ ⊥
  /-- A Frobenius complement is proper. -/
  ne_top : H ≠ ⊤
  /-- A Frobenius complement meets each of its distinct conjugates trivially. -/
  isTISubgroup : IsTISubgroup H

namespace IsFrobeniusComplement

/-- A Frobenius complement is self-normalizing. -/
theorem normalizer_eq_self (hH : IsFrobeniusComplement H) :
    Subgroup.normalizer (H : Set G) = H :=
  hH.isTISubgroup.normalizer_eq_self hH.ne_bot

/-- The nonidentity part of a Frobenius complement is a trivial-intersection set. -/
theorem isTISet_diff_one (hH : IsFrobeniusComplement H) : IsTISet ((H : Set G) \ {1}) H :=
  hH.isTISubgroup.isTISet_diff_one

/-- **A Frobenius complement is not normal.**  It is self-normalizing and proper, so its
normalizer is not the whole group. -/
theorem not_normal (hH : IsFrobeniusComplement H) : ¬H.Normal := by
  intro hnorm
  have htop : Subgroup.normalizer (H : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hnorm
  exact hH.ne_top (hH.normalizer_eq_self ▸ htop)

end IsFrobeniusComplement

end TauCeti
