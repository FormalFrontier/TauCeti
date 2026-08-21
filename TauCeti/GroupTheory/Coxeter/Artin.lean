/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.Coxeter.Basic

/-!
# Artin-Tits groups

A Coxeter matrix `M` presents two different groups on the same generating set `B`. The Coxeter
group `M.Group` imposes the relations `(s i * s i') ^ M i i' = 1`; equivalently, that each
generator is an involution and that the two alternating words of length `M i i'` in `i` and `i'`
have the same product. Dropping the involution half and keeping only the second half presents the
*Artin-Tits group* (or generalised braid group) of `M`: generators `σ i`, one for each `i : B`,
subject only to

`σ i * σ i' * σ i * ⋯ = σ i' * σ i * σ i' * ⋯` (both sides of length `M i i'`).

The braid group on `n` strands is the Artin-Tits group of the Coxeter matrix of type `A`, and this
file is where its presentation and universal property are proved once and for all; the type-`A`
specialisation is `TauCeti.BraidGroup` in `TauCeti.GroupTheory.SpecificGroups.Braid`.

The alternating words are Mathlib's `CoxeterSystem.braidWord`, so the relator is spelled with
exactly the words that Mathlib's `CoxeterSystem.wordProd_braidWord_eq` proves equal in a Coxeter
group. That is what makes `TauCeti.ArtinGroup.toCoxeterGroup`, the canonical surjection onto the
Coxeter group, a one-line consequence of the universal property.

Two degenerate entries of `M` are worth spelling out, because they are what makes the relator set
above correct rather than merely plausible.

* On the diagonal, `M i i = 1`, and both alternating words are the one-letter word `[i]`, so the
  relator is trivial. In particular **no** relation `σ i * σ i = 1` is imposed: an Artin-Tits
  group is torsion-free-looking on its generators, and indeed `TauCeti.ArtinGroup.orderOf_gen`
  shows every generator has infinite order.
* When `M i i' = 0`, meaning that `s i * s i'` has infinite order in the Coxeter group, both
  alternating words are empty and again no relation is imposed, which is the intended reading.

## Main definitions

* `TauCeti.artinRelation M i i'`: the relator `⟨i i'⟩ * ⟨i' i⟩⁻¹` in `FreeGroup B`, where `⟨i i'⟩`
  denotes the alternating word of length `M i i'` in `i` and `i'` that ends with `i'`.
* `TauCeti.artinRelationsSet M`: the set of all such relators.
* `TauCeti.ArtinGroup M`: the Artin-Tits group of `M`.
* `TauCeti.ArtinGroup.gen M i`: its standard generator at the index `i`.
* `TauCeti.ArtinGroup.lift`: the universal property.
* `TauCeti.ArtinGroup.closure_range_gen` and `TauCeti.ArtinGroup.gen_induction_on`: generation by
  the standard generators and its induction principle.
* `TauCeti.ArtinGroup.toCoxeterGroup`: the canonical map onto a Coxeter group with matrix `M`.
* `TauCeti.ArtinGroup.exponentSum`: the total exponent of a word in the standard generators.

## Main results

* `TauCeti.prod_map_alternatingWord_two` and `TauCeti.prod_map_alternatingWord_three`: the
  rank-two alternating-word evaluation rules used below.
* `TauCeti.ArtinGroup.prod_map_gen_braidWord`: the defining braid relation holds.
* `TauCeti.ArtinGroup.gen_mul_gen_comm` and `TauCeti.ArtinGroup.gen_braid`: the rank-two form of
  that relation, at an entry `M i i' = 2` and at an entry `M i i' = 3`.
* `TauCeti.ArtinGroup.toCoxeterGroup_surjective`: the map to the Coxeter group is surjective.
* `TauCeti.ArtinGroup.hom_ext`: homomorphisms are determined by the standard generators.
* `TauCeti.ArtinGroup.gen_ne_one` and `TauCeti.ArtinGroup.orderOf_gen`: a standard generator is
  nontrivial, indeed of infinite order. These are the non-degeneracy statements which distinguish
  the Artin-Tits presentation from the Coxeter presentation on the same generators.

## References

* E. Artin, *Theorie der Zöpfe*, Abh. Math. Sem. Univ. Hamburg 4 (1925), 47-72.
* E. Brieskorn, K. Saito, *Artin-Gruppen und Coxeter-Gruppen*, Invent. Math. 17 (1972), 245-271.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974).

This file is Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), which asks for "braid closures (over
`PresentedMonoid` braid groups with the Artin relations)" as one of the presentations of a knot.
-/

public section

open Function List

namespace TauCeti

variable {B G W : Type*} [Group G] [Group W]

section Relations

variable (M : CoxeterMatrix B)

/-- The Artin-Tits relator of a Coxeter matrix `M` at a pair of indices: the quotient of the two
alternating words of length `M i i'` in `i` and `i'`. It is trivial when `M i i' ∈ {0, 1}`, in
particular on the diagonal. -/
def artinRelation (i i' : B) : FreeGroup B :=
  ((CoxeterSystem.braidWord M i i').map FreeGroup.of).prod *
    (((CoxeterSystem.braidWord M i' i).map FreeGroup.of).prod)⁻¹

/-- The defining equation of an Artin-Tits relator. -/
theorem artinRelation_def (i i' : B) :
    artinRelation M i i' =
      ((CoxeterSystem.braidWord M i i').map FreeGroup.of).prod *
        (((CoxeterSystem.braidWord M i' i).map FreeGroup.of).prod)⁻¹ :=
  (rfl)

/-- The set of all Artin-Tits relators of a Coxeter matrix. -/
def artinRelationsSet : Set (FreeGroup B) := Set.range (uncurry (artinRelation M))

theorem artinRelation_mem_artinRelationsSet (i i' : B) :
    artinRelation M i i' ∈ artinRelationsSet M :=
  ⟨(i, i'), rfl⟩

@[simp]
theorem mem_artinRelationsSet {r : FreeGroup B} :
    r ∈ artinRelationsSet M ↔ ∃ i i', artinRelation M i i' = r := by
  simp [artinRelationsSet, uncurry, Prod.exists]

/-- The Artin-Tits group of a Coxeter matrix `M`; that is, the group
$$\langle \{σ_i\}_{i ∈ B} \mid \underbrace{σ_i σ_{i'} ⋯}_{M_{i,i'}} =
  \underbrace{σ_{i'} σ_i ⋯}_{M_{i,i'}} \rangle .$$
Unlike the Coxeter group of `M`, the generators are not required to be involutions. -/
abbrev ArtinGroup : Type _ := PresentedGroup (artinRelationsSet M)

/-- The standard generator `σ i` of the Artin-Tits group of `M`. -/
def ArtinGroup.gen (i : B) : ArtinGroup M := PresentedGroup.of i

/-- Mathlib's presented-group generator is the standard Artin-Tits generator. -/
@[simp]
theorem ArtinGroup.of_eq_gen (i : B) :
    (PresentedGroup.of i : ArtinGroup M) = ArtinGroup.gen M i :=
  (rfl)

/-- The standard generators generate the Artin-Tits group. -/
@[simp]
theorem ArtinGroup.closure_range_gen :
    Subgroup.closure (Set.range (ArtinGroup.gen M)) = ⊤ := by
  have hof : (PresentedGroup.of : B → ArtinGroup M) = ArtinGroup.gen M := by
    funext i
    exact ArtinGroup.of_eq_gen M i
  rw [← hof]
  exact PresentedGroup.closure_range_of (artinRelationsSet M)

/-- To prove a predicate for every Artin-Tits group element, it suffices to prove it for the
identity and standard generators and show that it is preserved by multiplication and inverse. -/
theorem ArtinGroup.gen_induction_on {p : ArtinGroup M → Prop} (g : ArtinGroup M)
    (gen : ∀ i : B, p (ArtinGroup.gen M i)) (one : p 1)
    (mul : ∀ g g' : ArtinGroup M, p g → p g' → p (g * g'))
    (inv : ∀ g : ArtinGroup M, p g → p g⁻¹) : p g := by
  have hg : g ∈ Subgroup.closure (Set.range (ArtinGroup.gen M)) := by
    rw [ArtinGroup.closure_range_gen]
    exact Subgroup.mem_top g
  exact Subgroup.closure_induction
    (fun x ⟨i, hi⟩ ↦ hi ▸ gen i) one
    (fun x y _ _ hx hy ↦ mul x y hx hy) (fun x _ hx ↦ inv x hx) hg

/-- The defining relation of the Artin-Tits group: the two alternating words of length `M i i'`
in the standard generators `σ i` and `σ i'` have the same product. -/
theorem ArtinGroup.prod_map_gen_braidWord (i i' : B) :
    ((CoxeterSystem.braidWord M i i').map (ArtinGroup.gen M)).prod =
      ((CoxeterSystem.braidWord M i' i).map (ArtinGroup.gen M)).prod := by
  have hmem := artinRelation_mem_artinRelationsSet M i i'
  rw [artinRelation_def] at hmem
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem
  rw [← List.prod_map_hom, ← List.prod_map_hom] at h
  have hof : (⇑(PresentedGroup.mk (artinRelationsSet M)) ∘ FreeGroup.of) =
      ArtinGroup.gen M := by
    funext j
    exact ArtinGroup.of_eq_gen M j
  rw [hof] at h
  exact h

/-- Two standard generators commute when the corresponding entry of `M` is `2`. -/
theorem ArtinGroup.gen_mul_gen_comm {i i' : B} (h : M i i' = 2) :
    ArtinGroup.gen M i * ArtinGroup.gen M i' = ArtinGroup.gen M i' * ArtinGroup.gen M i := by
  have h' : M i' i = 2 := by rw [M.symmetric i' i]; exact h
  have hb := ArtinGroup.prod_map_gen_braidWord M i i'
  rw [CoxeterSystem.braidWord, h, CoxeterSystem.braidWord, h',
    prod_map_alternatingWord_two, prod_map_alternatingWord_two] at hb
  exact hb

/-- Two standard generators satisfy the length-three braid relation when the corresponding entry
of `M` is `3`. -/
theorem ArtinGroup.gen_braid {i i' : B} (h : M i i' = 3) :
    ArtinGroup.gen M i * ArtinGroup.gen M i' * ArtinGroup.gen M i =
      ArtinGroup.gen M i' * ArtinGroup.gen M i * ArtinGroup.gen M i' := by
  have h' : M i' i = 3 := by rw [M.symmetric i' i]; exact h
  have hb := ArtinGroup.prod_map_gen_braidWord M i i'
  rw [CoxeterSystem.braidWord, h, CoxeterSystem.braidWord, h',
    prod_map_alternatingWord_three, prod_map_alternatingWord_three] at hb
  exact hb.symm

/-- The universal property of the Artin-Tits presentation: a family `f` of elements of a group
satisfying the braid relations of `M` extends to a homomorphism out of `ArtinGroup M`. -/
def ArtinGroup.lift (f : B → G)
    (hf : ∀ i i', ((CoxeterSystem.braidWord M i i').map f).prod =
      ((CoxeterSystem.braidWord M i' i).map f).prod) :
    ArtinGroup M →* G :=
  PresentedGroup.toGroup (f := f) <| by
    rintro r ⟨⟨i, i'⟩, rfl⟩
    simp only [uncurry, artinRelation_def, map_mul, map_inv, ← List.prod_map_hom,
      mul_inv_eq_one]
    have hcomp : (⇑(FreeGroup.lift f) ∘ FreeGroup.of) = f := by
      funext j
      exact FreeGroup.lift_apply_of
    rw [hcomp]
    exact hf i i'

@[simp]
theorem ArtinGroup.lift_gen (f : B → G) (hf) (i : B) :
    ArtinGroup.lift M f hf (ArtinGroup.gen M i) = f i :=
  by
    rw [← ArtinGroup.of_eq_gen]
    exact PresentedGroup.toGroup.of _

/-- Two homomorphisms from an Artin–Tits group are equal if they agree on every standard
generator. -/
@[ext]
theorem ArtinGroup.hom_ext {f g : ArtinGroup M →* G}
    (h : ∀ i, f (ArtinGroup.gen M i) = g (ArtinGroup.gen M i)) : f = g := by
  apply PresentedGroup.ext
  intro i
  simpa only [ArtinGroup.of_eq_gen] using h i

/-- The exponent-sum homomorphism, sending every standard generator to `1 : ℤ`. It is well defined
because the two sides of every Artin-Tits relation are words of the same length; this is what
fails for the Coxeter presentation, where `σ i * σ i = 1` has sides of lengths `2` and `0`. -/
def ArtinGroup.exponentSum : ArtinGroup M →* Multiplicative ℤ :=
  ArtinGroup.lift M (fun _ ↦ Multiplicative.ofAdd 1) <| by
    intro i i'
    simp only [CoxeterSystem.braidWord, List.map_const', CoxeterSystem.length_alternatingWord,
      List.prod_replicate, M.symmetric i i']

@[simp]
theorem ArtinGroup.exponentSum_gen (i : B) :
    ArtinGroup.exponentSum M (ArtinGroup.gen M i) = Multiplicative.ofAdd 1 :=
  ArtinGroup.lift_gen M _ _ i

/-- A power of a standard generator is trivial only for the exponent `0`; in particular the
Artin-Tits presentation does not collapse. -/
@[simp]
theorem ArtinGroup.gen_zpow_eq_one_iff (i : B) (k : ℤ) :
    ArtinGroup.gen M i ^ k = 1 ↔ k = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zpow_zero]⟩
  have h₁ : ArtinGroup.exponentSum M (ArtinGroup.gen M i ^ k) = 1 := by rw [h, map_one]
  rw [map_zpow, ArtinGroup.exponentSum_gen] at h₁
  simpa using congrArg Multiplicative.toAdd h₁

@[simp]
theorem ArtinGroup.gen_pow_eq_one_iff (i : B) (k : ℕ) :
    ArtinGroup.gen M i ^ k = 1 ↔ k = 0 := by
  rw [← zpow_natCast, ArtinGroup.gen_zpow_eq_one_iff, Int.natCast_eq_zero]

/-- Every standard Artin-Tits generator has infinite order. -/
@[simp]
theorem ArtinGroup.orderOf_gen (i : B) : orderOf (ArtinGroup.gen M i) = 0 :=
  orderOf_eq_zero_iff'.mpr fun k hk h ↦ hk.ne' ((ArtinGroup.gen_pow_eq_one_iff M i k).mp h)

/-- Every standard Artin-Tits generator is nontrivial. -/
@[simp]
theorem ArtinGroup.gen_ne_one (i : B) : ArtinGroup.gen M i ≠ 1 := by
  intro h
  simpa using (ArtinGroup.gen_pow_eq_one_iff M i 1).mp (by rwa [pow_one])

end Relations

section Coxeter

variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The canonical homomorphism from the Artin-Tits group of `M` onto a Coxeter group with matrix
`M`, sending each standard generator to the corresponding simple reflection. It exists because the
Coxeter relations imply the Artin-Tits relations, which is Mathlib's
`CoxeterSystem.wordProd_braidWord_eq`. -/
def ArtinGroup.toCoxeterGroup : ArtinGroup M →* W :=
  ArtinGroup.lift M cs.simple fun i i' ↦ cs.wordProd_braidWord_eq i i'

@[simp]
theorem ArtinGroup.toCoxeterGroup_gen (i : B) :
    ArtinGroup.toCoxeterGroup cs (ArtinGroup.gen M i) = cs.simple i :=
  ArtinGroup.lift_gen M _ _ i

/-- The canonical map from the Artin–Tits group onto the associated Coxeter group is
surjective. -/
theorem ArtinGroup.toCoxeterGroup_surjective :
    Function.Surjective (ArtinGroup.toCoxeterGroup cs) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← cs.subgroup_closure_range_simple,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨ArtinGroup.gen M i, ArtinGroup.toCoxeterGroup_gen cs i⟩

end Coxeter

end TauCeti
