/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.MultiplicationMatrix

/-!
# Executable conjugacy-class data

The class-algebra theory of a finite group is indexed by `ConjClasses G`, a quotient type: perfect
for stating theorems, useless for computing with, since nothing picks a representative of a class
or orders the classes. The Burnside--Dixon--Schneider character-table algorithm needs both, because
its input is the array of structure constants `aᵢⱼₖ` and its output is a table whose rows and
columns are numbered.

This file supplies the missing numbering. A `TauCeti.ClassData G` is a list of elements of `G`, one
from each conjugacy class; the two fields say that no two entries are conjugate and that every
element of `G` is conjugate to an entry. From those two facts alone the whole indexing API follows:
a representative `d.rep i` for each `i : Fin d.numClasses`, an inverse `d.index g` computed by a
list search, and the equivalence `d.equivConjClasses : Fin d.numClasses ≃ ConjClasses G` that
transports statements about `ConjClasses G` to the numbering. All of these are genuine `def`s: the
numbering data itself asks only for `[Group G]`, the searches computed from it for a decidable
conjugacy relation, the classes as `Finset`s for `[Fintype G]`, and `TauCeti.ClassData.ofList`
builds class data from any list that meets every conjugacy class.

On top of the numbering the file gives the two computational objects the algorithm consumes: the
structure constants `d.structureConstant i j k`, counted by a single scan of the `i`-th class rather
than by the double scan of the definition, and the class-multiplication matrices
`d.classMultMatrix i` over `Fin d.numClasses`. Both are proved equal to their `ConjClasses`-indexed
counterparts `TauCeti.structureConstant` and `TauCeti.classMultMatrix`, so the theory built on the
latter — in particular the eigenrow characterization of the central characters — applies verbatim
to the computed data.

`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Dihedral` works the dihedral group of
order `8` as a closed instance of everything here.

## Main definitions

* `TauCeti.ClassData`: a numbered list of conjugacy-class representatives of a group.
* `TauCeti.ClassData.ofList`: such a list, extracted from any list meeting every conjugacy class.
* `TauCeti.ClassData.index`, `TauCeti.ClassData.rep`: the numbering and its representatives.
* `TauCeti.ClassData.equivConjClasses`: the numbering as an equivalence with `ConjClasses G`.
* `TauCeti.ClassData.classFinset`, `TauCeti.ClassData.classes`: the `i`-th conjugacy class and the
  executable list of all conjugacy classes.
* `TauCeti.ClassData.structureConstant`, `TauCeti.ClassData.structureConstantTable`,
  `TauCeti.ClassData.classMultMatrix`: the single-scan structure constants, tabulated, and the
  matrices they assemble.

## Main results

* `TauCeti.ClassData.numClasses_eq_card_conjClasses`: the numbering has the expected length.
* `TauCeti.ClassData.exists_mem_classes`, `TauCeti.ClassData.pairwise_disjoint_classes`: the
  executable list covers the group and its entries are pairwise disjoint.
* `TauCeti.ClassData.sum_card_classFinset`: the numbered classes partition the group.
* `TauCeti.ClassData.structureConstant_eq` and
  `TauCeti.ClassData.classMultMatrix_eq_submatrix`: the computed constants and matrices are the
  ones the theory uses, renumbered.

## References

This implements the object `ClassData` and the executable `structureConstant` of Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
the layer that makes the Burnside--Dixon--Schneider algorithm executable. The `Fin`-indexed family
`classFinset` is what the class-multiplication matrices are indexed by, while `classes` packages
the same family as the executable `List (Finset G)` requested there. See J. D. Dixon, *High speed
computation of group characters*, Numer. Math. 10 (1967) 446-450.
-/

-- The definitions carrying the computation are individually `@[expose]`d below: a downstream
-- module that evaluates class data for a concrete group needs exactly those bodies to reduce in
-- the kernel. The theorems and the `ConjClasses`-indexed API stay opaque.
public section

namespace TauCeti

open scoped BigOperators

attribute [local instance] IsConj.setoid

variable {G : Type*} [Group G]

/-- **Executable conjugacy-class data** for a group: a list `reps` containing exactly one element of
each conjugacy class. The two fields are the two halves of "exactly one": distinct entries name
distinct classes, and no class is missed. Carrying the data asks nothing of `G` beyond its group
structure; a decidable conjugacy relation is what the searches computed from it need, and
finiteness what turns the classes into `Finset`s.

The order of `reps` is the arbitrary but fixed numbering of the conjugacy classes that a
computation indexes by; `TauCeti.ClassData.equivConjClasses` identifies it with
`ConjClasses G`. -/
structure ClassData (G : Type*) [Group G] where
  /-- The chosen representatives, in the order that numbers the classes. -/
  reps : List G
  /-- Distinct representatives are not conjugate, so they name distinct classes. -/
  pairwise_not_isConj : reps.Pairwise fun x y => ¬ IsConj x y
  /-- Every element of the group is conjugate to a representative, so no class is missed. -/
  exists_isConj : ∀ g : G, ∃ x ∈ reps, IsConj x g

namespace ClassData

/-- **Class data is determined by its representatives**: the two remaining fields are proofs. -/
@[ext]
theorem ext {d₁ d₂ : ClassData G} (h : d₁.reps = d₂.reps) : d₁ = d₂ := by
  cases d₁
  cases d₂
  subst h
  rfl

/-- Class data extracted from a list `l` that meets every conjugacy class: keep an entry exactly
when it is not conjugate to any entry kept from the part of `l` after it. Since `List.pwFilter`
recurses from the right, this keeps the *last* representative of each class, in the order those
representatives occur in `l`.

The hypothesis, rather than `Finset.univ.toList`, is what keeps this computable: `Finset.toList`
is noncomputable, whereas a concrete finite group can supply concrete representatives. -/
@[expose] def ofList [DecidableRel (IsConj : G → G → Prop)] (l : List G)
    (hl : ∀ g : G, ∃ x ∈ l, IsConj x g) :
    ClassData G where
  reps := l.pwFilter fun x y => ¬ IsConj x y
  pairwise_not_isConj := List.pairwise_pwFilter _
  exists_isConj g := by
    have hneg : ∀ {x y z : G}, ¬ IsConj x z → ¬ IsConj x y ∨ ¬ IsConj y z := by
      intro x y z hxz
      by_cases hxy : IsConj x y
      · exact Or.inr fun hyz => hxz (hxy.trans hyz)
      · exact Or.inl hxy
    by_contra hg
    have hall : ∀ b ∈ l.pwFilter fun x y => ¬ IsConj x y, ¬ IsConj g b := by
      intro b hb hgb
      exact hg ⟨b, hb, hgb.symm⟩
    obtain ⟨x, hxl, hxg⟩ := hl g
    exact (List.forall_mem_pwFilter (R := fun x y : G => ¬ IsConj x y) hneg g l).mp hall x hxl
      hxg.symm

/-- **The representatives extracted from `l`** are the entries of `l` that are not conjugate to any
later retained entry: the characteristic property of `TauCeti.ClassData.ofList`, so that a client
never has to unfold the filtering itself. -/
@[simp]
theorem reps_ofList [DecidableRel (IsConj : G → G → Prop)] (l : List G)
    (hl : ∀ g : G, ∃ x ∈ l, IsConj x g) :
    (ofList l hl).reps = l.pwFilter fun x y => ¬ IsConj x y := (rfl)

/-- Every finite group has class data; the witness is noncomputable only because
`Finset.toList` is. -/
noncomputable instance [Finite G] : Inhabited (ClassData G) := by
  letI := Fintype.ofFinite G
  letI := Classical.decRel (IsConj : G → G → Prop)
  exact ⟨ofList (Finset.univ : Finset G).toList fun g =>
    ⟨g, Finset.mem_toList.mpr (Finset.mem_univ g), IsConj.refl g⟩⟩

variable (d : ClassData G)

/-- The number of conjugacy classes of `G`, as numbered by `d`. -/
@[expose] def numClasses : ℕ := d.reps.length

/-- The chosen representative of the `i`-th conjugacy class. -/
@[expose] def rep (i : Fin d.numClasses) : G := d.reps[(i : ℕ)]

/-- The `i`-th conjugacy class, as an element of `ConjClasses G`. -/
def classOf (i : Fin d.numClasses) : ConjClasses G := ConjClasses.mk (d.rep i)

/-- The `i`-th class is the class of the `i`-th representative. This is not a `simp` lemma: it
would rewrite past `TauCeti.ClassData.classOf_index`, which is the normal form wanted. -/
theorem classOf_eq_mk (i : Fin d.numClasses) : d.classOf i = ConjClasses.mk (d.rep i) := (rfl)

/-- **Distinct numbers name distinct classes**: the `Fin`-indexed reading of the
`pairwise_not_isConj` field. -/
theorem not_isConj_rep {i j : Fin d.numClasses} (hij : i ≠ j) : ¬ IsConj (d.rep i) (d.rep j) := by
  have key : ∀ {a b : Fin d.numClasses}, (a : ℕ) < (b : ℕ) → ¬ IsConj (d.rep a) (d.rep b) :=
    fun {a b} hab => List.pairwise_iff_getElem.mp d.pairwise_not_isConj a b a.isLt b.isLt hab
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact fun hc => key h hc.symm

/-- The representatives are distinct, conjugacy being reflexive. -/
theorem nodup_reps : d.reps.Nodup := by
  refine d.pairwise_not_isConj.imp fun {a b} h => ?_
  rintro rfl
  exact h (IsConj.refl a)

section Executable

-- A decidable conjugacy relation is what makes the search below, and everything computed from it,
-- executable; the numbering data itself needs none. A finite `G` with decidable equality supplies
-- the instance, so a concrete group asks for nothing extra.
variable [DecidableRel (IsConj : G → G → Prop)]

/-- The number of the conjugacy class of `g`, found by searching `d.reps` for a representative
conjugate to `g`. The search succeeds because some representative is conjugate to `g`. -/
@[expose] def index (g : G) : Fin d.numClasses :=
  ⟨d.reps.findIdx fun x => IsConj x g, by
    refine List.findIdx_lt_length_of_exists ?_
    obtain ⟨x, hx, hxg⟩ := d.exists_isConj g
    exact ⟨x, hx, decide_eq_true hxg⟩⟩

/-- The representative found by `TauCeti.ClassData.index` is conjugate to `g`. -/
theorem isConj_rep_index (g : G) : IsConj (d.rep (d.index g)) g :=
  of_decide_eq_true
    (List.findIdx_getElem (p := fun x => decide (IsConj x g)) (w := (d.index g).isLt))

/-- **The numbering is characterized by conjugacy**: `g` has number `i` exactly when it is
conjugate to the `i`-th representative. -/
theorem index_eq_iff {g : G} {i : Fin d.numClasses} : d.index g = i ↔ IsConj (d.rep i) g := by
  refine ⟨fun h => h ▸ d.isConj_rep_index g, fun h => ?_⟩
  by_contra hne
  exact d.not_isConj_rep hne ((d.isConj_rep_index g).trans h.symm)

@[simp]
theorem index_rep (i : Fin d.numClasses) : d.index (d.rep i) = i :=
  d.index_eq_iff.mpr (IsConj.refl _)

/-- **Two elements get the same number exactly when they are conjugate.** -/
theorem index_eq_index_iff {g h : G} : d.index g = d.index h ↔ IsConj g h := by
  refine ⟨fun hgh => ?_, fun hgh => d.index_eq_iff.mpr ((d.isConj_rep_index h).trans hgh.symm)⟩
  have h1 := d.isConj_rep_index g
  rw [hgh] at h1
  exact h1.symm.trans (d.isConj_rep_index h)

@[simp]
theorem classOf_index (g : G) : d.classOf (d.index g) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (d.isConj_rep_index g)

/-- The number of a conjugacy class: `TauCeti.ClassData.index` is constant on classes, so it
descends to `ConjClasses G`. -/
def indexClass (C : ConjClasses G) : Fin d.numClasses :=
  Quotient.liftOn C d.index fun _ _ hab => d.index_eq_index_iff.mpr hab

@[simp]
theorem indexClass_mk (g : G) : d.indexClass (ConjClasses.mk g) = d.index g := (rfl)

/-- **The numbering of the conjugacy classes is a bijection.** The forward map sends a number to
the class it names; the inverse is the computable search `TauCeti.ClassData.index`. -/
def equivConjClasses : Fin d.numClasses ≃ ConjClasses G where
  toFun := d.classOf
  invFun := d.indexClass
  left_inv i := by rw [classOf_eq_mk, indexClass_mk, index_rep]
  right_inv := by
    refine Quotient.ind fun a => ?_
    rw [ConjClasses.quotient_mk_eq_mk, indexClass_mk, classOf_index]

@[simp]
theorem equivConjClasses_apply (i : Fin d.numClasses) : d.equivConjClasses i = d.classOf i := (rfl)

@[simp]
theorem equivConjClasses_symm_apply (C : ConjClasses G) :
    d.equivConjClasses.symm C = d.indexClass C := (rfl)

omit [DecidableRel (IsConj : G → G → Prop)] in
/-- **The numbering has the expected length**: `d.reps` lists as many elements as `G` has
conjugacy classes. The bijection is the one underlying `TauCeti.ClassData.equivConjClasses`, but it
is exhibited here from the two fields directly, since the count itself needs neither a finite `G`
nor a decidable conjugacy. -/
theorem numClasses_eq_card_conjClasses : d.numClasses = Nat.card (ConjClasses G) := by
  have hbij : Function.Bijective d.classOf := by
    constructor
    · intro i j hij
      rw [classOf_eq_mk, classOf_eq_mk, ConjClasses.mk_eq_mk_iff_isConj] at hij
      by_contra hne
      exact d.not_isConj_rep hne hij
    · refine Quotient.ind fun g => ?_
      obtain ⟨x, hx, hxg⟩ := d.exists_isConj g
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [ConjClasses.quotient_mk_eq_mk, classOf_eq_mk, ConjClasses.mk_eq_mk_iff_isConj]
      -- the representative `d.rep ⟨i, hi⟩` is the list entry `d.reps[i]` by definition
      exact hxg
  simpa using Nat.card_congr (Equiv.ofBijective _ hbij)

-- Finiteness enters only from here: it is what presents a conjugacy class as a `Finset`, and so
-- what lets the structure constants be counted.
variable [Fintype G]

section Classes

/-- The `i`-th conjugacy class, as a `Finset` of `G`. -/
@[expose] def classFinset (i : Fin d.numClasses) : Finset G := {g | d.index g = i}

@[simp]
theorem mem_classFinset {i : Fin d.numClasses} {g : G} :
    g ∈ d.classFinset i ↔ d.index g = i := by
  simp [classFinset]

/-- The `i`-th class consists of the elements conjugate to the `i`-th representative. -/
theorem mem_classFinset_iff_isConj {i : Fin d.numClasses} {g : G} :
    g ∈ d.classFinset i ↔ IsConj (d.rep i) g := by
  rw [mem_classFinset, index_eq_iff]

/-- The `i`-th representative lies in the `i`-th class. -/
theorem rep_mem_classFinset (i : Fin d.numClasses) : d.rep i ∈ d.classFinset i :=
  d.mem_classFinset_iff_isConj.mpr (IsConj.refl _)

/-- **The numbered class is the carrier of the class it names.** This is the compatibility that
lets the `Finset` be used in a computation and `ConjClasses.carrier` in a proof. -/
theorem coe_classFinset (i : Fin d.numClasses) :
    (d.classFinset i : Set G) = (d.classOf i).carrier := by
  ext g
  rw [Finset.mem_coe, mem_classFinset_iff_isConj, ConjClasses.mem_carrier_iff_mk_eq, classOf_eq_mk,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

/-- The size of the `i`-th class is the size of the class it names. -/
theorem card_classFinset (i : Fin d.numClasses) :
    (d.classFinset i).card = Nat.card (d.classOf i).carrier := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun x => by rw [← Finset.mem_coe, d.coe_classFinset i])

/-- **Distinct numbered classes are disjoint.** -/
theorem disjoint_classFinset {i j : Fin d.numClasses} (hij : i ≠ j) :
    Disjoint (d.classFinset i) (d.classFinset j) := by
  simp only [Finset.disjoint_left, mem_classFinset]
  rintro a rfl h
  exact hij h

/-- The conjugacy classes, in the order determined by `d`. -/
@[expose] def classes : List (Finset G) :=
  (List.finRange d.numClasses).map d.classFinset

/-- There is one entry of `classes` for each class number. -/
@[simp]
theorem length_classes : d.classes.length = d.numClasses := by
  simp [classes]

/-- Looking up the `i`-th entry of `classes` gives the `i`-th numbered class. -/
@[simp]
theorem getElem_classes (i : ℕ) (hi : i < d.classes.length) :
    d.classes[i] = d.classFinset ⟨i, d.length_classes ▸ hi⟩ := by
  simp [classes]

/-- The list `classes` covers every element of the group. -/
theorem exists_mem_classes (g : G) : ∃ C ∈ d.classes, g ∈ C := by
  refine ⟨d.classFinset (d.index g), ?_, d.mem_classFinset.mpr rfl⟩
  simp [classes]

/-- Distinct entries of `classes` are disjoint. -/
theorem pairwise_disjoint_classes : d.classes.Pairwise Disjoint := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [d.getElem_classes i hi, d.getElem_classes j hj]
  exact d.disjoint_classFinset (Fin.ne_of_val_ne (Nat.ne_of_lt hij))

/-- **The numbered classes partition the group**: their sizes sum to `|G|`. This is the
`Fin`-indexed reading of the class equation `sum_conjClasses_card_eq_card`. -/
theorem sum_card_classFinset : ∑ i, (d.classFinset i).card = Fintype.card G := by
  simp only [classFinset]
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise fun g _ => Finset.mem_univ (d.index g)).symm

end Classes

section StructureConstants

/-- The structure constant `aᵢⱼₖ` of the class algebra, computed by a single scan: it counts the
elements `x` of the `i`-th class whose complementary factor `x⁻¹ * gₖ` lies in the `j`-th class,
where `gₖ` is the `k`-th representative.

`TauCeti.ClassData.structureConstant_eq` identifies this with `TauCeti.structureConstant`, which
counts the factorizations `x * y = gₖ` themselves. -/
@[expose] def structureConstant (i j k : Fin d.numClasses) : ℕ :=
  ((d.classFinset i).filter fun x => d.index (x⁻¹ * d.rep k) = j).card

/-- The class-multiplication matrix `Mᵢ` of the `i`-th class, numbered by `d`. As in
`TauCeti.classMultMatrix`, the entry `(Mᵢ)ⱼₖ` is `aᵢₖⱼ`; that transposed index order is what makes
`Mᵢ` the matrix of multiplication by the `i`-th class sum on the centre of the group algebra, and
so what makes the central-character rows *left* eigenvectors of the family. -/
def classMultMatrix (i : Fin d.numClasses) :
    Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ :=
  Matrix.of fun j k => (d.structureConstant i k j : ℤ)

@[simp]
theorem classMultMatrix_apply (i j k : Fin d.numClasses) :
    d.classMultMatrix i j k = (d.structureConstant i k j : ℤ) :=
  (rfl)

/-- The structure constants of `d`, tabulated: the `k`-th entry of the `j`-th entry of the `i`-th
entry is `aᵢⱼₖ`. This nested list is the whole input to the Dixon--Schneider algorithm for `G`,
and, unlike the matrices it assembles, it can be compared with a literal by the kernel. -/
@[expose] def structureConstantTable : List (List (List ℕ)) :=
  (List.finRange d.numClasses).map fun i =>
    (List.finRange d.numClasses).map fun j =>
      (List.finRange d.numClasses).map fun k => d.structureConstant i j k

@[simp]
theorem length_structureConstantTable : d.structureConstantTable.length = d.numClasses := by
  simp [structureConstantTable]

/-- **The `i`-th row of the table** is the table of the structure constants with first index `i`.
Together with `List.getElem_map` and `List.getElem_finRange` this reduces a lookup at any depth:
in particular `simp` sends the depth-three entry `d.structureConstantTable[i][j][k]` to `aᵢⱼₖ`,
so no separate entry lemma is needed. -/
@[simp]
theorem getElem_structureConstantTable (i : ℕ) (hi : i < d.structureConstantTable.length) :
    d.structureConstantTable[i] =
      (List.finRange d.numClasses).map fun j =>
        (List.finRange d.numClasses).map fun k =>
          d.structureConstant ⟨i, d.length_structureConstantTable ▸ hi⟩ j k := by
  simp [structureConstantTable]

end StructureConstants

end Executable

section ClassIndexed

-- The `ConjClasses`-indexed theory the results below compare with is stated under decidable
-- equality on `G`, from which Mathlib derives the decidable conjugacy. Assuming that same
-- hypothesis here is what makes the two sides of a comparison decide conjugacy the same way, so
-- that they are the one computation renumbered rather than two.
variable [Fintype G] [DecidableEq G]

/-- **The computed structure constants are the structure constants**: recording a factorization by
its first factor matches the single scan with the double scan of the definition. -/
theorem structureConstant_eq (i j k : Fin d.numClasses) :
    d.structureConstant i j k =
      TauCeti.structureConstant (d.classOf i) (d.classOf j) (d.classOf k) := by
  rw [d.classOf_eq_mk k, TauCeti.structureConstant_mk]
  refine Finset.card_bij'
    (fun x hx => (⟨⟨x, ?_⟩, ⟨x⁻¹ * d.rep k, ?_⟩⟩ :
      (d.classOf i).carrier × (d.classOf j).carrier))
    (fun p _ => (p.1 : G)) ?_ ?_ ?_ ?_
  · rw [← d.coe_classFinset i, Finset.mem_coe]
    exact (Finset.mem_filter.mp hx).1
  · rw [← d.coe_classFinset j, Finset.mem_coe]
    exact d.mem_classFinset.mpr (Finset.mem_filter.mp hx).2
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact mul_inv_cancel_left _ _
  · intro p hp
    have h1 : (p.1 : G) ∈ d.classFinset i := by
      rw [← Finset.mem_coe, d.coe_classFinset i]; exact p.1.2
    have h2 : (p.2 : G) ∈ d.classFinset j := by
      rw [← Finset.mem_coe, d.coe_classFinset j]; exact p.2.2
    have hp' : (p.1 : G) * (p.2 : G) = d.rep k := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨h1, ?_⟩
    rw [← hp', inv_mul_cancel_left]
    exact d.mem_classFinset.mp h2
  · intro x _
    rfl
  · intro p hp
    have hp' : (p.1 : G) * (p.2 : G) = d.rep k := (Finset.mem_filter.mp hp).2
    exact Prod.ext (Subtype.ext rfl) (Subtype.ext (eq_inv_mul_iff_mul_eq.mpr hp').symm)

/-- **The numbered class-multiplication matrix is a renumbering of the class-indexed one.** Every
statement about `TauCeti.classMultMatrix` therefore transports to the numbered family. -/
theorem classMultMatrix_eq_submatrix (i : Fin d.numClasses) :
    d.classMultMatrix i =
      (TauCeti.classMultMatrix (d.classOf i)).submatrix d.equivConjClasses d.equivConjClasses := by
  ext j k
  rw [classMultMatrix_apply, Matrix.submatrix_apply, equivConjClasses_apply, equivConjClasses_apply,
    TauCeti.classMultMatrix_apply, structureConstant_eq]

/-- The numbered class-multiplication matrices commute pairwise, the centre of the group algebra
being commutative. -/
theorem classMultMatrix_commute (i j : Fin d.numClasses) :
    Commute (d.classMultMatrix i) (d.classMultMatrix j) := by
  simp only [Commute, SemiconjBy, classMultMatrix_eq_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    (TauCeti.classMultMatrix_commute (d.classOf i) (d.classOf j)).eq]

end ClassIndexed

end ClassData

end TauCeti
