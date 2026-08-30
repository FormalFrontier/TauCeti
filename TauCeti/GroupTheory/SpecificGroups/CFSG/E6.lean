/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted

/-!
# The pinned ambient groups of the type-E6 families

This file connects the explicit full-weight type-`E₆` minuscule carrier to the validated indices
for the two type-`E₆` families in the classification list:

```text
E₆(q),       ²E₆(q).
```

`TauCeti.E6LieIndex` contains exactly those two constructors of
`TauCeti.ValidLieTypeIndex`. Thus every group-valued definition below carries the field parameter
and validity proof fixed by the CFSG-statement roadmap. Its underlying Dynkin diagram is the pinned
`TauCeti.DynkinType.E6` datum, and its rank-six Bourbaki numbering is identified explicitly with
the numbering of `TauCeti.E6Minuscule.groupScheme`.

For `d : TauCeti.E6LieIndex`, `d.AmbientGroup` is the group of `d.Closure`-valued points of that
carrier. The maps `d.rootSubgroup k` expose all twelve positive and negative numbered simple-root
subgroups, while `d.simpleRootSubgroup i` is the positive half required by the uniform CFSG
interface. The represented split weight torus is exposed with the same index-derived numbering.

This is the type-`E₆` slice of milestone L0, "pinned ambient groups", in
`TauCetiRoadmap/CFSGStatement/README.md`. It supplies the common ambient group used by both the
ordinary and graph-twisted families. It does not construct either Steinberg endomorphism: the
ordinary Frobenius and the graph automorphism are separate Layer 9 outputs of the reductive-groups
roadmap. Nothing here asserts reductivity, finiteness, or simplicity.

## Main declarations

* `TauCeti.E6LieIndex`: the valid ordinary and graph-twisted type-`E₆` indices.
* `TauCeti.E6LieIndex.dynkinType_eq_E6` and `rank_eq_six`: the pinned diagram and numbering.
* `TauCeti.E6LieIndex.AmbientGroup`: the algebraic-closure-valued points of the explicit
  full-weight type-`E₆` carrier.
* `TauCeti.E6LieIndex.rootSubgroup` and `simpleRootSubgroup`: its numbered root subgroups.
* `TauCeti.E6LieIndex.weightTorus`: its rank-six represented split torus.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 7 and 13.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* The indexed interface follows the formal pattern of
  `TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA`; the carrier itself is the construction in
  `TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme`.
-/

public section

namespace TauCeti

namespace LieTypeIndex

/-- Whether a Lie-type index belongs to one of the two type-`E₆` families, `E₆(q)` or `²E₆(q)`.

This is a constructor selector, not a mathematical property of a group. The enclosing
`ValidLieTypeIndex` supplies the field and validity conditions. -/
def IsTypeE6 : LieTypeIndex → Prop
  | .E6 _ | .twistedE6 _ => True
  | _ => False

/-- Characterization of the two type-`E₆` constructors. -/
@[simp]
theorem isTypeE6_iff (d : LieTypeIndex) : d.IsTypeE6 ↔
    match d with
    | .E6 _ | .twistedE6 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeE6 := fun d => by
  cases d <;> rw [isTypeE6_iff] <;> infer_instance

/-- Neither type-`E₆` family uses a half-Frobenius, so both belong to the ordinary-or-graph-twisted
lane of the Steinberg construction. -/
theorem not_usesHalfFrobenius_of_isTypeE6 {d : LieTypeIndex} (h : d.IsTypeE6) :
    ¬d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

end LieTypeIndex

/-- A validated index in one of the two type-`E₆` families, `E₆(q)` or `²E₆(q)`. -/
abbrev E6LieIndex : Type := {d : ValidLieTypeIndex // d.1.IsTypeE6}

namespace E6LieIndex

/-- Introduce a valid ordinary type-`E₆` index. -/
abbrev ofE6 (q : PrimePower) (hvalid : (LieTypeIndex.E6 q).Valid) : E6LieIndex :=
  ⟨⟨.E6 q, hvalid⟩, (LieTypeIndex.isTypeE6_iff _).mpr trivial⟩

/-- Introduce a valid graph-twisted type-`E₆` index. -/
abbrev ofTwistedE6 (q : PrimePower) (hvalid : (LieTypeIndex.twistedE6 q).Valid) : E6LieIndex :=
  ⟨⟨.twistedE6 q, hvalid⟩, (LieTypeIndex.isTypeE6_iff _).mpr trivial⟩

/-- Every type-`E₆` index is one of the two introduction forms. -/
theorem exists_eq_ofE6_or_exists_eq_ofTwistedE6 (d : E6LieIndex) :
    (∃ (q : PrimePower) (hvalid : (LieTypeIndex.E6 q).Valid), d = ofE6 q hvalid) ∨
      ∃ (q : PrimePower) (hvalid : (LieTypeIndex.twistedE6 q).Valid),
        d = ofTwistedE6 q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hE6⟩ := d
  revert hvalid hE6
  cases d
  case E6 q => exact fun hvalid _ ↦ .inl ⟨q, hvalid, rfl⟩
  case twistedE6 q => exact fun hvalid _ ↦ .inr ⟨q, hvalid, rfl⟩
  all_goals exact fun _ hE6 ↦ ((LieTypeIndex.isTypeE6_iff _).mp hE6).elim

/-- A type-`E₆` index, regarded as an index with an ordinary or graph-twisted Frobenius. -/
abbrev toGraphTwistedIndex (d : E6LieIndex) : GraphTwistedIndex :=
  ⟨d.1, LieTypeIndex.not_usesHalfFrobenius_of_isTypeE6 d.2⟩

/-! ## The pinned root datum and its numbering -/

/-- The underlying Dynkin diagram of either type-`E₆` family is `E₆`. -/
@[simp]
theorem dynkinType_eq_E6 (d : E6LieIndex) : d.1.dynkinType = .E6 := by
  rcases d.exists_eq_ofE6_or_exists_eq_ofTwistedE6 with ⟨q, hvalid, rfl⟩ | ⟨q, hvalid, rfl⟩
  · exact LieTypeIndex.dynkinType_E6 q
  · exact LieTypeIndex.dynkinType_twistedE6 q

/-- The rank read from the pinned Dynkin diagram of a type-`E₆` index is six. -/
@[simp]
theorem rank_eq_six (d : E6LieIndex) : d.1.rank = 6 := by
  rw [ValidLieTypeIndex.rank, d.dynkinType_eq_E6, DynkinType.rank_E6]

/-- The Bourbaki nodes supplied by the index, identified with the six nodes used by the explicit
minuscule carrier. -/
def nodeEquiv (d : E6LieIndex) : Fin d.1.rank ≃ Fin 6 :=
  finCongr d.rank_eq_six

/-- Applying the node identification only changes the proof that an index is below the rank. -/
@[simp]
theorem nodeEquiv_apply_val (d : E6LieIndex) (i : Fin d.1.rank) :
    (d.nodeEquiv i).val = i.val :=
  finCongr_apply_coe d.rank_eq_six i

/-- Positive and negative simple-root indices, transported to the numbering of the minuscule
carrier. -/
def rootNodeEquiv (d : E6LieIndex) :
    (Fin d.1.rank ⊕ Fin d.1.rank) ≃ (Fin 6 ⊕ Fin 6) :=
  Equiv.sumCongr d.nodeEquiv d.nodeEquiv

@[simp]
theorem rootNodeEquiv_inl (d : E6LieIndex) (i : Fin d.1.rank) :
    d.rootNodeEquiv (.inl i) = .inl (d.nodeEquiv i) :=
  by
    rw [rootNodeEquiv, Equiv.sumCongr_apply]
    rfl

@[simp]
theorem rootNodeEquiv_inr (d : E6LieIndex) (i : Fin d.1.rank) :
    d.rootNodeEquiv (.inr i) = .inr (d.nodeEquiv i) :=
  by
    rw [rootNodeEquiv, Equiv.sumCongr_apply]
    rfl

/-! ## Algebraic-closure-valued points and pinned subgroups -/

/-- The algebraic-closure-valued points of the explicit full-weight type-`E₆` minuscule carrier. -/
noncomputable abbrev AmbientGroup (d : E6LieIndex) : Type :=
  E6Minuscule.points d.1.Closure

/-- A positive or negative simple-root subgroup of the type-`E₆` ambient group, in the index's
Bourbaki numbering. -/
noncomputable def rootSubgroup (d : E6LieIndex)
    (k : Fin d.1.rank ⊕ Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  E6Minuscule.rootSubgroupPoints (d.rootNodeEquiv k) d.1.Closure

/-- The indexed root subgroup is the corresponding numbered root subgroup of the minuscule
carrier. -/
theorem rootSubgroup_def (d : E6LieIndex) (k : Fin d.1.rank ⊕ Fin d.1.rank) :
    d.rootSubgroup k = E6Minuscule.rootSubgroupPoints (d.rootNodeEquiv k) d.1.Closure :=
  (rfl)

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i`. -/
noncomputable abbrev simpleRootSubgroup (d : E6LieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  d.rootSubgroup (.inl i)

/-- A positive simple-root subgroup is the positive numbered root subgroup of the minuscule
carrier. -/
theorem simpleRootSubgroup_def (d : E6LieIndex) (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      E6Minuscule.rootSubgroupPoints (.inl (d.nodeEquiv i)) d.1.Closure := by
  rw [simpleRootSubgroup, rootSubgroup_def, rootNodeEquiv_inl]

/-- The negative simple-root subgroup at the Bourbaki-numbered node `i`. -/
noncomputable abbrev negativeSimpleRootSubgroup (d : E6LieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  d.rootSubgroup (.inr i)

/-- A negative simple-root subgroup is the negative numbered root subgroup of the minuscule
carrier. -/
theorem negativeSimpleRootSubgroup_def (d : E6LieIndex) (i : Fin d.1.rank) :
    d.negativeSimpleRootSubgroup i =
      E6Minuscule.rootSubgroupPoints (.inr (d.nodeEquiv i)) d.1.Closure := by
  rw [negativeSimpleRootSubgroup, rootSubgroup_def, rootNodeEquiv_inr]

/-- Reindex a rank-indexed tuple along the identification of the index's Dynkin nodes with
`Fin 6`. -/
private def weightTorusReindex (d : E6LieIndex) :
    (Fin d.1.rank → d.1.Closureˣ) →* (Fin 6 → d.1.Closureˣ) where
  toFun s i := s (d.nodeEquiv.symm i)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The represented split weight torus of the type-`E₆` ambient group, with coordinates indexed
by the pinned Dynkin nodes. -/
noncomputable def weightTorus (d : E6LieIndex) :
    (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (E6Minuscule.weightTorusPoints d.1.Closure).comp
    d.weightTorusReindex

/-- The indexed weight torus is the minuscule carrier's weight torus after reindexing its six
coordinates along `nodeEquiv`. -/
@[simp]
theorem weightTorus_apply (d : E6LieIndex) (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s =
      E6Minuscule.weightTorusPoints d.1.Closure (fun i ↦ s (d.nodeEquiv.symm i)) :=
  by
    rw [weightTorus]
    rfl

end E6LieIndex

end TauCeti
