/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence

/-!
# Combinatorial balls, spheres, and manifolds

A simplicial complex is a **combinatorial `n`-ball** when it is stellar equivalent to the standard
`n`-simplex, and a **combinatorial `n`-sphere** when it is stellar equivalent to the boundary of
the standard `(n+1)`-simplex. A complex is a **combinatorial `n`-manifold** when the link of each
of its vertices is a combinatorial `(n-1)`-sphere — an interior vertex — or a combinatorial
`(n-1)`-ball — a boundary vertex. This is the simplicial side of piecewise-linear topology asked
for by layer 11 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), the definition that "has the correct links to be
a manifold".

The models are the complexes of `Simplex.Basic`: `simplex V` for a vertex set of `n + 1`
elements, and `simplexBoundary V` for one of `n + 2` elements, so that both models have dimension
`n`. They are compared using
`PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling`, which injectively relabels both
complexes in a common enlarged vertex type with infinitely many fresh vertices. Thus the
definitions do not depend on the names or unused capacity of the original ambient vertex type.

## The dimension convention, and why `0` is a separate case

`IsCombinatorialManifold` is defined by cases on the dimension rather than through a truncated
subtraction. The link of a vertex of a `0`-manifold — a discrete set of points — is the void
complex, which is neither a combinatorial ball nor a combinatorial sphere in any dimension `≥ 0`;
writing the link condition with `n - 1` in `ℕ` would therefore make the `0`-dimensional case
silently wrong rather than merely unused. The two cases are exposed by
`PreAbstractSimplicialComplex.isCombinatorialManifold_zero_iff` and
`PreAbstractSimplicialComplex.isCombinatorialManifold_succ_iff`.

## Main definitions

* `PreAbstractSimplicialComplex.IsCombinatorialBall`
* `PreAbstractSimplicialComplex.IsCombinatorialSphere`
* `PreAbstractSimplicialComplex.IsCombinatorialManifold`

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialBall.dimension_eq` and
  `PreAbstractSimplicialComplex.IsCombinatorialSphere.dimension_eq`: a combinatorial `n`-ball and
  a combinatorial `n`-sphere both have dimension `n`.
* `PreAbstractSimplicialComplex.isCombinatorialManifold_simplex`: the standard `(n+1)`-simplex is
  a combinatorial `(n+1)`-manifold, every vertex being a boundary vertex.
* `PreAbstractSimplicialComplex.isCombinatorialManifold_simplexBoundary`: the boundary of the
  standard `(n+2)`-simplex is a combinatorial `(n+1)`-manifold, every vertex being an interior
  vertex.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.dimension_le`: a combinatorial
  `n`-manifold has dimension at most `n`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299-320.
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι} {V : Finset ι}
  {n : ℕ} {v w : ι}

/-! ### Combinatorial balls and spheres -/

/-- `K` is a **combinatorial `n`-ball** when it is stellar equivalent to the simplex on some
`(n + 1)`-element vertex set, the standard `n`-simplex. -/
def IsCombinatorialBall (K : PreAbstractSimplicialComplex ι) (n : ℕ) : Prop :=
  ∃ V : Finset ι, V.card = n + 1 ∧ StellarEquivalentUpToRelabeling K (simplex V)

/-- `K` is a **combinatorial `n`-sphere** when it is stellar equivalent to the boundary of the
simplex on some `(n + 2)`-element vertex set, the boundary of the standard `(n+1)`-simplex. -/
def IsCombinatorialSphere (K : PreAbstractSimplicialComplex ι) (n : ℕ) : Prop :=
  ∃ V : Finset ι, V.card = n + 2 ∧ StellarEquivalentUpToRelabeling K (simplexBoundary V)

/-- The standard `n`-simplex is a combinatorial `n`-ball, with no moves needed. -/
theorem isCombinatorialBall_simplex (hV : V.card = n + 1) : IsCombinatorialBall (simplex V) n :=
  ⟨V, hV, StellarEquivalentUpToRelabeling.refl _⟩

/-- The boundary of the standard `(n+1)`-simplex is a combinatorial `n`-sphere, with no moves
needed. -/
theorem isCombinatorialSphere_simplexBoundary (hV : V.card = n + 2) :
    IsCombinatorialSphere (simplexBoundary V) n :=
  ⟨V, hV, StellarEquivalentUpToRelabeling.refl _⟩

/-- A one-vertex simplex is a combinatorial `0`-ball. -/
theorem isCombinatorialBall_simplex_singleton (v : ι) :
    IsCombinatorialBall (simplex {v}) 0 :=
  isCombinatorialBall_simplex (Finset.card_singleton v)

/-- The two vertices of an edge form a combinatorial `0`-sphere. -/
theorem isCombinatorialSphere_simplexBoundary_pair (hvw : v ≠ w) :
    IsCombinatorialSphere (simplexBoundary {v, w}) 0 :=
  isCombinatorialSphere_simplexBoundary (Finset.card_pair hvw)

/-- Being a combinatorial ball transfers along an intrinsic stellar equivalence. -/
theorem IsCombinatorialBall.of_stellarEquivalentUpToRelabeling
    (h : StellarEquivalentUpToRelabeling K L)
    (hL : IsCombinatorialBall L n) : IsCombinatorialBall K n := by
  obtain ⟨V, hV, hLV⟩ := hL
  exact ⟨V, hV, h.trans hLV⟩

/-- Being a combinatorial sphere transfers along an intrinsic stellar equivalence. -/
theorem IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling
    (h : StellarEquivalentUpToRelabeling K L)
    (hL : IsCombinatorialSphere L n) : IsCombinatorialSphere K n := by
  obtain ⟨V, hV, hLV⟩ := hL
  exact ⟨V, hV, h.trans hLV⟩

/-- A combinatorial `n`-ball has dimension `n`. -/
theorem IsCombinatorialBall.dimension_eq (h : IsCombinatorialBall K n) :
    dimension K = (n : WithBot ℕ∞) := by
  obtain ⟨V, hV, he⟩ := h
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  rw [← he.dimension_eq, dimension_simplex hne, hV]
  norm_num

/-- A combinatorial `n`-sphere has dimension `n`. -/
theorem IsCombinatorialSphere.dimension_eq (h : IsCombinatorialSphere K n) :
    dimension K = (n : WithBot ℕ∞) := by
  obtain ⟨V, hV, he⟩ := h
  rw [← he.dimension_eq, dimension_simplexBoundary (by omega), hV]
  norm_num

/-- A combinatorial ball has finitely many faces. -/
theorem IsCombinatorialBall.finite_faces (h : IsCombinatorialBall K n) : K.faces.Finite := by
  obtain ⟨V, -, he⟩ := h
  exact he.finite_faces_iff.mpr (finite_faces_simplex V)

/-- A combinatorial sphere has finitely many faces. -/
theorem IsCombinatorialSphere.finite_faces (h : IsCombinatorialSphere K n) : K.faces.Finite := by
  obtain ⟨V, -, he⟩ := h
  exact he.finite_faces_iff.mpr (finite_faces_simplexBoundary V)

/-- A combinatorial ball has a face; in particular it is not the void complex. -/
theorem IsCombinatorialBall.ne_bot (h : IsCombinatorialBall K n) : K ≠ ⊥ := by
  obtain ⟨V, hV, he⟩ := h
  apply he.ne_bot
  intro hbot
  have hmem : V ∈ simplex V := self_mem_simplex.mpr (Finset.card_pos.mp (by omega))
  rw [hbot] at hmem
  exact hmem

/-- A combinatorial sphere has a face; in particular it is not the void complex. -/
theorem IsCombinatorialSphere.ne_bot (h : IsCombinatorialSphere K n) : K ≠ ⊥ := by
  obtain ⟨V, hV, he⟩ := h
  apply he.ne_bot
  intro hbot
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
  have hVne : V ≠ {v} := by
    intro heq
    have := congrArg Finset.card heq
    simp [hV] at this
  have hmem : ({v} : Finset ι) ∈ simplexBoundary V :=
    singleton_mem_simplexBoundary.mpr ⟨hv, hVne⟩
  rw [hbot] at hmem
  exact hmem

/-! ### Combinatorial manifolds -/

/-- `K` is a **combinatorial `n`-manifold** when the link of each of its vertices is a
combinatorial `(n-1)`-sphere (an interior vertex) or a combinatorial `(n-1)`-ball (a boundary
vertex).

The dimension is matched against rather than decremented: in dimension `0` the condition is that
every vertex has void link, which is what a discrete set of points satisfies, and which no
combinatorial ball or sphere does. -/
def IsCombinatorialManifold (K : PreAbstractSimplicialComplex ι) : ℕ → Prop
  | 0 => ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → link K {v} = ⊥
  | n + 1 => ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K →
      IsCombinatorialSphere (link K {v}) n ∨ IsCombinatorialBall (link K {v}) n

/-- In dimension `0` the link condition says that every vertex has void link. -/
@[simp]
theorem isCombinatorialManifold_zero_iff :
    IsCombinatorialManifold K 0 ↔ ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → link K {v} = ⊥ :=
  Iff.rfl

/-- In positive dimension the link condition says that every vertex link is a combinatorial
sphere or ball one dimension down. -/
@[simp]
theorem isCombinatorialManifold_succ_iff :
    IsCombinatorialManifold K (n + 1) ↔ ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K →
      IsCombinatorialSphere (link K {v}) n ∨ IsCombinatorialBall (link K {v}) n :=
  Iff.rfl

/-- The standard `(n+1)`-simplex is a combinatorial `(n+1)`-manifold: the link of a vertex is the
simplex on the remaining `n + 1` vertices, a combinatorial `n`-ball, so every vertex is a
boundary vertex. -/
theorem isCombinatorialManifold_simplex (hV : V.card = n + 2) :
    IsCombinatorialManifold (simplex V) (n + 1) := by
  intro v hv
  have hvmem : v ∈ V := singleton_mem_simplex.mp hv
  rw [link_simplex (Finset.singleton_subset_iff.mpr hvmem)]
  refine Or.inr (isCombinatorialBall_simplex ?_)
  have hcard : (V \ {v}).card = V.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvmem]
  omega

/-- The boundary of the standard `(n+2)`-simplex is a combinatorial `(n+1)`-manifold: the link of
a vertex is the boundary of the simplex on the remaining `n + 2` vertices, a combinatorial
`n`-sphere, so every vertex is an interior vertex. -/
theorem isCombinatorialManifold_simplexBoundary (hV : V.card = n + 3) :
    IsCombinatorialManifold (simplexBoundary V) (n + 1) := by
  intro v hv
  have hvmem : v ∈ V := (singleton_mem_simplexBoundary.mp hv).1
  rw [link_simplexBoundary (Finset.singleton_subset_iff.mpr hvmem)]
  refine Or.inl (isCombinatorialSphere_simplexBoundary ?_)
  have hcard : (V \ {v}).card = V.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvmem]
  omega

/-- A one-vertex simplex is a combinatorial `0`-manifold. -/
theorem isCombinatorialManifold_simplex_zero (hV : V.card = 1) :
    IsCombinatorialManifold (simplex V) 0 := by
  intro v hv
  have hvmem : v ∈ V := singleton_mem_simplex.mp hv
  have hcard : (V \ {v}).card = V.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvmem]
  have hempty : V \ {v} = ∅ := Finset.card_eq_zero.mp (by omega)
  rw [link_simplex (Finset.singleton_subset_iff.mpr hvmem), hempty, simplex_empty]

/-- The two vertices of an edge form a combinatorial `0`-manifold, the combinatorial `0`-sphere.
Together with `isCombinatorialManifold_simplexBoundary` this is the acceptance check that the
link condition is not vacuous in either direction: the boundary of a simplex is a closed
combinatorial manifold in every dimension. -/
theorem isCombinatorialManifold_simplexBoundary_zero (hV : V.card = 2) :
    IsCombinatorialManifold (simplexBoundary V) 0 := by
  intro v hv
  have hvmem : v ∈ V := (singleton_mem_simplexBoundary.mp hv).1
  have hcard : (V \ {v}).card = V.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvmem]
  obtain ⟨w, hw⟩ : ∃ w, V \ {v} = {w} := Finset.card_eq_one.mp (by omega)
  rw [link_simplexBoundary (Finset.singleton_subset_iff.mpr hvmem), hw,
    simplexBoundary_singleton]

/-- A combinatorial `n`-manifold has dimension at most `n`. -/
theorem IsCombinatorialManifold.dimension_le (h : IsCombinatorialManifold K n) :
    dimension K ≤ (n : WithBot ℕ∞) := by
  refine dimension_le_iff.mpr fun σ hσ => ?_
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
  have hvK : ({v} : Finset ι) ∈ K := singleton_mem_of_mem hσ hv
  have key : σ.card ≤ n + 1 := by
    rcases eq_or_ne (σ.erase v) ∅ with herase | herase
    · have : σ = {v} := by
        rw [← Finset.insert_erase hv, herase, Finset.insert_empty]
      rw [this, Finset.card_singleton]
      omega
    · have hne : (σ.erase v).Nonempty := Finset.nonempty_of_ne_empty herase
      have hmem : σ.erase v ∈ link K {v} := by
        refine mem_link.mpr ⟨?_, Finset.disjoint_singleton_right.mpr (Finset.notMem_erase v σ), ?_⟩
        · exact (K.isRelLowerSet_faces hσ).2 (fun _ hx => Finset.mem_of_mem_erase hx) hne
        · rwa [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hv]
      have hcard : (σ.erase v).card = σ.card - 1 := Finset.card_erase_of_mem hv
      cases n with
      | zero =>
        rw [isCombinatorialManifold_zero_iff.mp h hvK] at hmem
        exact hmem.elim
      | succ m =>
        have hdim : dimension (link K {v}) = (m : WithBot ℕ∞) := by
          rcases isCombinatorialManifold_succ_iff.mp h hvK with hs | hb
          · exact hs.dimension_eq
          · exact hb.dimension_eq
        have hle := le_dimension hmem
        rw [hdim] at hle
        have : (σ.erase v).card - 1 ≤ m := by exact_mod_cast hle
        omega
  have : σ.card - 1 ≤ n := by omega
  exact_mod_cast this

end PreAbstractSimplicialComplex
