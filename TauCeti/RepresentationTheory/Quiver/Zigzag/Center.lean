/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication

/-!
# The centre of a zigzag algebra

The zigzag relation quotient `TauCeti.nonisolatedZigzagQuotient` of a finite simple graph `G`
without isolated vertices has the vertex idempotents `e_i`, the oriented edges `a_d` and the volume
classes `x_i` as a basis, and `TauCeti.zigzagMk_ofArrow_mul_ofArrow_symm` and its companions
compute every product of two of them. This file reads the centre off that multiplication table.

Every volume class is central: the idempotent at its base is a two-sided unit for it, and the
arrows, the other idempotents and the other volume classes annihilate it on both sides. A
combination `∑ i, f i • e_i` of vertex idempotents is central exactly when `f` is constant along
the edges of `G`, since an arrow `a_d` meets that combination through `f d.snd` on one side and
through `f d.fst` on the other. Those two families exhaust the centre: a central element `z`
satisfies `e_i * z * e_j = z * e_i * e_j = 0` for `i ≠ j`, so it is the sum of its diagonal corners
`e_i * z * e_i`, and each corner lies in the span of `e_i` and `x_i` because an arrow has distinct
endpoints and so does not survive a corner.

For a connected graph the coefficient family `f` is constant, its combination is a multiple of
`1 = ∑ i, e_i`, and the centre has `1` together with the volume classes as a basis; in particular
its dimension is `|V| + 1`. The independence of that family is proved by pushing it through the
coordinates of `TauCeti.zigzagBasis` at one fixed vertex and at the volume classes, where it
becomes the standard basis of `Option V → k`.

## Main definitions

* `TauCeti.zigzagCenterFun`: the family consisting of `1` and the volume classes, indexed by
  `Option V`.
* `TauCeti.zigzagCenterBasis`: that family, as a basis of the centre of the zigzag algebra of a
  connected graph.

## Main results

* `TauCeti.mem_center_of_commute_zigzagBasisFun`: commuting with the vertex idempotents, the arrows
  and the volume classes is enough to be central.
* `TauCeti.zigzagVolume_mem_center`: the volume classes are central.
* `TauCeti.sum_smul_zigzagMk_vertexIdempotent_mem_center` and
  `TauCeti.sum_smul_zigzagMk_vertexIdempotent_mem_center_iff`: a combination of vertex idempotents
  is central exactly when its coefficients are constant along the edges.
* `TauCeti.mem_center_nonisolatedZigzagQuotient_iff`: the centre consists exactly of the sums of
  such a combination and a combination of volume classes.
* `TauCeti.span_range_zigzagCenterFun_eq_center` and
  `TauCeti.linearIndependent_zigzagCenterFun`: for a connected graph the unit and the volume
  classes span the centre and are independent.
* `TauCeti.finrank_center_nonisolatedZigzagQuotient`: the centre of the zigzag algebra of a
  connected graph with at least two vertices has dimension `|V| + 1`.

## References

This is the fourth clause of Layer 2 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, whose
target signature `finrank_center_zigzagAlgebra` appears in
`TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`. See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### A criterion for centrality -/

/-- An element commuting with every vertex idempotent, every arrow and every volume class is
central: those classes span the zigzag relation quotient. -/
theorem mem_center_of_commute_zigzagBasisFun {z : nonisolatedZigzagQuotient k G}
    (h : ∀ b, z * zigzagBasisFun k G b = zigzagBasisFun k G b * z) :
    z ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  exact (Commute.span_right (s := Set.range (zigzagBasisFun k G))
    (fun _ ⟨b, hb⟩ => by rw [← hb]; exact h b) y (by
    rw [span_range_zigzagBasisFun_eq_top]
    exact Submodule.mem_top)).eq.symm

/-- A scalar annihilating a member of the vertex, arrow and volume family is zero: that family is
a basis when no vertex is isolated. -/
private theorem smul_zigzagBasisFun_eq_zero (hns : ∀ i : V, ∃ j, G.Adj i j)
    {b : ZigzagBasisIndex G} {c : k} (h : c • zigzagBasisFun k G b = 0) : c = 0 := by
  have h0 : (zigzagBasis k G hns).repr (c • zigzagBasisFun k G b) = 0 := by
    rw [h, map_zero]
  rw [map_smul, ← zigzagBasis_apply k G hns b, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h0
  exact Finsupp.single_eq_zero.mp h0

/-! ### The volume classes are central -/

/-- **The volume class of a vertex is central.** The idempotent at its base is a two-sided unit for
it, the other idempotents kill it on both sides, and the arrows and the other volume classes
annihilate it on both sides. -/
@[simp]
theorem zigzagVolume_mem_center (i : V) :
    zigzagVolume k G i ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) := by
  refine mem_center_of_commute_zigzagBasisFun k G fun b => ?_
  rcases b with j | d | j
  · rw [zigzagBasisFun_inl]
    rcases eq_or_ne j i with rfl | hji
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent,
        zigzagMk_vertexIdempotent_mul_zigzagVolume]
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G hji,
        zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G hji]
  · rw [zigzagBasisFun_inr_inl, zigzagVolume_mul_zigzagMk_ofArrow,
      zigzagMk_ofArrow_mul_zigzagVolume]
  · rw [zigzagBasisFun_inr_inr, zigzagVolume_mul_zigzagVolume, zigzagVolume_mul_zigzagVolume]

/-! ### Combinations of vertex idempotents -/

/-- A combination of vertex idempotents meets an idempotent through the coefficient at its
vertex. -/
private theorem sum_smul_vertexIdempotent_mul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
        * zigzagMk k G (vertexIdempotent k (vertex G j))
      = f j • zigzagMk k G (vertexIdempotent k (vertex G j)) := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_self]
  · intro i _ hij
    rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets an idempotent through the coefficient at its vertex,
on the other side. -/
private theorem vertexIdempotent_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    zigzagMk k G (vertexIdempotent k (vertex G j))
        * ∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i))
      = f j • zigzagMk k G (vertexIdempotent k (vertex G j)) := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, zigzagMk_vertexIdempotent_mul_self]
  · intro i _ hij
    rw [mul_smul_comm, zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hij),
      smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets an arrow through the coefficient at its head. -/
private theorem sum_smul_vertexIdempotent_mul_ofArrow [Fintype V] (f : V → k) (d : G.Dart) :
    (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
        * zigzagMk k G (ofArrow (arrow G d.adj))
      = f d.snd • zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [Finset.sum_mul, Finset.sum_eq_single d.snd]
  · rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_ofArrow]
  · intro i _ hij
    rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G d hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ d.snd) hj

/-- A combination of vertex idempotents meets an arrow through the coefficient at its tail, on the
other side. -/
private theorem ofArrow_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj))
        * ∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i))
      = f d.fst • zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [Finset.mul_sum, Finset.sum_eq_single d.fst]
  · rw [mul_smul_comm, zigzagMk_ofArrow_mul_vertexIdempotent]
  · intro i _ hij
    rw [mul_smul_comm, zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ d.fst) hj

/-- A combination of vertex idempotents meets a volume class through the coefficient at its base
vertex. -/
private theorem sum_smul_vertexIdempotent_mul_zigzagVolume [Fintype V] (f : V → k) (j : V) :
    (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i))) * zigzagVolume k G j
      = f j • zigzagVolume k G j := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_zigzagVolume]
  · intro i _ hij
    rw [smul_mul_assoc, zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A combination of vertex idempotents meets a volume class through the coefficient at its base
vertex, on the other side. -/
private theorem zigzagVolume_mul_sum_smul_vertexIdempotent [Fintype V] (f : V → k) (j : V) :
    zigzagVolume k G j * ∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i))
      = f j • zigzagVolume k G j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, zigzagVolume_mul_zigzagMk_vertexIdempotent]
  · intro i _ hij
    rw [mul_smul_comm, zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G hij, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **A combination of vertex idempotents whose coefficients are constant along the edges is
central.** An arrow sees the coefficient at its head on one side and the coefficient at its tail on
the other, and an idempotent or a volume class sees the coefficient at its own vertex on both
sides. -/
theorem sum_smul_zigzagMk_vertexIdempotent_mem_center [Fintype V] (f : V → k)
    (hf : ∀ ⦃i j : V⦄, G.Adj i j → f i = f j) :
    (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
      ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) := by
  refine mem_center_of_commute_zigzagBasisFun k G fun b => ?_
  rcases b with j | d | j
  · rw [zigzagBasisFun_inl, sum_smul_vertexIdempotent_mul_vertexIdempotent,
      vertexIdempotent_mul_sum_smul_vertexIdempotent]
  · rw [zigzagBasisFun_inr_inl, sum_smul_vertexIdempotent_mul_ofArrow,
      ofArrow_mul_sum_smul_vertexIdempotent, hf d.adj]
  · rw [zigzagBasisFun_inr_inr, sum_smul_vertexIdempotent_mul_zigzagVolume,
      zigzagVolume_mul_sum_smul_vertexIdempotent]

/-- **A combination of vertex idempotents is central exactly when its coefficients are constant
along the edges.** The converse of
`TauCeti.sum_smul_zigzagMk_vertexIdempotent_mem_center` needs the arrows to be independent, hence
the hypothesis that no vertex is isolated. -/
@[simp]
theorem sum_smul_zigzagMk_vertexIdempotent_mem_center_iff [Fintype V]
    (hns : ∀ i : V, ∃ j, G.Adj i j) (f : V → k) :
    (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
        ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G)
      ↔ ∀ ⦃i j : V⦄, G.Adj i j → f i = f j := by
  refine ⟨fun hz i j hij => ?_, sum_smul_zigzagMk_vertexIdempotent_mem_center k G f⟩
  have hcomm := (Subalgebra.mem_center_iff.mp hz)
    (zigzagMk k G (ofArrow (arrow G (⟨(i, j), hij⟩ : G.Dart).adj)))
  rw [sum_smul_vertexIdempotent_mul_ofArrow k G f ⟨(i, j), hij⟩,
    ofArrow_mul_sum_smul_vertexIdempotent k G f ⟨(i, j), hij⟩] at hcomm
  have hzero : (f i - f j) • zigzagBasisFun k G (.inr (.inl ⟨(i, j), hij⟩)) = 0 := by
    rw [zigzagBasisFun_inr_inl, sub_smul, sub_eq_zero]
    exact hcomm
  exact sub_eq_zero.mp (smul_zigzagBasisFun_eq_zero k G hns hzero)

/-! ### The diagonal corners of a central element -/

/-- The unit of the zigzag relation quotient is the sum of the vertex idempotents. -/
private theorem one_eq_sum_zigzagMk_vertexIdempotent [Fintype V] :
    (1 : nonisolatedZigzagQuotient k G)
      = ∑ i, zigzagMk k G (vertexIdempotent k (vertex G i)) := by
  rw [← map_one (zigzagMk k G), PathAlgebra.one_def, map_sum]
  exact (Fintype.sum_equiv (vertexEquiv G)
    (fun i : V => zigzagMk k G (vertexIdempotent k (vertex G i)))
    (fun v : DoubledQuiver G => zigzagMk k G (vertexIdempotent k v))
    fun i => by rw [vertexEquiv_apply]).symm

/-- **A diagonal corner is spanned by the idempotent and the volume class of its vertex.** An
arrow has distinct endpoints, so it does not survive a corner, and the idempotents away from the
corner vertex are killed on one side or the other. -/
private theorem corner_mem_span (i : V) (y : nonisolatedZigzagQuotient k G) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * y
        * zigzagMk k G (vertexIdempotent k (vertex G i))
      ∈ Submodule.span k
        {zigzagMk k G (vertexIdempotent k (vertex G i)), zigzagVolume k G i} := by
  have hy : y ∈ Submodule.span k (Set.range (zigzagBasisFun k G)) := by
    rw [span_range_zigzagBasisFun_eq_top]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rcases b with j | d | j
    · rw [zigzagBasisFun_inl]
      rcases eq_or_ne i j with rfl | hij
      · rw [zigzagMk_vertexIdempotent_mul_self, zigzagMk_vertexIdempotent_mul_self]
        exact Submodule.subset_span (by simp)
      · rw [zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G hij, zero_mul]
        exact Submodule.zero_mem _
    · rw [zigzagBasisFun_inr_inl]
      rcases eq_or_ne i d.snd with rfl | hne
      · rw [zigzagMk_vertexIdempotent_mul_ofArrow,
          zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d d.adj.ne']
        exact Submodule.zero_mem _
      · rw [zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G d hne, zero_mul]
        exact Submodule.zero_mem _
    · rw [zigzagBasisFun_inr_inr]
      rcases eq_or_ne i j with rfl | hij
      · rw [zigzagMk_vertexIdempotent_mul_zigzagVolume,
          zigzagVolume_mul_zigzagMk_vertexIdempotent]
        exact Submodule.subset_span (by simp)
      · rw [zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G hij, zero_mul]
        exact Submodule.zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- **A central element is the sum of its diagonal corners.** An off-diagonal corner
`e_i * z * e_j` of a central element is `z * e_i * e_j`, and distinct vertex idempotents are
orthogonal. -/
private theorem sum_corner_eq_self [Fintype V] {z : nonisolatedZigzagQuotient k G}
    (hz : z ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G)) :
    ∑ i, zigzagMk k G (vertexIdempotent k (vertex G i)) * z
        * zigzagMk k G (vertexIdempotent k (vertex G i)) = z := by
  have hcomm := Subalgebra.mem_center_iff.mp hz
  calc ∑ i, zigzagMk k G (vertexIdempotent k (vertex G i)) * z
          * zigzagMk k G (vertexIdempotent k (vertex G i))
      = ∑ i, ∑ j, zigzagMk k G (vertexIdempotent k (vertex G i)) * z
          * zigzagMk k G (vertexIdempotent k (vertex G j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        symm
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _ hji
          rw [mul_assoc, ← hcomm, ← mul_assoc,
            zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hji), zero_mul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    _ = (∑ i, zigzagMk k G (vertexIdempotent k (vertex G i))) * z
          * ∑ j, zigzagMk k G (vertexIdempotent k (vertex G j)) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = z := by
        rw [← one_eq_sum_zigzagMk_vertexIdempotent k G, one_mul, mul_one]

/-! ### The centre -/

/-- **The centre of a zigzag algebra.** For a finite simple graph with no isolated vertex, an
element is central exactly when it is the sum of a combination of vertex idempotents whose
coefficients are constant along the edges and a combination of volume classes. -/
theorem mem_center_nonisolatedZigzagQuotient_iff [Fintype V] (hns : ∀ i : V, ∃ j, G.Adj i j)
    {z : nonisolatedZigzagQuotient k G} :
    z ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) ↔
      ∃ f g : V → k, (∀ ⦃i j : V⦄, G.Adj i j → f i = f j) ∧
        z = (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
          + ∑ i, g i • zigzagVolume k G i := by
  constructor
  · intro hz
    have hcorner : ∀ i : V, ∃ a b : k,
        zigzagMk k G (vertexIdempotent k (vertex G i)) * z
            * zigzagMk k G (vertexIdempotent k (vertex G i))
          = a • zigzagMk k G (vertexIdempotent k (vertex G i)) + b • zigzagVolume k G i :=
      fun i => by
        obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (corner_mem_span k G i z)
        exact ⟨a, b, hab.symm⟩
    choose f g hfg using hcorner
    have hzsum : z = (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
        + ∑ i, g i • zigzagVolume k G i := by
      rw [← Finset.sum_add_distrib, ← sum_corner_eq_self k G hz]
      exact Finset.sum_congr rfl fun i _ => hfg i
    have hvol : (∑ i, g i • zigzagVolume k G i)
        ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) :=
      sum_mem fun i _ => Subalgebra.smul_mem _ (zigzagVolume_mem_center k G i) _
    have hidem : (∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i)))
        ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) := by
      have := sub_mem hz hvol
      rwa [hzsum, add_sub_cancel_right] at this
    exact ⟨f, g, (sum_smul_zigzagMk_vertexIdempotent_mem_center_iff k G hns f).mp hidem, hzsum⟩
  · rintro ⟨f, g, hf, rfl⟩
    exact add_mem (sum_smul_zigzagMk_vertexIdempotent_mem_center k G f hf)
      (sum_mem fun i _ => Subalgebra.smul_mem _ (zigzagVolume_mem_center k G i) _)

/-! ### The centre of a connected zigzag algebra -/

omit [Finite V] in
/-- A preconnected graph with at least two vertices has no isolated vertex. -/
private theorem exists_adj_of_preconnected [Nontrivial V] (hconn : G.Preconnected) (i : V) :
    ∃ j, G.Adj i j :=
  SimpleGraph.exists_adj_iff_not_isIsolated.mpr (hconn.not_isIsolated i)

omit [CommRing k] [Finite V] in
/-- A family of scalars constant along the edges is constant along reachability: induct along a
walk. -/
private theorem eq_of_reachable {f : V → k} (hf : ∀ ⦃i j : V⦄, G.Adj i j → f i = f j) {i j : V}
    (h : G.Reachable i j) : f i = f j := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf hadj).trans ih

/-- The family consisting of the unit and one volume class per vertex, indexed by `Option V`. For
a connected graph it is a basis of the centre: the unit takes the place of the sum of the vertex
idempotents, which is, up to a scalar, the only edge-constant combination of them. -/
noncomputable def zigzagCenterFun : Option V → nonisolatedZigzagQuotient k G
  | none => 1
  | some i => zigzagVolume k G i

@[simp]
theorem zigzagCenterFun_none : zigzagCenterFun k G none = 1 := (rfl)

@[simp]
theorem zigzagCenterFun_some (i : V) : zigzagCenterFun k G (some i) = zigzagVolume k G i := (rfl)

/-- The unit and the volume classes are central. -/
@[simp]
theorem zigzagCenterFun_mem_center (o : Option V) :
    zigzagCenterFun k G o ∈ Subalgebra.center k (nonisolatedZigzagQuotient k G) := by
  cases o with
  | none => rw [zigzagCenterFun_none]; exact one_mem _
  | some i => rw [zigzagCenterFun_some]; exact zigzagVolume_mem_center k G i

/-- **The unit and the volume classes span the centre of a connected zigzag algebra.** The
coefficients of a central combination of vertex idempotents are constant along the edges, hence
constant, so that combination is a multiple of `1 = ∑ i, e_i`. -/
theorem span_range_zigzagCenterFun_eq_center [Nontrivial V] (hconn : G.Preconnected) :
    Submodule.span k (Set.range (zigzagCenterFun k G))
      = Subalgebra.toSubmodule (Subalgebra.center k (nonisolatedZigzagQuotient k G)) := by
  have : Fintype V := Fintype.ofFinite V
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨o, rfl⟩
    exact zigzagCenterFun_mem_center k G o
  · intro z hz
    obtain ⟨f, g, hf, rfl⟩ := (mem_center_nonisolatedZigzagQuotient_iff k G
      (exists_adj_of_preconnected G hconn)).mp hz
    obtain ⟨i₀⟩ := (inferInstance : Nonempty V)
    have hidem : ∑ i, f i • zigzagMk k G (vertexIdempotent k (vertex G i))
        = f i₀ • (1 : nonisolatedZigzagQuotient k G) := by
      rw [one_eq_sum_zigzagMk_vertexIdempotent k G, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [eq_of_reachable k G hf (hconn i i₀)]
    rw [hidem]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩))

/-- **The unit and the volume classes are independent.** Their coordinates against
`TauCeti.zigzagBasis` at one fixed vertex and at the volume classes are the standard basis of
`Option V → k`. -/
theorem linearIndependent_zigzagCenterFun [Nonempty V] (hns : ∀ i : V, ∃ j, G.Adj i j) :
    LinearIndependent k (zigzagCenterFun k G) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨i₀⟩ := (inferInstance : Nonempty V)
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (ZigzagBasisIndex G) k (nonisolatedZigzagQuotient k G),
      ∀ b, B b = zigzagBasisFun k G b :=
    ⟨zigzagBasis k G hns, zigzagBasis_apply k G hns⟩
  have hone : (1 : nonisolatedZigzagQuotient k G) = ∑ i, B (Sum.inl i) := by
    rw [one_eq_sum_zigzagMk_vertexIdempotent k G]
    exact Finset.sum_congr rfl fun i _ => by rw [hB, zigzagBasisFun_inl]
  have h1l : B.repr 1 (Sum.inl i₀) = 1 := by
    rw [hone, map_sum, Finset.sum_apply', Finset.sum_eq_single i₀]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same]
    · intro i _ hi
      rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne (by simpa using hi.symm)]
    · intro hi
      exact absurd (Finset.mem_univ i₀) hi
  have h1r : ∀ j : V, B.repr 1 (Sum.inr (Sum.inr j)) = 0 := fun j => by
    rw [hone, map_sum, Finset.sum_apply']
    exact Finset.sum_eq_zero fun i _ => by
      rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne (by simp)]
  have hvol_eq (i : V) : zigzagVolume k G i = B (Sum.inr (Sum.inr i)) := by
    rw [hB, zigzagBasisFun_inr_inr]
  have hvol : ∀ (i : V) (b : ZigzagBasisIndex G), B.repr (zigzagVolume k G i) b
      = if (Sum.inr (Sum.inr i) : ZigzagBasisIndex G) = b then (1 : k) else 0 := fun i b => by
    rw [hvol_eq, Module.Basis.repr_self, Finsupp.single_apply]
  refine LinearIndependent.of_comp (LinearMap.pi fun o : Option V =>
    B.coord (Option.elim o (Sum.inl i₀) fun i => Sum.inr (Sum.inr i))) ?_
  have hfun : ⇑(LinearMap.pi fun o : Option V =>
      B.coord (Option.elim o (Sum.inl i₀) fun i => Sum.inr (Sum.inr i))) ∘ zigzagCenterFun k G
      = ⇑(Pi.basisFun k (Option V)) := by
    funext o o'
    rw [Pi.basisFun_apply, Pi.single_apply]
    rcases o with _ | i <;> rcases o' with _ | j <;>
      simp only [Function.comp_apply, LinearMap.pi_apply, Module.Basis.coord_apply,
        zigzagCenterFun_none, zigzagCenterFun_some, Option.elim]
    · rw [h1l]
      simp
    · rw [h1r]
      simp
    · rw [hvol]
      simp
    · rw [hvol]
      simp [eq_comm (a := i) (b := j)]
  rw [hfun]
  exact Module.Basis.linearIndependent _

/-- **The basis of the centre of a connected zigzag algebra.** For a preconnected finite simple
graph with at least two vertices the unit and the volume classes are a basis of the centre of the
zigzag relation quotient. -/
noncomputable def zigzagCenterBasis [Nontrivial V] (hconn : G.Preconnected) :
    Module.Basis (Option V) k (Subalgebra.center k (nonisolatedZigzagQuotient k G)) :=
  (Module.Basis.span
    (linearIndependent_zigzagCenterFun k G (exists_adj_of_preconnected G hconn))).map
      ((LinearEquiv.ofEq _ _ (span_range_zigzagCenterFun_eq_center k G hconn)).trans
        (Subalgebra.toSubmoduleEquiv _))

@[simp]
theorem zigzagCenterBasis_apply [Nontrivial V] (hconn : G.Preconnected) (o : Option V) :
    (zigzagCenterBasis k G hconn o : nonisolatedZigzagQuotient k G) = zigzagCenterFun k G o := by
  rw [zigzagCenterBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

/-- **The dimension of the centre of a zigzag algebra.** A preconnected finite simple graph with
at least two vertices has centre of dimension `|V| + 1`: the unit, together with one volume class
at each vertex. -/
theorem finrank_center_nonisolatedZigzagQuotient [Nontrivial k] [Fintype V] [Nontrivial V]
    (hconn : G.Preconnected) :
    Module.finrank k (Subalgebra.center k (nonisolatedZigzagQuotient k G))
      = Fintype.card V + 1 := by
  rw [Module.finrank_eq_card_basis (zigzagCenterBasis k G hconn), Fintype.card_option]

end TauCeti
