/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
public import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
public import TauCeti.Geometry.Lie.Exponential.Smoothness
public import TauCeti.Geometry.Lie.Exponential.Trotter
-- Non-public: the slope characterisation of a derivative and the module description of a slope
-- are used only inside proofs, and no statement below mentions `slope`.
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Lie subalgebra of a closed subgroup

For a subgroup `K` of a Lie group `G` the derivations whose one-parameter subgroup never leaves
`K`,

`𝔨 = {X : 𝔤 | ∀ t : ℝ, lieExp (t • X) ∈ K}`,

are the candidate Lie algebra of `K`. This file proves that `𝔨` is a **Lie subalgebra** of `𝔤`
whenever `K` is closed, as `TauCeti.Lie.lieSubalgebraOfSubgroup`.

Each of the three closure properties is a limit of elements of `K`, and each uses a different
piece of the Layer 0/1 machinery:

* scalars are free, because `t • (c • X) = (t * c) • X`;
* addition is the **Trotter product formula** `TauCeti.Lie.tendsto_lieExp_smul_mul_lieExp_smul_pow`,
  which exhibits `lieExp (t • (X + Y))` as a limit of products of elements of `K`;
* the bracket is the **infinitesimal adjoint**. If `X` and `Y` both generate one-parameter
  subgroups inside `K` then so does `Ad (lieExp (s • X)) Y`, by the conjugation formula
  `TauCeti.Lie.conj_lieExp`; the curve `s ↦ Ad (lieExp (s • X)) Y` therefore runs inside `𝔨` and
  starts at `Y`, and its derivative at `0` is `⁅X, Y⁆` by
  `TauCeti.Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero`. A difference quotient of a
  curve in a linear subspace stays in that subspace, so `⁅X, Y⁆` lies in its closure.

## Closedness is load-bearing

The roadmap advertises `𝔨` as a Lie subalgebra for an arbitrary subgroup, but only the scalar
closure survives without a topological hypothesis: both the Trotter formula and the difference
quotient produce the new element as a *limit* of elements of `K`, never as an element of `K` on
the nose. `TauCeti.Lie.isClosed_setOf_forall_lieExp_smul_mem` is what turns those limits back into
membership, and it is the only place the hypothesis is used. This is also the hypothesis under
which the next Layer 2 target — the closed-subgroup theorem, which promotes `K` to an embedded
Lie subgroup with `Lie(K) = 𝔨` — is stated, so nothing downstream is lost.

## Main definitions

* `TauCeti.Lie.lieSubalgebraOfSubgroup`: the Lie subalgebra of a closed subgroup.

## Main results

* `TauCeti.Lie.lieExp_smul_add_mem`, `TauCeti.Lie.lieExp_smul_smul_mem` and
  `TauCeti.Lie.lieExp_smul_lie_mem`: the three closure properties, stated on the defining
  condition itself so that they can be used without producing the bundled subalgebra.
* `TauCeti.Lie.isClosed_setOf_forall_lieExp_smul_mem`: the candidate Lie algebra is a closed
  subset of `𝔤`.
* `TauCeti.Lie.Ad_mem_lieSubalgebraOfSubgroup`: the Lie algebra of `K` is invariant under the
  adjoint action of `K`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "The Lie subalgebra of a subgroup".
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Section 9.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### The three closure properties -/

/-- The zero derivation generates the trivial one-parameter subgroup, which lies in every
subgroup. -/
theorem lieExp_smul_zero_mem (K : Subgroup G) (t : ℝ) :
    lieExp (I := I) (t • (0 : LeftInvariantDerivation I G)) ∈ K := by
  simp

/-- **Scalar closure.** Rescaling a derivation reparametrises its one-parameter subgroup, so the
condition defining the Lie algebra of a subgroup is invariant under scalars. No hypothesis on the
subgroup is needed. -/
theorem lieExp_smul_smul_mem {K : Subgroup G} {X : LeftInvariantDerivation I G}
    (hX : ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K) (c t : ℝ) :
    lieExp (I := I) (t • c • X) ∈ K := by
  rw [smul_smul]
  exact hX _

/-- **Additive closure**, from the Trotter product formula: `lieExp (t • (X + Y))` is the limit of
the powers `(lieExp ((t / n) • X) * lieExp ((t / n) • Y)) ^ n`, each of which lies in `K`, so a
closed `K` contains the limit. -/
theorem lieExp_smul_add_mem {K : Subgroup G} (hK : IsClosed (K : Set G))
    {X Y : LeftInvariantDerivation I G} (hX : ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K)
    (hY : ∀ t : ℝ, lieExp (I := I) (t • Y) ∈ K) (t : ℝ) :
    lieExp (I := I) (t • (X + Y)) ∈ K := by
  refine hK.mem_of_tendsto (tendsto_lieExp_smul_mul_lieExp_smul_pow (I := I) (G := G) X Y t) ?_
  filter_upwards with n
  exact K.pow_mem (K.mul_mem (hX _) (hY _)) n

/-- **The candidate Lie algebra of a closed subgroup is closed.** It is an intersection over the
time parameter of preimages of `K` under the continuous maps `X ↦ lieExp (t • X)`. -/
theorem isClosed_setOf_forall_lieExp_smul_mem {K : Subgroup G} (hK : IsClosed (K : Set G)) :
    IsClosed {X : LeftInvariantDerivation I G | ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K} := by
  have hset : {X : LeftInvariantDerivation I G | ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K} =
      ⋂ t : ℝ, (fun X : LeftInvariantDerivation I G => lieExp (I := I) (t • X)) ⁻¹'
        (K : Set G) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [hset]
  refine isClosed_iInter fun t => hK.preimage ?_
  exact (contMDiff_lieExp (I := I) (G := G)).continuous.comp (continuous_const_smul t)

/-- The adjoint action of an element of `K` preserves the defining condition: conjugating the
one-parameter subgroup of `Y` by `g ∈ K` is the one-parameter subgroup of `Ad g Y`, and stays
inside `K`. -/
theorem lieExp_smul_Ad_mem {K : Subgroup G} {g : G} (hg : g ∈ K)
    {Y : LeftInvariantDerivation I G} (hY : ∀ t : ℝ, lieExp (I := I) (t • Y) ∈ K) (t : ℝ) :
    lieExp (I := I) (t • Ad (I := I) g Y) ∈ K := by
  have hconj : lieExp (I := I) (t • Ad (I := I) g Y) = g * lieExp (I := I) (t • Y) * g⁻¹ := by
    rw [← map_smul, conj_lieExp (I := I) g (t • Y)]
  rw [hconj]
  exact K.mul_mem (K.mul_mem hg (hY t)) (K.inv_mem hg)

/-- **Bracket closure.** The curve `s ↦ Ad (lieExp (s • X)) Y` takes its values in the candidate
Lie algebra of `K`, starts at `Y` and has derivative `⁅X, Y⁆` at `s = 0`; its difference quotients
therefore lie in the linear span, and the bracket is their limit. -/
theorem lieExp_smul_lie_mem {K : Subgroup G} (hK : IsClosed (K : Set G))
    {X Y : LeftInvariantDerivation I G} (hX : ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K)
    (hY : ∀ t : ℝ, lieExp (I := I) (t • Y) ∈ K) (t : ℝ) :
    lieExp (I := I) (t • ⁅X, Y⁆) ∈ K := by
  -- The candidate Lie algebra, as a linear subspace of `𝔤`.
  let S : Submodule ℝ (LeftInvariantDerivation I G) :=
    { carrier := {Z : LeftInvariantDerivation I G | ∀ s : ℝ, lieExp (I := I) (s • Z) ∈ K}
      zero_mem' := lieExp_smul_zero_mem K
      add_mem' := fun {_ _} hZ hW => lieExp_smul_add_mem hK hZ hW
      smul_mem' := fun c {_} hZ => lieExp_smul_smul_mem hZ c }
  have hmemS : ∀ Z : LeftInvariantDerivation I G,
      Z ∈ S ↔ ∀ s : ℝ, lieExp (I := I) (s • Z) ∈ K := fun _ => Iff.rfl
  have hSclosed : IsClosed (S : Set (LeftInvariantDerivation I G)) :=
    isClosed_setOf_forall_lieExp_smul_mem hK
  -- The adjoint orbit of `Y` along the one-parameter subgroup of `X`.
  set φ : ℝ → LeftInvariantDerivation I G := fun s => Ad (I := I) (lieExp (I := I) (s • X)) Y
    with hφ
  have hφmem : ∀ s : ℝ, φ s ∈ S := fun s => lieExp_smul_Ad_mem (hX s) hY
  have hφzero : φ 0 = Y := by simp [hφ]
  -- Its derivative at the origin is the bracket.
  have hderiv : HasDerivAt φ ⁅X, Y⁆ 0 := by
    let e : LeftInvariantDerivation I G ≃ₗᵢ[ℝ] E :=
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
    -- Evaluation at the identity, read in the model space, is the equivalence `lieExp` is built
    -- from; this is the bridge between the two spellings.
    have he : ∀ Z : LeftInvariantDerivation I G, (e Z : E) =
        ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint Z : GroupLieAlgebra I G) : E) := fun Z =>
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply Z
    have hexp : ∀ s : ℝ,
        mulInvariantExp (I := I) (G := G) (s • ((e X : E) : GroupLieAlgebra I G)) =
          lieExp (I := I) (s • X) := by
      intro s
      rw [lieExp_eq_mulInvariantExp, map_smul, he X]
      rfl
    have hbracket : ((e ⁅X, Y⁆ : E) : GroupLieAlgebra I G) =
        LieAlgebra.ad ℝ (GroupLieAlgebra I G) ((e X : E) : GroupLieAlgebra I G)
          ((e Y : E) : GroupLieAlgebra I G) := by
      have hmap := (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) BoundarylessManifold.isInteriorPoint).map_lie X Y
      simp only [leftInvariantDerivationLieEquivGroupLieAlgebra_apply] at hmap
      rw [he X, he Y, he ⁅X, Y⁆]
      exact hmap
    have key : HasDerivAt (fun s : ℝ => (e (φ s) : E)) (e ⁅X, Y⁆) 0 := by
      have hraw := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) (G := G)
        ((e X : E) : GroupLieAlgebra I G) ((e Y : E) : GroupLieAlgebra I G)
      have hfun : (fun s : ℝ => (e (φ s) : E)) =
          fun s : ℝ => show E from tangentAd (I := I)
            (mulInvariantExp (I := I) (G := G) (s • ((e X : E) : GroupLieAlgebra I G)))
            ((e Y : E) : GroupLieAlgebra I G) := by
        funext s
        rw [hexp s, hφ]
        exact leftInvariantDerivationLinearIsometryEquivModelVectorSpace_Ad
          (I := I) (lieExp (I := I) (s • X)) Y
      rw [hfun, hbracket]
      exact hraw
    have hcomp := (e.symm.toContinuousLinearEquiv.hasFDerivAt
      (x := (fun s : ℝ => (e (φ s) : E)) 0)).comp_hasDerivAt 0 key
    simpa [Function.comp_def] using hcomp
  -- A difference quotient of a curve in `S` stays in `S`, and `S` is closed.
  have hslope : ∀ s : ℝ, slope φ 0 s ∈ S := by
    intro s
    rw [slope_def_module]
    exact S.smul_mem _ (S.sub_mem (hφmem s) (hφzero ▸ hφmem 0))
  have hlie : ⁅X, Y⁆ ∈ S :=
    hSclosed.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hderiv)
      (Eventually.of_forall hslope)
  exact (hmemS _).mp hlie t

/-! ### The Lie subalgebra -/

/-- **The Lie algebra of a closed subgroup.** For a closed subgroup `K` of a Lie group `G`, the
derivations whose one-parameter subgroup lies entirely in `K` form a Lie subalgebra of `𝔤`. It is
the candidate `Lie K`, identified with the honest Lie algebra of `K` by the closed-subgroup
theorem.

Closedness of `K` is needed for everything but the scalar closure; see the module docstring. -/
def lieSubalgebraOfSubgroup (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    LieSubalgebra ℝ (LeftInvariantDerivation I G) where
  carrier := {X : LeftInvariantDerivation I G | ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K}
  zero_mem' := lieExp_smul_zero_mem K
  add_mem' := fun {_ _} hX hY => lieExp_smul_add_mem hK hX hY
  smul_mem' := fun c {_} hX => lieExp_smul_smul_mem hX c
  lie_mem' := fun {_ _} hX hY => lieExp_smul_lie_mem hK hX hY

@[simp]
theorem mem_lieSubalgebraOfSubgroup {K : Subgroup G} {hK : IsClosed (K : Set G)}
    {X : LeftInvariantDerivation I G} :
    X ∈ lieSubalgebraOfSubgroup (I := I) K hK ↔ ∀ t : ℝ, lieExp (I := I) (t • X) ∈ K :=
  Iff.rfl

/-- The one-parameter subgroup generated by an element of the Lie algebra of `K` lies in `K`. -/
theorem lieExp_smul_mem_of_mem_lieSubalgebraOfSubgroup {K : Subgroup G}
    {hK : IsClosed (K : Set G)} {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K hK) (t : ℝ) :
    lieExp (I := I) (t • X) ∈ K :=
  hX t

/-- The exponential of an element of the Lie algebra of `K` lies in `K`. -/
theorem lieExp_mem_of_mem_lieSubalgebraOfSubgroup {K : Subgroup G}
    {hK : IsClosed (K : Set G)} {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K hK) : lieExp (I := I) X ∈ K := by
  simpa using hX 1

/-- The Lie algebra of a closed subgroup is a closed subset of `𝔤`. This is what makes the
closed-subgroup theorem's complement argument available: `𝔨` is a closed linear subspace of a
finite-dimensional space, hence has a linear complement on which the exponential is transverse. -/
theorem isClosed_lieSubalgebraOfSubgroup {K : Subgroup G} (hK : IsClosed (K : Set G)) :
    IsClosed (lieSubalgebraOfSubgroup (I := I) K hK : Set (LeftInvariantDerivation I G)) :=
  isClosed_setOf_forall_lieExp_smul_mem hK

/-- **Monotonicity.** A larger closed subgroup has a larger Lie algebra. -/
theorem lieSubalgebraOfSubgroup_mono {K K' : Subgroup G} (hK : IsClosed (K : Set G))
    (hK' : IsClosed (K' : Set G)) (h : K ≤ K') :
    lieSubalgebraOfSubgroup (I := I) K hK ≤ lieSubalgebraOfSubgroup (I := I) K' hK' :=
  fun _ hX t => h (hX t)

/-- The Lie algebra of the whole group is the whole Lie algebra. -/
@[simp]
theorem lieSubalgebraOfSubgroup_top (hK : IsClosed ((⊤ : Subgroup G) : Set G)) :
    lieSubalgebraOfSubgroup (I := I) ⊤ hK = ⊤ := by
  ext X
  simp

/-- **The Lie algebra of `K` is invariant under the adjoint action of `K`.** Conjugating by `g ∈ K`
carries the one-parameter subgroup of `X` to the one of `Ad g X`, which therefore also stays in `K`.
This is the bundled form of `lieExp_smul_Ad_mem`, the statement that makes the adjoint orbit of the
bracket proof run inside `𝔨`. Invariance under `Ad g` for `g` outside `K` — which for a normal `K`
would say that `𝔨` is an ideal of `𝔤` — is not asserted here. -/
theorem Ad_mem_lieSubalgebraOfSubgroup {K : Subgroup G} {hK : IsClosed (K : Set G)} {g : G}
    (hg : g ∈ K) {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K hK) :
    Ad (I := I) g X ∈ lieSubalgebraOfSubgroup (I := I) K hK :=
  fun t => lieExp_smul_Ad_mem hg hX t

end TauCeti.Lie
