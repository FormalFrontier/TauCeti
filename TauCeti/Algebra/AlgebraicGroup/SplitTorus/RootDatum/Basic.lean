/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.Swap

/-!
# The coordinate-difference root datum

For a finite coordinate type `σ`, this file constructs the root datum whose roots and coroots are
the vectors `e_i - e_j`, indexed by ordered pairs `i ≠ j`. The character and cocharacter lattices
are the standard split-torus coordinate lattices

```text
σ →₀ ℤ,    σ → ℤ,
```

with `SplitTorus.dotPairing`. Reflections act by transposing the two coordinates that index the
reflecting root. The construction is independent of any choice of an enumeration of `σ`.

## Main declarations

* `TauCeti.SplitTorus.CoordinateRootIndex`: ordered pairs of distinct coordinates.
* `TauCeti.SplitTorus.coordinatePermRootIndex`: simultaneous application of a coordinate
  permutation to both entries of a root index.
* `TauCeti.SplitTorus.coordinateRoot` and `coordinateCoroot`: the vectors `e_i - e_j`, defined
  for arbitrary pairs of coordinates.
* `TauCeti.SplitTorus.coordinateRootDatum`: the resulting reduced root datum.
* `TauCeti.SplitTorus.coordinateRootDatum_pairing_apply`: the closed formula for its Cartan
  integers.
* `TauCeti.SplitTorus.coordinateRootDatum_reflection_apply` and
  `coordinateRootDatum_coreflection_apply`: reflections transpose arbitrary character and
  cocharacter coordinates.
* `TauCeti.SplitTorus.coordinateRootDatum_reflectionPerm`: reflections transpose coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

The ordered-pair construction and its proof plan are adapted from the formal template in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A`.

This is the coordinate-lattice construction used by the diagonal-torus root datum of `GL_n` in
Layer 7 of the ReductiveGroups roadmap.
-/

public section

open Set Function
open Module hiding reflection

namespace TauCeti.SplitTorus

noncomputable section

variable {σ : Type*}

/-- Ordered pairs of distinct coordinates, indexing the roots `e_i - e_j`. -/
abbrev CoordinateRootIndex (σ : Type*) := {p : σ × σ // p.1 ≠ p.2}

/-- A coordinate permutation acts on a root index by applying it to both entries. -/
noncomputable def coordinatePermRootIndex (e : Equiv.Perm σ) :
    CoordinateRootIndex σ ≃ CoordinateRootIndex σ :=
  Equiv.subtypeEquiv (e.prodCongr e) (fun p ↦ by simp)

/-- A coordinate permutation acts componentwise on an ordered root index. -/
@[simp]
theorem coordinatePermRootIndex_coe (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    (coordinatePermRootIndex e p).1 = (e p.1.1, e p.1.2) := by
  rw [coordinatePermRootIndex]
  simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply]
  -- `Equiv.prodCongr` uses `Prod.map`, whose application reduces definitionally.
  rfl

/-- Inverting a coordinate permutation inverts its action on root indices. -/
@[simp]
theorem coordinatePermRootIndex_symm (e : Equiv.Perm σ) :
    (coordinatePermRootIndex e).symm = coordinatePermRootIndex e.symm := by
  apply Equiv.ext
  intro p
  apply (coordinatePermRootIndex e).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply, coordinatePermRootIndex_coe]

/-- The identity coordinate permutation acts trivially on root indices. -/
@[simp]
theorem coordinatePermRootIndex_one :
    coordinatePermRootIndex (1 : Equiv.Perm σ) = 1 := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  rw [coordinatePermRootIndex_coe]
  -- The identity equivalence acts definitionally on the underlying pair.
  rfl

/-- Products of coordinate permutations act by the corresponding product on root indices. -/
@[simp]
theorem coordinatePermRootIndex_mul (e f : Equiv.Perm σ) :
    coordinatePermRootIndex (e * f) =
      coordinatePermRootIndex e * coordinatePermRootIndex f := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  simp only [coordinatePermRootIndex_coe, Equiv.Perm.mul_def, Equiv.trans_apply]

/-- The character-lattice vector `e_i - e_j`, defined for any two coordinates. -/
noncomputable def coordinateRoot (i j : σ) : σ →₀ ℤ := by
  classical
  exact Finsupp.single i 1 - Finsupp.single j 1

/-- The cocharacter-lattice vector `e_i - e_j`, defined for any two coordinates. -/
noncomputable def coordinateCoroot (i j : σ) : σ → ℤ :=
  ⇑(coordinateRoot i j)

open Classical in
/-- Evaluation of a coordinate root. -/
@[simp]
theorem coordinateRoot_apply (i j a : σ) :
    coordinateRoot i j a =
      (if a = i then 1 else 0) - (if a = j then 1 else 0) := by
  classical
  simp [coordinateRoot, Finsupp.single_apply, eq_comm]

open Classical in
/-- A coordinate coroot is the function underlying the corresponding finitely supported root. -/
@[simp]
theorem coordinateCoroot_apply (i j a : σ) :
    coordinateCoroot i j a =
      (if a = i then 1 else 0) - (if a = j then 1 else 0) := by
  rw [coordinateCoroot, coordinateRoot_apply]

/-- The coordinate coroot is the coercion of the coordinate root to a function. -/
theorem coe_coordinateRoot (i j : σ) : ⇑(coordinateRoot i j) = coordinateCoroot i j :=
  by rw [coordinateCoroot]

open Classical in
/-- The split-torus pairing of two coordinate differences, in closed form. -/
theorem dotPairing_coordinateRoot_coordinateCoroot (i j a b : σ) :
    dotPairing (coordinateRoot i j) (coordinateCoroot a b) =
      (if i = a then 1 else 0) - (if i = b then 1 else 0) -
        ((if j = a then 1 else 0) - (if j = b then 1 else 0)) := by
  classical
  rw [coordinateRoot, map_sub]
  simp [dotPairing_apply, coordinateCoroot_apply]

private theorem coordinateRoot_coroot_two (p : CoordinateRootIndex σ) :
    dotPairing (coordinateRoot p.1.1 p.1.2) (coordinateCoroot p.1.1 p.1.2) = 2 := by
  classical
  rw [dotPairing_coordinateRoot_coordinateCoroot]
  simp [p.2, Ne.symm p.2]

private theorem coordinateRoot_injective :
    Injective (fun p : CoordinateRootIndex σ ↦ coordinateRoot p.1.1 p.1.2) := by
  classical
  intro p q hpq
  have hroot : coordinateRoot p.1.1 p.1.2 = coordinateRoot q.1.1 q.1.2 := hpq
  have htwo : dotPairing (coordinateRoot q.1.1 q.1.2)
      (coordinateCoroot p.1.1 p.1.2) = 2 := by
    rw [← hroot]
    exact coordinateRoot_coroot_two p
  rw [dotPairing_coordinateRoot_coordinateCoroot] at htwo
  have hp := p.2
  have hq := q.2
  refine Subtype.ext (Prod.ext ?_ ?_) <;> (split_ifs at htwo <;> simp_all)

private theorem coordinateCoroot_injective :
    Injective (fun p : CoordinateRootIndex σ ↦ coordinateCoroot p.1.1 p.1.2) := by
  intro p q hpq
  apply coordinateRoot_injective
  apply DFunLike.coe_injective
  simpa only [coe_coordinateRoot] using hpq

/-- The injective root family used internally to construct `coordinateRootDatum`. -/
private def coordinateRootEmbedding : CoordinateRootIndex σ ↪ σ →₀ ℤ :=
  ⟨fun p ↦ coordinateRoot p.1.1 p.1.2, coordinateRoot_injective⟩

@[simp]
private theorem coordinateRootEmbedding_apply (p : CoordinateRootIndex σ) :
    coordinateRootEmbedding p = coordinateRoot p.1.1 p.1.2 :=
  rfl

/-- The injective coroot family used internally to construct `coordinateRootDatum`. -/
private def coordinateCorootEmbedding : CoordinateRootIndex σ ↪ σ → ℤ :=
  ⟨fun p ↦ coordinateCoroot p.1.1 p.1.2, coordinateCoroot_injective⟩

@[simp]
private theorem coordinateCorootEmbedding_apply (p : CoordinateRootIndex σ) :
    coordinateCorootEmbedding p = coordinateCoroot p.1.1 p.1.2 :=
  rfl

private theorem coordinatePairing_comm (p q : CoordinateRootIndex σ) :
    dotPairing (coordinateRoot p.1.1 p.1.2) (coordinateCoroot q.1.1 q.1.2) =
      dotPairing (coordinateRoot q.1.1 q.1.2) (coordinateCoroot p.1.1 p.1.2) := by
  classical
  rw [dotPairing_coordinateRoot_coordinateCoroot,
    dotPairing_coordinateRoot_coordinateCoroot]
  simp only [eq_comm]
  ring

private theorem coordinateRoot_reflection [DecidableEq σ]
    (p q : CoordinateRootIndex σ) :
    preReflection (coordinateRoot p.1.1 p.1.2)
        (dotPairing.flip (coordinateCoroot p.1.1 p.1.2))
        (coordinateRoot q.1.1 q.1.2) =
      coordinateRoot (coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q).1.1
        (coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q).1.2 := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
  classical
  rw [preReflection_apply, LinearMap.flip_apply,
    dotPairing_coordinateRoot_coordinateCoroot]
  simp only [coordinateRoot, coordinatePermRootIndex_coe]
  rw [apply_swap_eq (fun i : σ ↦ Finsupp.single i (1 : ℤ)) p.1.1 p.1.2 q.1.1,
    apply_swap_eq (fun i : σ ↦ Finsupp.single i (1 : ℤ)) p.1.1 p.1.2 q.1.2]
  module

private theorem coordinateCoroot_reflection [DecidableEq σ]
    (p q : CoordinateRootIndex σ) :
    preReflection (coordinateCoroot p.1.1 p.1.2) (dotPairing (coordinateRoot p.1.1 p.1.2))
        (coordinateCoroot q.1.1 q.1.2) =
      coordinateCoroot (coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q).1.1
        (coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q).1.2 := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
  classical
  ext a
  have h := congrArg (fun f : σ →₀ ℤ ↦ f a) (coordinateRoot_reflection p q)
  rw [preReflection_apply] at h ⊢
  simp only [LinearMap.flip_apply, Finsupp.sub_apply, Finsupp.smul_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, coordinateRoot_apply, coordinateCoroot_apply] at h ⊢
  rw [coordinatePairing_comm p q]
  exact h

open Classical in
/-- The reduced root datum of all coordinate differences `e_i - e_j` on a finite coordinate
type `σ`, paired by the split-torus dot product. -/
noncomputable def coordinateRootDatum (σ : Type*) [Finite σ] :
    RootDatum (CoordinateRootIndex σ) (σ →₀ ℤ) (σ → ℤ) :=
  RootPairing.mk' dotPairing coordinateRootEmbedding coordinateCorootEmbedding
    coordinateRoot_coroot_two
    (fun p _ ⟨q, hq⟩ ↦ ⟨coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q, by
      rw [coordinateRootEmbedding_apply] at hq ⊢
      rw [← hq]
      exact (coordinateRoot_reflection p q).symm⟩)
    (fun p _ ⟨q, hq⟩ ↦ ⟨coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q, by
      rw [coordinateCorootEmbedding_apply] at hq ⊢
      rw [← hq]
      exact (coordinateCoroot_reflection p q).symm⟩)

/-- The underlying bilinear map of the coordinate root datum is the split-torus dot pairing. -/
@[simp]
theorem coordinateRootDatum_toLinearMap [Finite σ] :
    (coordinateRootDatum σ).toLinearMap = dotPairing :=
  by
    -- Mathlib currently provides no projection simp lemmas for `RootPairing.mk'`.
    rw [coordinateRootDatum]
    simp only [RootPairing.mk']

/-- The roots of the coordinate root datum are the vectors `e_i - e_j`. -/
@[simp]
theorem coordinateRootDatum_root [Finite σ] (p : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).root p = coordinateRoot p.1.1 p.1.2 :=
  by
    -- Mathlib currently provides no projection simp lemmas for `RootPairing.mk'`.
    rw [coordinateRootDatum]
    simp only [RootPairing.mk', coordinateRootEmbedding_apply]

/-- The coroots of the coordinate root datum are the vectors `e_i - e_j`. -/
@[simp]
theorem coordinateRootDatum_coroot [Finite σ] (p : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).coroot p = coordinateCoroot p.1.1 p.1.2 :=
  by
    -- Mathlib currently provides no projection simp lemmas for `RootPairing.mk'`.
    rw [coordinateRootDatum]
    simp only [RootPairing.mk', coordinateCorootEmbedding_apply]

/-- The root-datum pairing is the split-torus coordinate dot product. This bridge is not a simp
lemma; `coordinateRootDatum_pairing_apply` is the normal-form simp theorem. -/
theorem coordinateRootDatum_pairing [Finite σ] (p q : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).pairing p q =
      dotPairing (coordinateRoot p.1.1 p.1.2) (coordinateCoroot q.1.1 q.1.2) :=
  by
    rw [← RootPairing.root_coroot_eq_pairing, coordinateRootDatum_root,
      coordinateRootDatum_coroot, coordinateRootDatum_toLinearMap]

open Classical in
/-- Closed formula for the Cartan integers of the coordinate root datum. -/
@[simp]
theorem coordinateRootDatum_pairing_apply [Finite σ] (p q : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).pairing p q =
      (if p.1.1 = q.1.1 then 1 else 0) - (if p.1.1 = q.1.2 then 1 else 0) -
        ((if p.1.2 = q.1.1 then 1 else 0) - (if p.1.2 = q.1.2 then 1 else 0)) := by
  rw [coordinateRootDatum_pairing, dotPairing_coordinateRoot_coordinateCoroot]

/-- The root--coroot pairing of the coordinate root datum is symmetric. -/
theorem coordinateRootDatum_pairing_comm [Finite σ] (p q : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).pairing p q = (coordinateRootDatum σ).pairing q p := by
  rw [coordinateRootDatum_pairing, coordinateRootDatum_pairing]
  exact coordinatePairing_comm p q

/-- The coordinate-difference root datum is reduced. -/
instance isReduced_coordinateRootDatum [Finite σ] : (coordinateRootDatum σ).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ coordinateRootDatum_pairing_comm

open Classical in
/-- Reflection in the coordinate root indexed by `p` precomposes an arbitrary character with the
transposition of the two coordinates of `p`. -/
@[simp]
theorem coordinateRootDatum_reflection_apply [Finite σ] (p : CoordinateRootIndex σ)
    (x : σ →₀ ℤ) (a : σ) :
    (coordinateRootDatum σ).reflection p x a = x ((Equiv.swap p.1.1 p.1.2) a) := by
  rw [RootPairing.reflection_apply, coordinateRootDatum_root]
  simp only [RootPairing.coroot', LinearMap.flip_apply, coordinateRootDatum_coroot,
    coordinateRootDatum_toLinearMap, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    coordinateRoot_apply]
  have hpairing : dotPairing x (coordinateCoroot p.1.1 p.1.2) =
      x p.1.1 - x p.1.2 := by
    classical
    let _ := Fintype.ofFinite σ
    rw [dotPairing_apply,
      x.sum_fintype (fun i c ↦ c * coordinateCoroot p.1.1 p.1.2 i) (by simp)]
    simp [coordinateCoroot_apply, mul_sub, mul_ite]
  rw [hpairing]
  simpa only [smul_eq_mul, mul_comm] using
    (apply_swap_eq (fun b : σ ↦ x b) p.1.1 p.1.2 a).symm

open Classical in
/-- Coreflection in the coordinate root indexed by `p` precomposes an arbitrary cocharacter with
the transposition of the two coordinates of `p`. -/
@[simp]
theorem coordinateRootDatum_coreflection_apply [Finite σ] (p : CoordinateRootIndex σ)
    (x : σ → ℤ) (a : σ) :
    (coordinateRootDatum σ).coreflection p x a = x ((Equiv.swap p.1.1 p.1.2) a) := by
  rw [RootPairing.coreflection_apply]
  simp only [RootPairing.root', coordinateRootDatum_root, coordinateRootDatum_coroot,
    coordinateRootDatum_toLinearMap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    coordinateCoroot_apply]
  have hpairing : dotPairing (coordinateRoot p.1.1 p.1.2) x =
      x p.1.1 - x p.1.2 := by
    classical
    simp [dotPairing_apply, coordinateRoot]
  rw [hpairing]
  simpa only [smul_eq_mul, mul_comm] using
    (apply_swap_eq x p.1.1 p.1.2 a).symm

/-- Reflections in the coordinate root datum transpose both coordinates of the root index. -/
@[simp]
theorem coordinateRootDatum_reflectionPerm [Finite σ] [DecidableEq σ]
    (p q : CoordinateRootIndex σ) :
    (coordinateRootDatum σ).reflectionPerm p q =
      coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
  classical
  apply (coordinateRootDatum σ).root.injective
  rw [(coordinateRootDatum σ).root_reflectionPerm]
  rw [RootPairing.reflection_apply, coordinateRootDatum_root, coordinateRootDatum_root]
  simp only [RootPairing.coroot', LinearMap.flip_apply, coordinateRootDatum_coroot,
    coordinateRootDatum_toLinearMap]
  rw [coordinateRootDatum_root]
  exact coordinateRoot_reflection p q

end

end TauCeti.SplitTorus
