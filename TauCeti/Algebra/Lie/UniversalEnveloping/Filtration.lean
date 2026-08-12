/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import TauCeti.Algebra.WordFiltration

/-!
# The PBW filtration of a universal enveloping algebra

This file constructs the first stage of the Poincaré--Birkhoff--Witt development: the increasing
filtration of `UniversalEnvelopingAlgebra R L` by word length in the image of the canonical Lie map
`UniversalEnvelopingAlgebra.ι R`.

The defining relation

```text
ι(x) * ι(y) = ι(y) * ι(x) + ι([x,y])
```

replaces a degree-two commutator by a degree-one term. Thus word length gives a filtration, not a
grading. The associated graded will use this degree drop to make the leading symbols commute; that
comparison with `SymmetricAlgebra R L` is the next PBW stage and is not asserted here.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration`: words of length at most `k` in `ι(R)`.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_mul`: multiplication adds degrees.
* `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_zero` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwFiltration_one`: the scalar and generator steps.
* `TauCeti.UniversalEnvelopingAlgebra.iSup_pbwFiltration_eq_top`: the filtration is exhaustive.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ueaι" => _root_.UniversalEnvelopingAlgebra.ι R
local notation "ueaιₗ" => LieHom.toLinearMap (_root_.UniversalEnvelopingAlgebra.ι R)

/-- The PBW filtration on `U(L)`: its `k`-th step is spanned by products of at most `k` canonical
Lie generators. -/
abbrev pbwFiltration (k : ℕ) : Submodule R U :=
  TauCeti.Algebra.wordFiltration ueaιₗ k

/-- The step preceding degree `k` in the PBW filtration, with bottom in degree zero. -/
abbrev pbwFiltrationPrevious : ℕ → Submodule R U :=
  TauCeti.Algebra.wordFiltrationPrevious ueaιₗ

/-- The preceding PBW filtration is trivial in degree zero. -/
@[simp]
theorem pbwFiltrationPrevious_zero : pbwFiltrationPrevious R L 0 = ⊥ :=
  TauCeti.Algebra.wordFiltrationPrevious_zero ueaιₗ

/-- In successor degree, the preceding PBW filtration is the previous filtration step. -/
@[simp]
theorem pbwFiltrationPrevious_succ (k : ℕ) :
    pbwFiltrationPrevious R L (k + 1) = pbwFiltration R L k :=
  TauCeti.Algebra.wordFiltrationPrevious_succ ueaιₗ k

/-- A word of at most `k` canonical Lie generators lies in PBW filtration degree `k`. -/
theorem prod_ι_mem_pbwFiltration {k : ℕ} {l : List L} (hl : l.length ≤ k) :
    (l.map ueaι).prod ∈ pbwFiltration R L k := by
  exact TauCeti.Algebra.prod_map_mem_wordFiltration ueaιₗ hl

/-- A submodule contains the `k`-th PBW filtration step exactly when it contains every word of
length at most `k` in the canonical Lie generators. -/
theorem pbwFiltration_le_iff {k : ℕ} {p : Submodule R U} :
    pbwFiltration R L k ≤ p ↔ ∀ l : List L, l.length ≤ k → (l.map ueaι).prod ∈ p := by
  exact TauCeti.Algebra.wordFiltration_le_iff ueaιₗ

/-- The PBW filtration is increasing. -/
theorem pbwFiltration_mono : Monotone (pbwFiltration R L) :=
  TauCeti.Algebra.wordFiltration_mono ueaιₗ

/-- PBW filtration degree zero consists of scalars. -/
@[simp]
theorem pbwFiltration_zero : pbwFiltration R L 0 = 1 :=
  TauCeti.Algebra.wordFiltration_zero ueaιₗ

/-- Scalars belong to every PBW filtration step. -/
theorem algebraMap_mem_pbwFiltration (r : R) (k : ℕ) :
    algebraMap R U r ∈ pbwFiltration R L k :=
  TauCeti.Algebra.algebraMap_mem_wordFiltration ueaιₗ r k

/-- A canonical Lie generator has PBW filtration degree at most one. -/
theorem ι_mem_pbwFiltration_one (x : L) : ueaι x ∈ pbwFiltration R L 1 :=
  TauCeti.Algebra.apply_mem_wordFiltration_one ueaιₗ x

/-- The range of the canonical Lie map lies in the first PBW filtration step. -/
theorem ι_range_le_pbwFiltration_one :
    LinearMap.range ueaιₗ ≤ pbwFiltration R L 1 :=
  TauCeti.Algebra.range_le_wordFiltration_one ueaιₗ

/-- Multiplication adds PBW filtration degrees. -/
theorem pbwFiltration_mul (i j : ℕ) :
    pbwFiltration R L i * pbwFiltration R L j = pbwFiltration R L (i + j) :=
  TauCeti.Algebra.wordFiltration_mul ueaιₗ i j

/-- The elementwise multiplicativity of the PBW filtration. -/
theorem mul_mem_pbwFiltration {i j : ℕ} {x y : U} (hx : x ∈ pbwFiltration R L i)
    (hy : y ∈ pbwFiltration R L j) : x * y ∈ pbwFiltration R L (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltration ueaιₗ hx hy

/-- The PBW filtration is the increasing union of powers of the canonical generator range. -/
theorem pbwFiltration_eq_iSup_pow (k : ℕ) :
    pbwFiltration R L k =
      ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range ueaιₗ ^ (i : ℕ) :=
  TauCeti.Algebra.wordFiltration_eq_iSup_pow ueaιₗ k

/-- The successor PBW step adjoins words of exactly the new degree. -/
theorem pbwFiltration_succ_eq_sup (k : ℕ) :
    pbwFiltration R L (k + 1) =
      pbwFiltration R L k ⊔ LinearMap.range ueaιₗ ^ (k + 1) :=
  TauCeti.Algebra.wordFiltration_succ_eq_sup ueaιₗ k

/-- PBW filtration degree one consists of the scalars and the canonical Lie generators. -/
@[simp]
theorem pbwFiltration_one :
    pbwFiltration R L 1 = 1 ⊔ LinearMap.range ueaιₗ :=
  TauCeti.Algebra.wordFiltration_one ueaιₗ

/-- The image of every tensor-algebra element belongs to some PBW filtration step. -/
private theorem exists_mem_pbwFiltration_mkAlgHom
    (x : TensorAlgebra R L) :
    ∃ k, _root_.UniversalEnvelopingAlgebra.mkAlgHom R L x ∈ pbwFiltration R L k := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      exact ⟨0, algebraMap_mem_pbwFiltration R L r 0⟩
  | ι x =>
      exact ⟨1, by
        simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using
          ι_mem_pbwFiltration_one R L x⟩
  | add x y hx hy =>
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      refine ⟨max i j, ?_⟩
      rw [map_add]
      exact Submodule.add_mem _
        (pbwFiltration_mono R L (Nat.le_max_left i j) hi)
        (pbwFiltration_mono R L (Nat.le_max_right i j) hj)
  | mul x y hx hy =>
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      exact ⟨i + j, by simpa only [map_mul] using mul_mem_pbwFiltration R L hi hj⟩

/-- The PBW filtration is exhaustive: every element of `U(L)` is represented by a tensor-algebra
expression and hence belongs to a finite word-length step. -/
theorem iSup_pbwFiltration_eq_top : ⨆ k, pbwFiltration R L k = ⊤ := by
  rw [eq_top_iff]
  intro x _
  -- Expose the enveloping algebra as its defining tensor-algebra quotient.
  obtain ⟨x, rfl⟩ := (show Function.Surjective
    (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L) from Quotient.mk_surjective) x
  obtain ⟨k, hk⟩ := exists_mem_pbwFiltration_mkAlgHom R L x
  exact Submodule.mem_iSup_of_mem k hk

/-- The PBW filtration carries Mathlib's bundled ring-filtration structure. -/
instance : IsRingFiltration (pbwFiltration R L) (pbwFiltrationPrevious R L) :=
  TauCeti.Algebra.wordFiltration.instIsRingFiltration ueaιₗ

end TauCeti.UniversalEnvelopingAlgebra
