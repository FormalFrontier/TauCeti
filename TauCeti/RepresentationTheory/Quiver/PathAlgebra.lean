/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# The path algebra of a quiver

The path algebra `kQ` of a quiver `Q` over a semiring `k` is the free `k`-module on the paths of
`Q`, with the product of two paths their concatenation when they are composable and `0` otherwise.

Paths are concatenated in the *later factor first* order: for `p : Path a b` and `q : Path c a`,
the product of the corresponding basis elements is the basis element of `q.comp p : Path c b`.
With this convention an arrow `α : i ⟶ j` satisfies `eⱼ * α = α = α * eᵢ` for the vertex
idempotents `e`, so left multiplication by `α` carries the `i`-component of a left module to its
`j`-component: representations of `Q` are left `kQ`-modules.

## Main definitions

* `TauCeti.Quiver.TotalPath Q`: the total space `Σ a b, Path a b` of the paths of `Q`, the index
  type of the path basis.
* `TauCeti.Quiver.TotalPath.mul?`: concatenation of two indexed paths, `none` when they are not
  composable.
* `TauCeti.pathAlgebra k Q`: the path algebra, with `TauCeti.PathAlgebra.single` its basis
  elements. It is a non-unital semiring for any quiver, and carries `Semiring`, `Ring` and
  `Algebra k` structures once the vertex type is `Finite`, finiteness being what makes the unit
  `1 = ∑ᵥ eᵥ` exist.
* `TauCeti.PathAlgebra.vertexIdempotent`: the idempotent `eᵥ` given by the trivial path at `v`.
* `TauCeti.pathAlgebraBasis`: the paths of `Q` as a `k`-basis of `kQ`.
* `TauCeti.Quiver.OneLoop`: the quiver with one vertex and one loop.

## Main results

* `TauCeti.PathAlgebra.single_mul_single`: the defining product of two basis paths.
* `TauCeti.PathAlgebra.one_def`: the vertex idempotents sum to `1`; they are
  orthogonal by `TauCeti.PathAlgebra.vertexIdempotent_mul_vertexIdempotent_of_ne`.
* `TauCeti.module_finite_pathAlgebra` and `TauCeti.finrank_pathAlgebra`: `kQ` is a free module of
  rank the number of paths of `Q`. The specialization to a finite acyclic quiver, whose paths are
  finite, is `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` in
  `TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra`.
* `TauCeti.PathAlgebra.adjoin_vertexIdempotents_union_arrows`: the vertex idempotents and arrows
  generate the path algebra.
* `TauCeti.PathAlgebra.oneLoopAlgEquiv`: the one-loop path algebra is the additive monoid algebra
  on `ℕ`; `TauCeti.not_finiteDimensional_pathAlgebra_oneLoop` records that it is
  infinite-dimensional.

## Implementation notes

`pathAlgebra k Q` is a semireducible type synonym for `Quiver.TotalPath Q →₀ k`, following the
pattern of `MonoidAlgebra`: were it reducible, instance search would unfold it and pick up the
*pointwise* multiplication of `Finsupp`. The multiplication is therefore introduced as an
operation `mul'` on `Quiver.TotalPath Q →₀ k` (with `singleOption` naming the product of two basis
paths, which is a basis path or `0`), where the `Finsupp` API applies without friction; the ring
axioms are proved there and transferred definitionally.

That whole layer is private. The exposed `Mul` instance spells out the same operation because it
cannot mention a private declaration; `mul_def` records their definitional agreement. The ring
axioms reach the structure instances through a `by exact` for the same reason. `pathAlgebra` is the
only definition whose body is `@[expose]`d, because the transported instances unfold it; every other
definition here is opaque downstream, which sees the path algebra through its algebraic structure
and the lemmas below
(`ofPath_eq_single` and `vertexIdempotent_eq_single` for the basis elements, `single_mul_single`
and the `mul?` lemmas for products) rather than through the `Finsupp` representation.

Since `Finset.univ` is data, the unit is the sum of the vertex idempotents over a `Fintype`
structure chosen internally by `Fintype.ofFinite`; the unital instances therefore ask only for
`[Finite Q]`, and `one_def` identifies `1` with the sum over *any* `Fintype Q` a caller supplies.

## References

This file implements the path-algebra part of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

/-! ### The one-loop quiver -/

namespace Quiver

/-- The quiver with one vertex and one loop. -/
inductive OneLoop : Type
  | vertex
  deriving DecidableEq

namespace OneLoop

instance : Fintype OneLoop where
  elems := {vertex}
  complete x := by cases x; simp

instance : Unique OneLoop where
  default := vertex
  uniq x := by cases x; rfl

instance : _root_.Quiver OneLoop where
  Hom _ _ := PUnit

instance (a b : OneLoop) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique loop in the one-loop quiver. -/
def loop : (vertex : OneLoop) ⟶ vertex := PUnit.unit

/-- The path of a prescribed length in the one-loop quiver. -/
private def pathOfLength : ℕ → _root_.Quiver.Path (vertex : OneLoop) vertex
  | 0 => .nil
  | n + 1 => (pathOfLength n).cons loop

@[simp]
private theorem length_pathOfLength (n : ℕ) : (pathOfLength n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathOfLength, ih]

private theorem length_toList {a b : OneLoop}
    (p : _root_.Quiver.Path a b) : p.toList.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

private theorem path_eq_pathOfLength (p : _root_.Quiver.Path (vertex : OneLoop) vertex) :
    p = pathOfLength p.length := by
  apply (_root_.Quiver.Path.toList_injective vertex vertex)
  apply List.length_injective
  rw [length_toList, length_toList, length_pathOfLength]

end OneLoop

end Quiver

/-! ### The index type of the path basis -/

/-- The total space of the paths of a quiver: a path together with its source and target. This is
the index type of the path basis of the path algebra. -/
abbrev Quiver.TotalPath (Q : Type u) [Quiver.{v} Q] : Type _ :=
  Σ a b : Q, _root_.Quiver.Path a b

namespace Quiver.OneLoop

/-- Paths in the one-loop quiver are classified by their length. -/
private def totalPathEquivNat : Quiver.TotalPath OneLoop ≃ ℕ where
  toFun x := x.2.2.length
  invFun n := ⟨vertex, vertex, pathOfLength n⟩
  left_inv x := by
    obtain ⟨a, b, p⟩ := x
    cases a
    cases b
    simp only
    exact congrArg (fun q => (⟨vertex, vertex, q⟩ : Quiver.TotalPath OneLoop))
      (path_eq_pathOfLength p).symm
  right_inv := length_pathOfLength

end Quiver.OneLoop

namespace Quiver.TotalPath

variable {Q : Type u} [Quiver.{v} Q]

open scoped Classical in
/-- Concatenation of indexed paths in the *later factor first* order used by the path algebra:
`x.mul? y` traces `y` and then `x`, and is `none` unless `y` ends where `x` starts. -/
noncomputable def mul? (x y : TotalPath Q) : Option (TotalPath Q) :=
  if h : y.2.1 = x.1 then some ⟨y.1, x.2.1, (h ▸ y.2.2).comp x.2.2⟩ else none

/-- Composable indexed paths concatenate, the later factor written first. -/
@[simp]
theorem mul?_mk {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path c a) :
    mul? (⟨a, b, p⟩ : TotalPath Q) ⟨c, a, q⟩ = some ⟨c, b, q.comp p⟩ := by
  simp [mul?]

/-- Indexed paths that do not meet have no concatenation. -/
theorem mul?_eq_none {x y : TotalPath Q} (h : y.2.1 ≠ x.1) : mul? x y = none := by
  simp only [mul?, dif_neg h]

/-- The concatenation of two indexed paths is undefined exactly when they do not meet. -/
theorem mul?_eq_none_iff {x y : TotalPath Q} : mul? x y = none ↔ y.2.1 ≠ x.1 := by
  refine ⟨fun h hne => ?_, mul?_eq_none⟩
  rw [mul?, dif_pos hne] at h
  exact Option.some_ne_none _ h

/-- The trivial path at the target of `x` is a left unit for `x`. -/
@[simp]
theorem mul?_nil_left (x : TotalPath Q) :
    mul? (⟨x.2.1, x.2.1, _root_.Quiver.Path.nil⟩ : TotalPath Q) x = some x := by
  obtain ⟨a, b, p⟩ := x
  simp

/-- The trivial path at the source of `x` is a right unit for `x`. -/
@[simp]
theorem mul?_nil_right (x : TotalPath Q) :
    mul? x (⟨x.1, x.1, _root_.Quiver.Path.nil⟩ : TotalPath Q) = some x := by
  obtain ⟨a, b, p⟩ := x
  simp [_root_.Quiver.Path.nil_comp]

/-- Concatenation of indexed paths is associative as a partial operation. -/
theorem mul?_assoc (x y z : TotalPath Q) :
    ((x.mul? y).bind fun w => w.mul? z) = (y.mul? z).bind fun w => x.mul? w := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  obtain ⟨e, f, r⟩ := z
  by_cases h₁ : d = a
  · subst h₁
    by_cases h₂ : f = c
    · subst h₂
      simp [_root_.Quiver.Path.comp_assoc]
    · rw [mul?_mk, Option.bind_some, mul?_eq_none (by simpa using h₂),
        mul?_eq_none (by simpa using h₂), Option.bind_none]
  · rw [mul?_eq_none (by simpa using h₁), Option.bind_none]
    by_cases h₂ : f = c
    · subst h₂
      rw [mul?_mk, Option.bind_some, mul?_eq_none (by simpa using h₁)]
    · rw [mul?_eq_none (by simpa using h₂), Option.bind_none]

end Quiver.TotalPath

/-! ### The path algebra -/

/-- The path algebra of a quiver `Q` over `k`: the free `k`-module on the paths of `Q`, with
multiplication the concatenation of composable paths in the *later factor first* order, and `0` on
non-composable pairs.

This is a semireducible type synonym so that instance search does not confuse the path
multiplication with the pointwise multiplication of `Finsupp`. -/
@[expose] def pathAlgebra (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q] : Type _ :=
  Quiver.TotalPath Q →₀ k

namespace PathAlgebra

section Semiring

variable {k : Type w} {Q : Type u} [Semiring k] [Quiver.{v} Q]

noncomputable instance : AddCommMonoid (pathAlgebra k Q) :=
  inferInstanceAs (AddCommMonoid (Quiver.TotalPath Q →₀ k))

noncomputable instance : Module k (pathAlgebra k Q) :=
  inferInstanceAs (Module k (Quiver.TotalPath Q →₀ k))

noncomputable instance : Inhabited (pathAlgebra k Q) :=
  inferInstanceAs (Inhabited (Quiver.TotalPath Q →₀ k))

/-- The basis element of the path algebra attached to a path, with a coefficient. -/
noncomputable def single (x : Quiver.TotalPath Q) (c : k) : pathAlgebra k Q :=
  Finsupp.single x c

/-- A basis path is the corresponding `Finsupp.single`, read through the type synonym. -/
private theorem single_def (x : Quiver.TotalPath Q) (c : k) :
    (single x c : pathAlgebra k Q) = Finsupp.single x c := rfl

/-- A basis path with coefficient zero is zero. -/
@[simp]
theorem single_zero (x : Quiver.TotalPath Q) : (single x (0 : k) : pathAlgebra k Q) = 0 :=
  Finsupp.single_zero x

/-- Basis paths are additive in their coefficient. -/
theorem single_add (x : Quiver.TotalPath Q) (c d : k) :
    (single x (c + d) : pathAlgebra k Q) = single x c + single x d :=
  Finsupp.single_add x c d

/-- Scaling a basis path scales its coefficient. -/
@[simp]
theorem smul_single (r : k) (x : Quiver.TotalPath Q) (c : k) :
    r • (single x c : pathAlgebra k Q) = single x (r * c) :=
  Finsupp.smul_single r x c

/-- Additive induction on the path algebra: it suffices to treat `0`, sums, and basis paths. -/
@[elab_as_elim]
theorem induction_linear {motive : pathAlgebra k Q → Prop} (f : pathAlgebra k Q)
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (single : ∀ x c, motive (PathAlgebra.single x c)) : motive f :=
  Finsupp.induction_linear (motive := motive) f zero add single

/-! ### The multiplication -/

/-- `Finsupp.single` at an optional index, the zero function at `none`. It spells the product of
two basis paths uniformly: a single path when they are composable, and `0` otherwise. -/
private noncomputable def singleOption (o : Option (Quiver.TotalPath Q)) (c : k) :
    Quiver.TotalPath Q →₀ k :=
  o.elim 0 fun x => Finsupp.single x c

/-- An absent index contributes nothing. -/
@[simp]
private theorem singleOption_none (c : k) : singleOption (Q := Q) none c = 0 := rfl

/-- A present index contributes the corresponding basis path. -/
@[simp]
private theorem singleOption_some (x : Quiver.TotalPath Q) (c : k) :
    singleOption (some x) c = Finsupp.single x c := rfl

/-- The coefficient zero contributes nothing. -/
@[simp]
private theorem singleOption_zero (o : Option (Quiver.TotalPath Q)) :
    singleOption o (0 : k) = 0 := by
  cases o <;> simp

/-- `singleOption` is additive in its coefficient. -/
private theorem singleOption_add (o : Option (Quiver.TotalPath Q)) (c d : k) :
    singleOption o (c + d) = singleOption o c + singleOption o d := by
  cases o <;> simp [Finsupp.single_add]

/-- `singleOption` absorbs scalars into its coefficient. -/
private theorem smul_singleOption (r : k) (o : Option (Quiver.TotalPath Q)) (c : k) :
    r • singleOption o c = singleOption o (r * c) := by
  cases o <;> simp [Finsupp.smul_single]

/-- The multiplication of the path algebra, at the level of finitely supported functions. -/
private noncomputable def mul' (f g : Quiver.TotalPath Q →₀ k) : Quiver.TotalPath Q →₀ k :=
  f.sum fun x a => g.sum fun y b => singleOption (x.mul? y) (a * b)

/-- The multiplication kills zero on the left. -/
@[simp]
private theorem mul'_zero_left (g : Quiver.TotalPath Q →₀ k) :
    mul' (0 : Quiver.TotalPath Q →₀ k) g = 0 := by
  simp [mul']

/-- The multiplication kills zero on the right. -/
@[simp]
private theorem mul'_zero_right (f : Quiver.TotalPath Q →₀ k) :
    mul' f (0 : Quiver.TotalPath Q →₀ k) = 0 := by
  simp [mul']

/-- The multiplication is additive in its left argument. -/
private theorem mul'_add_left (f₁ f₂ g : Quiver.TotalPath Q →₀ k) :
    mul' (f₁ + f₂) g = mul' f₁ g + mul' f₂ g := by
  refine Finsupp.sum_add_index' (fun x => ?_) fun x a₁ a₂ => ?_
  · simp
  · rw [← Finsupp.sum_add]
    exact Finsupp.sum_congr fun y _ => by rw [add_mul, singleOption_add]

/-- The multiplication is additive in its right argument. -/
private theorem mul'_add_right (f g₁ g₂ : Quiver.TotalPath Q →₀ k) :
    mul' f (g₁ + g₂) = mul' f g₁ + mul' f g₂ := by
  simp only [mul']
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr fun x _ =>
    Finsupp.sum_add_index' (fun y => by simp) fun y b₁ b₂ => by
      rw [mul_add, singleOption_add]

/-- The multiplication on basis paths is the partial concatenation of their indices. -/
private theorem mul'_single_single (x y : Quiver.TotalPath Q) (a b : k) :
    mul' (Finsupp.single x a) (Finsupp.single y b) = singleOption (x.mul? y) (a * b) := by
  rw [mul', Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

/-- Multiplying an optional basis path by a basis path binds the two indices. -/
private theorem mul'_singleOption_single (o : Option (Quiver.TotalPath Q)) (c : k)
    (y : Quiver.TotalPath Q) (b : k) :
    mul' (singleOption o c) (Finsupp.single y b)
      = singleOption (o.bind fun w => w.mul? y) (c * b) := by
  cases o with
  | none => simp
  | some x => rw [singleOption_some, mul'_single_single, Option.bind_some]

/-- Multiplying a basis path by an optional basis path binds the two indices. -/
private theorem mul'_single_singleOption (x : Quiver.TotalPath Q) (a : k)
    (o : Option (Quiver.TotalPath Q)) (c : k) :
    mul' (Finsupp.single x a) (singleOption o c)
      = singleOption (o.bind fun w => x.mul? w) (a * c) := by
  cases o with
  | none => simp
  | some y => rw [singleOption_some, mul'_single_single, Option.bind_some]

/-- The multiplication is associative, by associativity of path concatenation. -/
private theorem mul'_assoc (f g t : Quiver.TotalPath Q →₀ k) :
    mul' (mul' f g) t = mul' f (mul' g t) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp only [mul'_add_left, ih₁, ih₂]
  | single x a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp only [mul'_add_left, mul'_add_right, ih₁, ih₂]
    | single y b =>
      induction t using Finsupp.induction_linear with
      | zero => simp
      | add t₁ t₂ ih₁ ih₂ => simp only [mul'_add_right, ih₁, ih₂]
      | single z c =>
        rw [mul'_single_single, mul'_single_single, mul'_singleOption_single,
          mul'_single_singleOption, Quiver.TotalPath.mul?_assoc, mul_assoc]

/-- The multiplication is homogeneous in its left argument. -/
private theorem smul_mul' (r : k) (f g : Quiver.TotalPath Q →₀ k) :
    mul' (r • f) g = r • mul' f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp only [smul_add, mul'_add_left, ih₁, ih₂]
  | single x a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp only [smul_add, mul'_add_right, ih₁, ih₂]
    | single y b =>
      rw [Finsupp.smul_single, mul'_single_single, mul'_single_single, smul_singleOption,
        smul_eq_mul, mul_assoc]

noncomputable instance : Mul (pathAlgebra k Q) :=
  ⟨fun f g =>
    f.sum fun x a => g.sum fun y b =>
      (x.mul? y).elim 0 fun z => Finsupp.single z (a * b)⟩

/-- The multiplication of the path algebra is `mul'`, read through the type synonym. This is the
only place the identification is used; every product below is computed from it. -/
private theorem mul_def (f g : pathAlgebra k Q) : f * g = mul' f g := rfl

-- The axioms below are the `mul'` lemmas above, which are private: an instance body is exposed,
-- so it can only mention them through a `by exact`, which elaborates to a lifted private proof.
noncomputable instance : NonUnitalNonAssocSemiring (pathAlgebra k Q) where
  left_distrib := by exact mul'_add_right
  right_distrib := by exact mul'_add_left
  zero_mul := by exact mul'_zero_left
  mul_zero := by exact mul'_zero_right

noncomputable instance : NonUnitalSemiring (pathAlgebra k Q) where
  mul_assoc := by exact mul'_assoc

/-! ### Products of basis paths -/

/-- The defining product of two basis paths: their concatenation, later factor first, when they
are composable, and `0` otherwise. -/
@[simp]
theorem single_mul_single (x y : Quiver.TotalPath Q) (a b : k) :
    (single x a * single y b : pathAlgebra k Q)
      = (x.mul? y).elim 0 fun z => single z (a * b) := by
  rw [mul_def, single_def, single_def, mul'_single_single]
  cases x.mul? y <;> rfl

/-- Multiplying two composable basis paths concatenates them, later factor first. -/
theorem single_mul_single_of_comp {a b c : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path c a) (r s : k) :
    (single (⟨a, b, p⟩ : Quiver.TotalPath Q) r * single ⟨c, a, q⟩ s : pathAlgebra k Q)
      = single ⟨c, b, q.comp p⟩ (r * s) := by
  rw [single_mul_single, Quiver.TotalPath.mul?_mk]
  rfl

/-- The product of two basis paths that are not composable vanishes. -/
theorem single_mul_single_of_not_composable {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) (r s : k) :
    (single x r * single y s : pathAlgebra k Q) = 0 := by
  rw [single_mul_single, Quiver.TotalPath.mul?_eq_none h]
  rfl

/-- The basis element of the path algebra attached to a path. -/
noncomputable def ofPath (x : Quiver.TotalPath Q) : pathAlgebra k Q :=
  single x 1

/-- A path is the basis element it indexes, with coefficient one. -/
theorem ofPath_eq_single (x : Quiver.TotalPath Q) :
    (ofPath x : pathAlgebra k Q) = single x 1 := (rfl)

/-- Two composable paths multiply to their concatenation, later factor first. -/
@[simp]
theorem ofPath_mul_ofPath_of_comp {a b c : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path c a) :
    (ofPath (⟨a, b, p⟩ : Quiver.TotalPath Q) * ofPath ⟨c, a, q⟩ : pathAlgebra k Q)
      = ofPath ⟨c, b, q.comp p⟩ := by
  rw [ofPath_eq_single, ofPath_eq_single, ofPath_eq_single, single_mul_single_of_comp, one_mul]

/-- Two paths that do not meet multiply to zero. -/
@[simp]
theorem ofPath_mul_ofPath_of_not_composable {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    (ofPath x * ofPath y : pathAlgebra k Q) = 0 := by
  rw [ofPath_eq_single, ofPath_eq_single]
  exact single_mul_single_of_not_composable h 1 1

/-! ### The vertex idempotents -/

variable (k) in
/-- The idempotent of the path algebra attached to a vertex: the trivial path at that vertex. -/
noncomputable def vertexIdempotent (v : Q) : pathAlgebra k Q :=
  ofPath ⟨v, v, _root_.Quiver.Path.nil⟩

/-- The vertex idempotent is the basis element of the trivial path, with coefficient one. -/
theorem vertexIdempotent_eq_single (v : Q) :
    vertexIdempotent k v
      = single (⟨v, v, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q) (1 : k) := (rfl)

/-- The vertex idempotent at the target of a path is a left unit for it. -/
@[simp]
theorem vertexIdempotent_mul_single (x : Quiver.TotalPath Q) (r : k) :
    (vertexIdempotent k x.2.1 * single x r : pathAlgebra k Q) = single x r := by
  rw [vertexIdempotent_eq_single, single_mul_single, Quiver.TotalPath.mul?_nil_left,
    Option.elim_some, one_mul]

/-- The vertex idempotent at the source of a path is a right unit for it. -/
@[simp]
theorem single_mul_vertexIdempotent (x : Quiver.TotalPath Q) (r : k) :
    (single x r * vertexIdempotent k x.1 : pathAlgebra k Q) = single x r := by
  rw [vertexIdempotent_eq_single, single_mul_single, Quiver.TotalPath.mul?_nil_right,
    Option.elim_some, mul_one]

/-- The vertex idempotent at the target of a path is a left unit for its canonical element. -/
@[simp]
theorem vertexIdempotent_mul_ofPath {a b : Q} (p : _root_.Quiver.Path a b) :
    (vertexIdempotent k b * ofPath ⟨a, b, p⟩ : pathAlgebra k Q) = ofPath ⟨a, b, p⟩ := by
  exact vertexIdempotent_mul_single (k := k) ⟨a, b, p⟩ 1

/-- The vertex idempotent at the source of a path is a right unit for its canonical element. -/
@[simp]
theorem ofPath_mul_vertexIdempotent {a b : Q} (p : _root_.Quiver.Path a b) :
    (ofPath ⟨a, b, p⟩ * vertexIdempotent k a : pathAlgebra k Q) = ofPath ⟨a, b, p⟩ := by
  exact single_mul_vertexIdempotent (k := k) ⟨a, b, p⟩ 1

/-- A vertex idempotent not at the target of a path annihilates its canonical element on the
left. -/
@[simp]
theorem vertexIdempotent_mul_ofPath_of_ne {v : Q} (x : Quiver.TotalPath Q) (h : v ≠ x.2.1) :
    (vertexIdempotent k v * ofPath x : pathAlgebra k Q) = 0 := by
  rw [vertexIdempotent_eq_single, ofPath_eq_single]
  exact single_mul_single_of_not_composable h.symm 1 1

/-- A vertex idempotent not at the source of a path annihilates its canonical element on the
right. -/
@[simp]
theorem ofPath_mul_vertexIdempotent_of_ne {v : Q} (x : Quiver.TotalPath Q) (h : v ≠ x.1) :
    (ofPath x * vertexIdempotent k v : pathAlgebra k Q) = 0 := by
  rw [ofPath_eq_single, vertexIdempotent_eq_single]
  exact single_mul_single_of_not_composable h 1 1

/-- Distinct vertex idempotents are orthogonal. -/
@[simp]
theorem vertexIdempotent_mul_vertexIdempotent_of_ne {u v : Q} (h : u ≠ v) :
    (vertexIdempotent k u * vertexIdempotent k v : pathAlgebra k Q) = 0 := by
  rw [vertexIdempotent_eq_single, vertexIdempotent_eq_single]
  exact single_mul_single_of_not_composable h.symm 1 1

/-- The vertex idempotents are idempotent. -/
@[simp]
theorem vertexIdempotent_mul_self (v : Q) :
    (vertexIdempotent k v * vertexIdempotent k v : pathAlgebra k Q) = vertexIdempotent k v := by
  rw [vertexIdempotent_eq_single, single_mul_single_of_comp, one_mul, _root_.Quiver.Path.comp_nil]

/-! ### The unit -/

section Unit

variable [Finite Q]

-- `Finset.univ` is data, so the unit picks an enumeration of the finite vertex type; `one_def`
-- below identifies it with the sum over any `Fintype Q` structure a caller supplies.
noncomputable instance : One (pathAlgebra k Q) :=
  letI := Fintype.ofFinite Q
  ⟨∑ v : Q, vertexIdempotent k v⟩

/-- The unit of the path algebra is the sum of the vertex idempotents: the vertex idempotents are
a decomposition of the unit. -/
theorem one_def [Fintype Q] : (1 : pathAlgebra k Q) = ∑ v : Q, vertexIdempotent k v :=
  Finset.sum_congr (congrArg (@Finset.univ Q) (Subsingleton.elim _ _)) fun _ _ => rfl

-- The unit lemmas on basis paths are the ingredients of the `Semiring` instance below; downstream
-- they are its `one_mul` and `mul_one`, which need no `Fintype` structure.
/-- The sum of the vertex idempotents is a left unit on basis paths. -/
private theorem one_mul_single (x : Quiver.TotalPath Q) (r : k) :
    ((1 : pathAlgebra k Q) * single x r : pathAlgebra k Q) = single x r := by
  letI := Fintype.ofFinite Q
  rw [one_def, Finset.sum_mul, Finset.sum_eq_single x.2.1]
  · exact vertexIdempotent_mul_single x r
  · intro v _ hv
    exact single_mul_single_of_not_composable (x := ⟨v, v, _root_.Quiver.Path.nil⟩)
      (fun h => hv h.symm) 1 r
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The sum of the vertex idempotents is a right unit on basis paths. -/
private theorem single_mul_one (x : Quiver.TotalPath Q) (r : k) :
    (single x r * (1 : pathAlgebra k Q) : pathAlgebra k Q) = single x r := by
  letI := Fintype.ofFinite Q
  rw [one_def, Finset.mul_sum, Finset.sum_eq_single x.1]
  · exact single_mul_vertexIdempotent x r
  · intro v _ hv
    exact single_mul_single_of_not_composable (y := ⟨v, v, _root_.Quiver.Path.nil⟩) hv r 1
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable instance : Semiring (pathAlgebra k Q) where
  one_mul f := by
    induction f using induction_linear with
    | zero => exact mul_zero _
    | add f₁ f₂ ih₁ ih₂ => rw [mul_add, ih₁, ih₂]
    | single x r => exact one_mul_single x r
  mul_one f := by
    induction f using induction_linear with
    | zero => exact zero_mul _
    | add f₁ f₂ ih₁ ih₂ => rw [add_mul, ih₁, ih₂]
    | single x r => exact single_mul_one x r

end Unit

end Semiring

section Ring

variable {k : Type w} {Q : Type u} [Ring k] [Quiver.{v} Q]

noncomputable instance : AddCommGroup (pathAlgebra k Q) :=
  inferInstanceAs (AddCommGroup (Quiver.TotalPath Q →₀ k))

noncomputable instance [Finite Q] : Ring (pathAlgebra k Q) where

end Ring

section Algebra

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- Over a commutative base the multiplication is homogeneous in its right argument. -/
private theorem mul'_smul (r : k) (f g : Quiver.TotalPath Q →₀ k) :
    mul' f (r • g) = r • mul' f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp only [smul_add, mul'_add_left, ih₁, ih₂]
  | single x a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp only [smul_add, mul'_add_right, ih₁, ih₂]
    | single y b =>
      rw [Finsupp.smul_single, mul'_single_single, mul'_single_single, smul_singleOption,
        smul_eq_mul, mul_left_comm]

variable [Finite Q]

noncomputable instance : Algebra k (pathAlgebra k Q) :=
  Algebra.ofModule (by exact fun r x y => smul_mul' r x y) (by exact fun r x y => mul'_smul r x y)

/-- The image of a scalar in the path algebra spreads it over the vertex idempotents. -/
theorem algebraMap_apply [Fintype Q] (r : k) :
    algebraMap k (pathAlgebra k Q) r = ∑ v : Q, r • vertexIdempotent k v := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, Finset.smul_sum]

end Algebra

end PathAlgebra

/-! ### The path basis -/

section Basis

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

/-- The paths of `Q` are a `k`-basis of the path algebra. -/
noncomputable def pathAlgebraBasis :
    Module.Basis (Quiver.TotalPath Q) k (pathAlgebra k Q) :=
  Finsupp.basisSingleOne

/-- The path basis consists of the basis paths. -/
@[simp]
theorem coe_pathAlgebraBasis :
    ⇑(pathAlgebraBasis k Q)
      = fun x : Quiver.TotalPath Q => (PathAlgebra.ofPath x : pathAlgebra k Q) :=
  Finsupp.coe_basisSingleOne

/-- The path algebra of a quiver with finitely many paths is a finite `k`-module. -/
theorem module_finite_pathAlgebra [Finite (Quiver.TotalPath Q)] :
    Module.Finite k (pathAlgebra k Q) :=
  Module.Finite.of_basis (pathAlgebraBasis k Q)

end Basis

section DivisionRing

variable (k : Type w) (Q : Type u) [DivisionRing k] [Quiver.{v} Q]

/-- The dimension of the path algebra is the number of paths of `Q`. -/
theorem finrank_pathAlgebra [Fintype (Quiver.TotalPath Q)] :
    Module.finrank k (pathAlgebra k Q) = Fintype.card (Quiver.TotalPath Q) :=
  Module.finrank_eq_card_basis (pathAlgebraBasis k Q)

end DivisionRing

namespace PathAlgebra

section Generate

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- The path-algebra element attached to an arrow. -/
noncomputable def ofArrow {a b : Q} (e : a ⟶ b) : pathAlgebra k Q :=
  ofPath ⟨a, b, e.toPath⟩

omit [Finite Q] in
/-- An arrow is the basis element indexed by its length-one path. -/
@[simp]
theorem ofArrow_eq_ofPath {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) = ofPath ⟨a, b, e.toPath⟩ := by
  rw [ofArrow]

/-- The vertex idempotents and arrows generate the path algebra. Vertex idempotents are necessary:
arrows alone do not generate the path algebra of, for example, a discrete multi-vertex quiver. -/
theorem adjoin_vertexIdempotents_union_arrows :
    Algebra.adjoin k
        (Set.range (vertexIdempotent k) ∪
          Set.range fun e : Σ a b : Q, a ⟶ b => ofArrow e.2.2) =
      ⊤ := by
  apply top_unique
  suffices ∀ f : pathAlgebra k Q,
      f ∈ Algebra.adjoin k
        (Set.range (vertexIdempotent k) ∪
          Set.range fun e : Σ a b : Q, a ⟶ b => ofArrow e.2.2) by
    exact fun f _ => this f
  intro f
  induction f using induction_linear with
  | zero => exact Subalgebra.zero_mem _
  | add f g hf hg => exact Subalgebra.add_mem _ hf hg
  | single x c =>
      have ofPath_mem (x : Quiver.TotalPath Q) :
          ofPath x ∈
            Algebra.adjoin k
              (Set.range (vertexIdempotent k) ∪
                Set.range fun e : Σ a b : Q, a ⟶ b => ofArrow e.2.2) := by
        obtain ⟨a, b, p⟩ := x
        induction p with
        | nil =>
            exact Algebra.subset_adjoin
              (Set.mem_union_left _ ⟨a, rfl⟩)
        | @cons b c p e ih =>
            rw [← _root_.Quiver.Path.comp_toPath_eq_cons,
              ← ofPath_mul_ofPath_of_comp e.toPath p]
            exact Subalgebra.mul_mem _
              (Algebra.subset_adjoin (Set.mem_union_right _
                ⟨⟨b, c, e⟩, rfl⟩)) ih
      simpa [ofPath_eq_single] using
        (Algebra.adjoin k
          (Set.range (vertexIdempotent k) ∪
            Set.range fun e : Σ a b : Q, a ⟶ b => ofArrow e.2.2)).smul_mem
          (ofPath_mem x) c

end Generate

section OneLoop

variable (k : Type w) [CommSemiring k]

private noncomputable def oneLoopLinearEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₗ[k] AddMonoidAlgebra k ℕ :=
  ((pathAlgebraBasis k Quiver.OneLoop).repr.trans
      (Finsupp.domLCongr Quiver.OneLoop.totalPathEquivNat)).trans
    (AddMonoidAlgebra.coeffLinearEquiv k).symm

private theorem oneLoopLinearEquiv_ofPath (x : Quiver.TotalPath Quiver.OneLoop) :
    oneLoopLinearEquiv k (PathAlgebra.ofPath x) =
      AddMonoidAlgebra.single (Quiver.OneLoop.totalPathEquivNat x) 1 := by
  have hb : pathAlgebraBasis k Quiver.OneLoop x = ofPath x :=
    congrFun (coe_pathAlgebraBasis k Quiver.OneLoop) x
  rw [← hb]
  simp only [oneLoopLinearEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self]
  simp

private theorem oneLoopLinearEquiv_single (x : Quiver.TotalPath Quiver.OneLoop) (c : k) :
    oneLoopLinearEquiv k (single x c) =
      AddMonoidAlgebra.single (Quiver.OneLoop.totalPathEquivNat x) c := by
  rw [← mul_one c, ← smul_single, ← ofPath_eq_single, map_smul,
    oneLoopLinearEquiv_ofPath]
  simp

private theorem oneLoopLinearEquiv_map_one :
    oneLoopLinearEquiv k (1 : pathAlgebra k Quiver.OneLoop) = 1 := by
  rw [one_def]
  simp [vertexIdempotent_eq_single, oneLoopLinearEquiv_single,
    Quiver.OneLoop.totalPathEquivNat, ← AddMonoidAlgebra.one_def]

private theorem oneLoopLinearEquiv_map_mul (f g : pathAlgebra k Quiver.OneLoop) :
    oneLoopLinearEquiv k (f * g) = oneLoopLinearEquiv k f * oneLoopLinearEquiv k g := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂, add_mul]
  | single x a =>
      induction g using induction_linear with
      | zero => simp
      | add g₁ g₂ ih₁ ih₂ => simp [ih₁, ih₂, mul_add]
      | single y b =>
          obtain ⟨x₁, x₂, p⟩ := x
          obtain ⟨y₁, y₂, q⟩ := y
          cases x₁
          cases x₂
          cases y₁
          cases y₂
          simp [single_mul_single, Quiver.TotalPath.mul?,
            oneLoopLinearEquiv_single, Quiver.OneLoop.totalPathEquivNat,
            _root_.Quiver.Path.length_comp, Nat.add_comm]

/-- The path algebra of the quiver with one vertex and one loop is the additive monoid algebra on
`ℕ` (equivalently, the polynomial algebra in one variable). -/
noncomputable def oneLoopAlgEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₐ[k] AddMonoidAlgebra k ℕ :=
  AlgEquiv.ofLinearEquiv (oneLoopLinearEquiv k) (oneLoopLinearEquiv_map_one k)
    (oneLoopLinearEquiv_map_mul k)

end OneLoop

end PathAlgebra

/-- Over a division ring, the path algebra of the one-loop quiver is infinite-dimensional. -/
theorem not_finiteDimensional_pathAlgebra_oneLoop (k : Type w) [DivisionRing k] :
    ¬ FiniteDimensional k (pathAlgebra k Quiver.OneLoop) := by
  letI : Infinite (Quiver.TotalPath Quiver.OneLoop) :=
    Quiver.OneLoop.totalPathEquivNat.infinite_iff.mpr inferInstance
  intro h
  letI : Module.Finite k (pathAlgebra k Quiver.OneLoop) := h
  exact Module.Finite.not_linearIndependent_of_infinite
    (⇑(pathAlgebraBasis k Quiver.OneLoop))
    (pathAlgebraBasis k Quiver.OneLoop).linearIndependent

end TauCeti
