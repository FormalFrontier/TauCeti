/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Idempotents

/-!
# Path algebras of quivers

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
* `TauCeti.PathAlgebra.liftAlgHom`: **the universal property of the path algebra**, extending an
  assignment of elements of a `k`-algebra to the basis paths to an algebra homomorphism out of
  `kQ`, the only one doing so by `TauCeti.PathAlgebra.liftAlgHom_unique`.

## Main results

* `TauCeti.PathAlgebra.single_mul_single`: the defining product of two basis paths.
* `TauCeti.PathAlgebra.one_def`: the vertex idempotents sum to `1`; they are
  orthogonal by `TauCeti.PathAlgebra.vertexIdempotent_mul_vertexIdempotent_of_ne`, idempotent by
  `TauCeti.PathAlgebra.vertexIdempotent_mul_self` and nonzero by
  `TauCeti.PathAlgebra.vertexIdempotent_ne_zero`. The first three are bundled as
  `TauCeti.PathAlgebra.completeOrthogonalIdempotents_vertexIdempotent`.
* `TauCeti.module_finite_pathAlgebra` and `TauCeti.finrank_pathAlgebra`: `kQ` is a free module of
  rank the number of paths of `Q`, with `TauCeti.pathAlgebraBasis_repr_single` reading off the
  coordinates of a basis path. The specialization to a finite acyclic quiver, whose paths are
  finite, is `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` in
  `TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra`.
* `TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`: when the trivial path is the only path from
  `v` to itself, `eᵥ f eᵥ` is the coefficient of `f` on that path, times `eᵥ`, so the corner
  `eᵥ kQ eᵥ` is a copy of `k`. This is what makes the trivial paths visible to a two-sided ideal.
* `TauCeti.PathAlgebra.adjoin_vertexIdempotents_union_arrows`: the vertex idempotents and arrows
  generate the path algebra.

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

/-! ### The index type of the path basis -/

/-- The total space of the paths of a quiver: a path together with its source and target. This is
the index type of the path basis of the path algebra. -/
abbrev Quiver.TotalPath (Q : Type u) [Quiver.{v} Q] : Type _ :=
  Σ a b : Q, _root_.Quiver.Path a b

namespace Quiver.TotalPath

variable {Q : Type u} [Quiver.{v} Q]

/-- An indexed path is the trivial path at `v` exactly when it starts at `v` and has length zero.
Stated this way the equality is checked against two non-dependent conditions, so recognizing a
trivial path inside a concatenation needs no transport along the endpoints. -/
@[simp]
theorem eq_nil_iff {v : Q} {x : TotalPath Q} :
    x = ⟨v, v, _root_.Quiver.Path.nil⟩ ↔ x.1 = v ∧ x.2.2.length = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨a, b, p⟩ := x
    rintro ⟨rfl, hlen⟩
    obtain rfl : a = b := p.eq_of_length_zero hlen
    obtain rfl : p = _root_.Quiver.Path.nil := p.eq_nil_of_length_zero hlen
    rfl

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
  simp only [mul?, dite_eq_right h]

/-- The concatenation of two indexed paths is undefined exactly when they do not meet. -/
theorem mul?_eq_none_iff {x y : TotalPath Q} : mul? x y = none ↔ y.2.1 ≠ x.1 := by
  refine ⟨fun h hne => ?_, mul?_eq_none⟩
  rw [mul?, dite_eq_left hne] at h
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

variable (k) in
/-- The vertex idempotent is the basis element of the trivial path at its vertex. -/
theorem vertexIdempotent_eq_ofPath (v : Q) :
    vertexIdempotent k v = ofPath (⟨v, v, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q) := by
  rw [vertexIdempotent_eq_single, ofPath_eq_single]

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

/-- A vertex idempotent is nonzero: it is the basis path of the trivial path at its vertex, whose
coefficient is `1`. -/
@[simp]
theorem vertexIdempotent_ne_zero [Nontrivial k] (v : Q) :
    (vertexIdempotent k v : pathAlgebra k Q) ≠ 0 := by
  rw [vertexIdempotent_eq_single, single_def]
  exact Finsupp.single_ne_zero.2 one_ne_zero

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
  let := Fintype.ofFinite Q
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
  let := Fintype.ofFinite Q
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

variable (k Q) in
/-- **The vertex idempotents are a complete orthogonal family of idempotents**: they are
idempotent, pairwise orthogonal, and sum to `1`. This bundles `TauCeti.PathAlgebra.one_def`
with the orthogonality and idempotency above. -/
theorem completeOrthogonalIdempotents_vertexIdempotent [Fintype Q] :
    CompleteOrthogonalIdempotents fun v : Q => (vertexIdempotent k v : pathAlgebra k Q) where
  idem v := vertexIdempotent_mul_self v
  ortho _ _ h := vertexIdempotent_mul_vertexIdempotent_of_ne h
  complete := one_def.symm

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

variable {k Q}

/-- The coordinates of a basis path for the path basis. -/
@[simp]
theorem pathAlgebraBasis_repr_single (x : Quiver.TotalPath Q) (c : k) :
    (pathAlgebraBasis k Q).repr (PathAlgebra.single x c) = Finsupp.single x c := by
  have hx : (PathAlgebra.single x c : pathAlgebra k Q) = c • pathAlgebraBasis k Q x := by
    simp [coe_pathAlgebraBasis, PathAlgebra.ofPath_eq_single]
  rw [hx, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

open PathAlgebra in
/-- **Conjugating by a vertex idempotent reads off a coordinate.** When the trivial path is the
only path from `v` to itself, `eᵥ f eᵥ` is the coordinate of `f` on that path, times `eᵥ`, so that
the corner `eᵥ kQ eᵥ` is a copy of `k`. An acyclic quiver supplies the hypothesis through
`TauCeti.Quiver.IsAcyclic.eq_nil`. -/
theorem vertexIdempotent_mul_mul_vertexIdempotent (v : Q)
    (h : ∀ p : _root_.Quiver.Path v v, p = _root_.Quiver.Path.nil) (f : pathAlgebra k Q) :
    vertexIdempotent k v * f * vertexIdempotent k v
      = (pathAlgebraBasis k Q).repr f ⟨v, v, _root_.Quiver.Path.nil⟩ • vertexIdempotent k v := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [mul_add, add_mul, hf, hg, map_add, Finsupp.add_apply, add_smul]
  | single x c =>
    obtain ⟨a, b, p⟩ := x
    rw [pathAlgebraBasis_repr_single, vertexIdempotent_eq_single, smul_single, mul_one]
    by_cases hb : v = b
    · subst hb
      rw [single_mul_single_of_comp (p := _root_.Quiver.Path.nil) (q := p) 1 c, one_mul,
        _root_.Quiver.Path.comp_nil]
      by_cases ha : v = a
      · subst ha
        obtain rfl := h p
        rw [single_mul_single_of_comp (p := _root_.Quiver.Path.nil)
            (q := _root_.Quiver.Path.nil) c 1, mul_one,
          _root_.Quiver.Path.comp_nil, Finsupp.single_eq_same]
      · have hne : (⟨a, v, p⟩ : Quiver.TotalPath Q) ≠ ⟨v, v, _root_.Quiver.Path.nil⟩ := by
          intro heq
          have hav : a = v := congrArg (fun z : Quiver.TotalPath Q => z.1) heq
          exact ha hav.symm
        rw [single_mul_single_of_not_composable
          (x := ⟨a, v, p⟩) (y := ⟨v, v, _root_.Quiver.Path.nil⟩) ha c 1,
          Finsupp.single_eq_of_ne' hne, single_zero]
    · have hne : (⟨a, b, p⟩ : Quiver.TotalPath Q) ≠ ⟨v, v, _root_.Quiver.Path.nil⟩ := by
        intro heq
        have hbv : b = v := congrArg (fun z : Quiver.TotalPath Q => z.2.1) heq
        exact hb hbv.symm
      rw [single_mul_single_of_not_composable
        (x := ⟨v, v, _root_.Quiver.Path.nil⟩) (y := ⟨a, b, p⟩) (fun hbv => hb hbv.symm) 1 c,
        zero_mul, Finsupp.single_eq_of_ne' hne, single_zero]

end Basis

/-! ### The universal property -/

namespace PathAlgebra

section Lift

variable (k : Type w) {Q : Type u} {B : Type*} [CommSemiring k] [Quiver.{v} Q]
  [Semiring B] [Algebra k B] (F : Quiver.TotalPath Q → B)

/-- The `k`-linear map extending an assignment of algebra elements to the basis paths. Private:
only its algebra-homomorphism upgrade `TauCeti.PathAlgebra.liftAlgHom` is public. -/
private noncomputable def liftLinear : pathAlgebra k Q →ₗ[k] B :=
  (pathAlgebraBasis k Q).constr k F

private theorem liftLinear_ofPath (x : Quiver.TotalPath Q) : liftLinear k F (ofPath x) = F x := by
  have h := (pathAlgebraBasis k Q).constr_basis k F x
  rwa [coe_pathAlgebraBasis] at h

private theorem liftLinear_single (x : Quiver.TotalPath Q) (c : k) :
    liftLinear k F (single x c) = c • F x := by
  have hx : (single x c : pathAlgebra k Q) = c • ofPath x := by
    rw [ofPath_eq_single, smul_single, mul_one]
  rw [hx, map_smul, liftLinear_ofPath]

variable (hcomp : ∀ {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path c a),
    F ⟨a, b, p⟩ * F ⟨c, a, q⟩ = F ⟨c, b, q.comp p⟩)
  (hzero : ∀ {x y : Quiver.TotalPath Q}, y.2.1 ≠ x.1 → F x * F y = 0)

include hcomp hzero in
private theorem liftLinear_mul (f g : pathAlgebra k Q) :
    liftLinear k F (f * g) = liftLinear k F f * liftLinear k F g := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | single x c =>
    induction g using PathAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | single y d =>
      obtain ⟨a, b, p⟩ := x
      obtain ⟨c', a', q⟩ := y
      by_cases hy : a' = a
      · subst hy
        rw [single_mul_single_of_comp, liftLinear_single, liftLinear_single, liftLinear_single,
          smul_mul_smul_comm, hcomp]
      · rw [single_mul_single_of_not_composable hy, map_zero, liftLinear_single, liftLinear_single,
          smul_mul_smul_comm, hzero hy, smul_zero]

-- The enumeration is the one the unit is built from, `Fintype.ofFinite Q`; a caller holding the
-- sum over some other `Fintype Q` transports it along `Subsingleton.elim`, as `one_def` does.
variable [Finite Q]
  (hone : letI := Fintype.ofFinite Q; ∑ v : Q, F ⟨v, v, _root_.Quiver.Path.nil⟩ = 1)

include hone in
private theorem liftLinear_one : liftLinear k F (1 : pathAlgebra k Q) = 1 := by
  let _ := Fintype.ofFinite Q
  rw [one_def, map_sum]
  simp only [vertexIdempotent_eq_single, liftLinear_single, one_smul]
  exact hone

include hcomp hzero hone in
/-- **The universal property of the path algebra**: an assignment `F` of elements of a `k`-algebra
`B` to the basis paths extends to a `k`-algebra homomorphism `kQ →ₐ[k] B` as soon as it turns the
three defining products of `kQ` into products in `B` — composable paths concatenate (`hcomp`,
later factor first, as `TauCeti.PathAlgebra.single_mul_single_of_comp` multiplies them), paths that
do not meet annihilate one another (`hzero`), and the trivial paths give a decomposition of the
unit (`hone`), as `TauCeti.PathAlgebra.one_def` says of the vertex idempotents. -/
noncomputable def liftAlgHom : pathAlgebra k Q →ₐ[k] B :=
  AlgHom.ofLinearMap (liftLinear k F) (liftLinear_one k F hone) (liftLinear_mul k F hcomp hzero)

/-- **The lift extends the assignment**: a basis path goes to the element it was assigned. -/
@[simp]
theorem liftAlgHom_ofPath (x : Quiver.TotalPath Q) :
    liftAlgHom k F hcomp hzero hone (ofPath x) = F x :=
  liftLinear_ofPath k F x

/-- The lift is `k`-linear, so a scaled basis path scales the element it was assigned. -/
@[simp]
theorem liftAlgHom_single (x : Quiver.TotalPath Q) (c : k) :
    liftAlgHom k F hcomp hzero hone (single x c) = c • F x :=
  liftLinear_single k F x c

/-- **The lift is the only one**: an algebra homomorphism out of `kQ` taking the value `F x` on
each basis path is `TauCeti.PathAlgebra.liftAlgHom`, since the basis paths span. -/
theorem liftAlgHom_unique (G : pathAlgebra k Q →ₐ[k] B) (hG : ∀ x, G (ofPath x) = F x) :
    G = liftAlgHom k F hcomp hzero hone :=
  AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
    simp only [AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, hG, liftAlgHom_ofPath]

end Lift

end PathAlgebra

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

end PathAlgebra

end TauCeti
