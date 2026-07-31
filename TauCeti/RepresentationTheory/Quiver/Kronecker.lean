/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The generalized Kronecker quiver

The generalized Kronecker quiver has two vertices, a source and a target, and one arrow from the
source to the target for each element of an arrow type `A`. Taking `A = Fin 2` gives the
*Kronecker quiver* `• ⇉ •`, the smallest connected acyclic quiver that is not of Dynkin type and
hence the boundary case of Gabriel's theorem; `A = Fin 1` gives the `A₂` quiver `• → •`. (Dropping
acyclicity there would be wrong: the one-loop quiver of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra` is connected, smaller, and not of Dynkin type.)

This file constructs the quiver, classifies its paths, computes the dimension of its path algebra,
and evaluates its Euler and Tits forms. The arithmetic of the Tits form pins down exactly where the
boundary lies: writing `n` for the number of arrows,

* `titsForm d = d src ^ 2 + d tgt ^ 2 - n * (d src * d tgt)`;
* it is positive definite iff `n ≤ 1`;
* it is positive semidefinite iff `n ≤ 2`, and for `n = 2` it is the perfect square
  `(d src - d tgt) ^ 2`, whose radical is the line spanned by the constant vector `(1, 1)` -- the
  null root of the affine root system `Ã₁`.

## Main definitions

* `TauCeti.Quiver.Kronecker A`: the vertex type, with constructors `src` and `tgt` and a `Quiver`
  instance whose only arrows are `src ⟶ tgt`, indexed by `A`.
* `TauCeti.Quiver.Kronecker.arrow`: the arrow attached to an element of the arrow type.
* `TauCeti.Quiver.Kronecker.pathEquivArrow`: the paths from `src` to `tgt` are the arrows.

## Main results

* `TauCeti.Quiver.Kronecker.isAcyclic`: the quiver is acyclic, so its path algebra is
  finite-dimensional (`TauCeti.Quiver.Kronecker.finiteDimensional_pathAlgebra`).
* `TauCeti.Quiver.Kronecker.card_totalPath` and
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra`: there are `n + 2` paths, so the path algebra has
  dimension `n + 2`; for the Kronecker quiver itself this is `4`.
* `TauCeti.Quiver.Kronecker.eulerForm_apply` and `TauCeti.Quiver.Kronecker.titsForm_apply`: the
  Euler and Tits forms in coordinates.
* `TauCeti.Quiver.Kronecker.titsForm_posDef_iff` and
  `TauCeti.Quiver.Kronecker.titsForm_nonneg_iff`: the two thresholds `n ≤ 1` and `n ≤ 2`.
* `TauCeti.Quiver.Kronecker.titsForm_eq_zero_iff_exists_smul` and
  `TauCeti.Quiver.Kronecker.titsForm_eq_one_iff`: for the Kronecker quiver the radical of the Tits
  form is the line spanned by `(1, 1)`, and the vectors of Tits norm one are those whose two
  coordinates differ by one.

## References

This file supplies the “Kronecker quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, alongside the one-loop
quiver of `TauCeti.RepresentationTheory.Quiver.PathAlgebra`. See Derksen--Weyman, *An Introduction
to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the Representation Theory
of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver

/-- The generalized Kronecker quiver on an arrow type `A`: two vertices, a source `src` and a
target `tgt`, with one arrow `src ⟶ tgt` for each element of `A` and no other arrows. The classical
Kronecker quiver `• ⇉ •` is the case `A = Fin 2`, and the `A₂` quiver `• → •` is the case
`A = Fin 1`. -/
inductive Kronecker (A : Type v) : Type
  | /-- The source vertex, the tail of every arrow. -/ src : Kronecker A
  | /-- The target vertex, the head of every arrow. -/ tgt : Kronecker A

namespace Kronecker

variable {A : Type v}

instance : _root_.Quiver.{v} (Kronecker A) where
  Hom a b :=
    match a, b with
    | .src, .tgt => A
    | _, _ => PEmpty

/-! ### The two vertices -/

/-- The source and the target are distinct vertices. -/
theorem src_ne_tgt : (src : Kronecker A) ≠ tgt := by simp

-- The `deriving DecidableEq` handler would ask for `[DecidableEq A]`, which the two constructors
-- plainly do not need.
instance : DecidableEq (Kronecker A)
  | .src, .src => isTrue rfl
  | .src, .tgt => isFalse src_ne_tgt
  | .tgt, .src => isFalse src_ne_tgt.symm
  | .tgt, .tgt => isTrue rfl

instance : Fintype (Kronecker A) where
  elems := {(src : Kronecker A), tgt}
  complete x := by cases x <;> simp

/-- The vertex type is the pair `{src, tgt}`. -/
theorem univ_eq : (Finset.univ : Finset (Kronecker A)) = {(src : Kronecker A), tgt} := rfl

@[simp]
theorem card_eq_two : Fintype.card (Kronecker A) = 2 := by
  rw [Fintype.card, univ_eq, Finset.card_pair src_ne_tgt]

/-- A sum over the two vertices is the sum of its two values. -/
@[simp]
theorem sum_univ {M : Type w} [AddCommMonoid M] (f : Kronecker A → M) :
    ∑ v, f v = f src + f tgt := by
  rw [univ_eq, Finset.sum_pair src_ne_tgt]

/-- A function on the vertices vanishes exactly when both of its values do. -/
theorem eq_zero_iff {M : Type w} [Zero M] {f : Kronecker A → M} :
    f = 0 ↔ f src = 0 ∧ f tgt = 0 := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => funext fun v => ?_⟩
  cases v
  · exact h.1
  · exact h.2

/-! ### The arrows -/

/-- The arrow of the generalized Kronecker quiver indexed by an element of the arrow type. The
arrows from the source to the target are exactly the elements of the arrow type, and the
identification is definitional. -/
def arrow (a : A) : (src : Kronecker A) ⟶ tgt := a

instance : IsEmpty ((src : Kronecker A) ⟶ src) := inferInstanceAs (IsEmpty PEmpty)

instance : IsEmpty ((tgt : Kronecker A) ⟶ src) := inferInstanceAs (IsEmpty PEmpty)

instance : IsEmpty ((tgt : Kronecker A) ⟶ tgt) := inferInstanceAs (IsEmpty PEmpty)

/-- No arrow ends at the source vertex. -/
theorem isEmpty_hom_to_src (a : Kronecker A) : IsEmpty (a ⟶ (src : Kronecker A)) := by
  cases a <;> infer_instance

/-- No arrow starts at the target vertex. -/
theorem isEmpty_hom_from_tgt (b : Kronecker A) : IsEmpty ((tgt : Kronecker A) ⟶ b) := by
  cases b <;> infer_instance

instance instFiniteHom [Finite A] : ∀ a b : Kronecker A, Finite (a ⟶ b)
  | .src, .src => inferInstanceAs (Finite PEmpty)
  | .src, .tgt => inferInstanceAs (Finite A)
  | .tgt, .src => inferInstanceAs (Finite PEmpty)
  | .tgt, .tgt => inferInstanceAs (Finite PEmpty)

instance instFintypeHom [Fintype A] : ∀ a b : Kronecker A, Fintype (a ⟶ b)
  | .src, .src => Fintype.ofIsEmpty
  | .src, .tgt => inferInstanceAs (Fintype A)
  | .tgt, .src => Fintype.ofIsEmpty
  | .tgt, .tgt => Fintype.ofIsEmpty

@[simp]
theorem card_hom_src_tgt [Fintype A] :
    Fintype.card ((src : Kronecker A) ⟶ tgt) = Fintype.card A :=
  rfl

/-! ### The paths -/

/-- A path leaving the target vertex ends there: the target has no outgoing arrows. -/
theorem eq_tgt_of_path_from_tgt {b : Kronecker A} (p : Path (tgt : Kronecker A) b) : b = tgt := by
  induction p with
  | nil => rfl
  | cons _ e ih => subst ih; exact (isEmpty_hom_from_tgt _).elim e

/-- The only closed path at the source vertex is the trivial one. -/
theorem path_src_src_eq_nil (p : Path (src : Kronecker A) src) : p = Path.nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact (isEmpty_hom_to_src _).elim e

/-- The only closed path at the target vertex is the trivial one. -/
theorem path_tgt_tgt_eq_nil (p : Path (tgt : Kronecker A) tgt) : p = Path.nil := by
  cases p with
  | cons q e =>
      have h := eq_tgt_of_path_from_tgt q
      subst h
      exact (isEmpty_hom_from_tgt _).elim e
  | nil => rfl

/-- The generalized Kronecker quiver is acyclic: all of its arrows run the same way. -/
theorem isAcyclic : Quiver.IsAcyclic (Kronecker A) :=
  isAcyclic_def.mpr fun a p => by
    cases a
    · exact path_src_src_eq_nil p
    · exact path_tgt_tgt_eq_nil p

instance : Unique (Path (src : Kronecker A) src) where
  default := Path.nil
  uniq := path_src_src_eq_nil

instance : Unique (Path (tgt : Kronecker A) tgt) where
  default := Path.nil
  uniq := path_tgt_tgt_eq_nil

instance : IsEmpty (Path (tgt : Kronecker A) src) :=
  ⟨fun p => src_ne_tgt (eq_tgt_of_path_from_tgt p)⟩

/-- The length-one path traced by an arrow of the generalized Kronecker quiver. -/
def arrowPath (a : A) : Path (src : Kronecker A) tgt := (arrow a).toPath

/-- Distinct arrows trace distinct paths. -/
theorem arrowPath_injective : Function.Injective (arrowPath (A := A)) := by
  intro a b h
  simpa [arrowPath, arrow, Hom.toPath] using h

/-- Every path from the source to the target is a single arrow. -/
theorem arrowPath_surjective : Function.Surjective (arrowPath (A := A)) := by
  intro p
  cases p with
  | @cons b _ q e =>
      cases b with
      | src => exact ⟨e, by rw [path_src_src_eq_nil q]; rfl⟩
      | tgt => exact (isEmpty_hom_from_tgt _).elim e

/-- The paths from the source to the target of the generalized Kronecker quiver are its arrows. -/
@[expose] noncomputable def pathEquivArrow : Path (src : Kronecker A) tgt ≃ A :=
  (Equiv.ofBijective arrowPath ⟨arrowPath_injective, arrowPath_surjective⟩).symm

/-- The inverse of the classification sends an arrow to the path it traces; the two are the same
construction, so this holds definitionally. -/
@[simp]
theorem pathEquivArrow_symm_apply (a : A) : pathEquivArrow.symm a = arrowPath a := rfl

/-- The classification sends the path traced by an arrow back to that arrow. -/
@[simp]
theorem pathEquivArrow_arrowPath (a : A) : pathEquivArrow (arrowPath a) = a := by
  rw [← pathEquivArrow_symm_apply, Equiv.apply_symm_apply]

/-- Every path from the source to the target is traced by the arrow it classifies. -/
@[simp]
theorem arrowPath_pathEquivArrow (p : Path (src : Kronecker A) tgt) :
    arrowPath (pathEquivArrow p) = p := by
  rw [← pathEquivArrow_symm_apply, Equiv.symm_apply_apply]

noncomputable instance instFintypePath [Fintype A] : ∀ a b : Kronecker A, Fintype (Path a b)
  | .src, .src => Unique.fintype
  | .src, .tgt => Fintype.ofEquiv A pathEquivArrow.symm
  | .tgt, .src => Fintype.ofIsEmpty
  | .tgt, .tgt => Unique.fintype

@[simp]
theorem card_path_src_tgt [Fintype A] :
    Fintype.card (Path (src : Kronecker A) tgt) = Fintype.card A :=
  Fintype.card_congr pathEquivArrow

/-- The generalized Kronecker quiver on `n` arrows has `n + 2` paths: the two trivial paths and the
arrows themselves. -/
theorem card_totalPath [Fintype A] :
    Fintype.card (Quiver.TotalPath (Kronecker A)) = Fintype.card A + 2 := by
  have h : Fintype.card (Quiver.TotalPath (Kronecker A))
      = ∑ a : Kronecker A, ∑ b : Kronecker A, Fintype.card (Path a b) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun _ _ => Fintype.card_sigma
  rw [h]
  simp only [sum_univ, card_path_src_tgt, Fintype.card_unique, Fintype.card_eq_zero]
  omega

/-- The path algebra of the generalized Kronecker quiver on `n` arrows has dimension `n + 2`. For
the Kronecker quiver `• ⇉ •` itself this is `4`. -/
theorem finrank_pathAlgebra (k : Type w) [DivisionRing k] [Fintype A] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = Fintype.card A + 2 := by
  rw [TauCeti.finrank_pathAlgebra k (Kronecker A), card_totalPath]

/-- The path algebra of the generalized Kronecker quiver is finite-dimensional: unlike the one-loop
quiver, it is acyclic, so it has only finitely many paths. -/
theorem finiteDimensional_pathAlgebra (k : Type w) [DivisionRing k] [Finite A] :
    FiniteDimensional k (pathAlgebra k (Kronecker A)) :=
  finiteDimensional_pathAlgebra_of_isAcyclic k (Kronecker A) isAcyclic

/-! ### The Euler and Tits forms -/

section Forms

variable [Fintype A]

/-- The Euler form of the generalized Kronecker quiver, in the coordinates of its two vertices. -/
@[simp]
theorem eulerForm_apply (d e : Kronecker A → ℤ) :
    eulerForm (Kronecker A) d e =
      d src * e src + d tgt * e tgt - (Fintype.card A : ℤ) * (d src * e tgt) := by
  rw [eulerForm_eq_sum_card]
  simp only [sum_univ, card_hom_src_tgt, Fintype.card_eq_zero, Nat.cast_zero]
  ring

/-- The Tits form of the generalized Kronecker quiver on `n` arrows is
`q(d) = d₁ ^ 2 + d₂ ^ 2 - n * d₁ * d₂`. -/
-- Deliberately not `@[simp]`: `TauCeti.titsForm_def` is already `simp`, so `simp` rewrites
-- `titsForm` to `eulerForm` and finishes with `eulerForm_apply` below; tagging this lemma too
-- would only add one that never fires.
theorem titsForm_apply (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d =
      d src ^ 2 + d tgt ^ 2 - (Fintype.card A : ℤ) * (d src * d tgt) := by
  rw [titsForm_def, eulerForm_apply]
  ring

/-- The Tits form on the constant dimension vector `(1, 1)` is `2 - n`. This single value decides
both thresholds below. -/
private theorem titsForm_one : titsForm (Kronecker A) 1 = 2 - (Fintype.card A : ℤ) := by
  rw [titsForm_apply, Pi.one_apply, Pi.one_apply]
  ring

/-- Doubling the Tits form splits it into the two pieces `(2 - n) * (d₁ ^ 2 + d₂ ^ 2)` and
`n * (d₁ - d₂) ^ 2`, both nonnegative as soon as `n ≤ 2`. -/
private theorem two_mul_titsForm (d : Kronecker A → ℤ) :
    2 * titsForm (Kronecker A) d =
      (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2)
        + (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 := by
  rw [titsForm_apply]
  ring

/-- With at most two arrows the Tits form is positive semidefinite. -/
theorem titsForm_nonneg (h : Fintype.card A ≤ 2) (d : Kronecker A → ℤ) :
    0 ≤ titsForm (Kronecker A) d := by
  have hn : (Fintype.card A : ℤ) ≤ 2 := by exact_mod_cast h
  have h₁ : 0 ≤ (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have h₂ : 0 ≤ (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 :=
    mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
  have h₃ := two_mul_titsForm (A := A) d
  linarith

/-- The Tits form of the generalized Kronecker quiver is positive semidefinite exactly when there
are at most two arrows. Two arrows is the Kronecker quiver `• ⇉ •`, of affine type `Ã₁`, the
boundary case of Gabriel's theorem; three or more arrows makes the form indefinite. -/
theorem titsForm_nonneg_iff :
    (∀ d, 0 ≤ titsForm (Kronecker A) d) ↔ Fintype.card A ≤ 2 := by
  refine ⟨fun h => ?_, fun h => titsForm_nonneg h⟩
  have h1 := h 1
  rw [titsForm_one] at h1
  omega

/-- With at most one arrow the Tits form is positive definite: these are the quivers of type
`A₁ ⊔ A₁` (no arrow) and `A₂` (one arrow). -/
theorem titsForm_posDef (h : Fintype.card A ≤ 1) : (titsForm (Kronecker A)).PosDef := by
  intro d hd
  have hn : (Fintype.card A : ℤ) ≤ 1 := by exact_mod_cast h
  have hpos : 0 < d src ^ 2 + d tgt ^ 2 := by
    rcases eq_or_ne (d src) 0 with hs | hs
    · have ht : d tgt ≠ 0 := fun ht => hd (eq_zero_iff.mpr ⟨hs, ht⟩)
      have := sq_pos_of_ne_zero ht
      have := sq_nonneg (d src)
      linarith
    · have := sq_pos_of_ne_zero hs
      have := sq_nonneg (d tgt)
      linarith
  have h₁ : d src ^ 2 + d tgt ^ 2
      ≤ (2 - (Fintype.card A : ℤ)) * (d src ^ 2 + d tgt ^ 2) := by nlinarith
  have h₂ : 0 ≤ (Fintype.card A : ℤ) * (d src - d tgt) ^ 2 :=
    mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
  have h₃ := two_mul_titsForm (A := A) d
  linarith

/-- The Tits form of the generalized Kronecker quiver is positive definite exactly when there is at
most one arrow: no arrow gives the disconnected Dynkin quiver `A₁ ⊔ A₁`, and one arrow gives `A₂`.
Every other generalized Kronecker quiver falls outside the Dynkin classification. -/
theorem titsForm_posDef_iff :
    (titsForm (Kronecker A)).PosDef ↔ Fintype.card A ≤ 1 := by
  refine ⟨fun h => ?_, titsForm_posDef⟩
  have h1 : (0 : ℤ) < titsForm (Kronecker A) 1 :=
    h 1 fun hc => one_ne_zero (congrFun hc src)
  rw [titsForm_one] at h1
  omega

end Forms

/-! ### The Kronecker quiver itself -/

section Two

variable [Fintype A] (h : Fintype.card A = 2)
include h

/-- The Tits form of the Kronecker quiver is the perfect square `(d₁ - d₂) ^ 2`. -/
theorem titsForm_eq_sq (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = (d src - d tgt) ^ 2 := by
  rw [titsForm_apply, h]
  push_cast
  ring

/-- The Tits form of the Kronecker quiver vanishes exactly on the diagonal. -/
theorem titsForm_eq_zero_iff (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 0 ↔ d src = d tgt := by
  rw [titsForm_eq_sq h, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

/-- The radical of the Tits form of the Kronecker quiver is the line spanned by the constant vector
`(1, 1)`: the null root of the affine root system `Ã₁`. -/
theorem titsForm_eq_zero_iff_exists_smul (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 0 ↔ ∃ c : ℤ, d = c • 1 := by
  rw [titsForm_eq_zero_iff h]
  refine ⟨fun hd => ⟨d src, funext fun v => ?_⟩, ?_⟩
  · cases v
    · simp
    · simp [hd]
  · rintro ⟨c, rfl⟩
    simp

/-- For the Kronecker quiver the integer vectors of Tits norm one -- the real roots of the affine
root system `Ã₁`, positive and negative alike -- are exactly those whose two coordinates differ by
one, that is `(m, m + 1)` and `(m + 1, m)`. -/
theorem titsForm_eq_one_iff (d : Kronecker A → ℤ) :
    titsForm (Kronecker A) d = 1 ↔ d src = d tgt + 1 ∨ d tgt = d src + 1 := by
  rw [titsForm_eq_sq h, sq_eq_one_iff]
  omega

/-- The Tits form of the Kronecker quiver is not positive definite: it is isotropic on the nonzero
vector `(1, 1)`. Together with `TauCeti.Quiver.Kronecker.titsForm_nonneg` this says it is positive
semidefinite but degenerate, which is what places the Kronecker quiver on the boundary of Gabriel's
dichotomy. -/
theorem not_titsForm_posDef : ¬ (titsForm (Kronecker A)).PosDef := by
  rw [titsForm_posDef_iff, h]
  omega

/-- The path algebra of the Kronecker quiver is four-dimensional: two trivial paths and two
arrows. -/
theorem finrank_pathAlgebra_eq_four (k : Type w) [DivisionRing k] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = 4 := by
  rw [finrank_pathAlgebra k, h]

end Two

end Kronecker

end Quiver

end TauCeti
