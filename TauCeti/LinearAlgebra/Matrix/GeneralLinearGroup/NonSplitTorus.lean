/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.unitsLeftMulMatrix` is the body of `TauCeti.GL2NonSplitTorusHom`, so it must be
-- imported publicly.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LeftMulMatrix
-- `TauCeti.GL2Borel` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- `Module.finBasisOfFinrankEq` is the body of `TauCeti.nonSplitTorusBasis`.
public import Mathlib.LinearAlgebra.Dimension.Free
-- Non-public: `Algebra.norm_ne_zero_iff`, `Module.natCard_eq_pow_finrank` and `Nat.card_units` are
-- used only inside proofs, so downstream importers do not pay for them.
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The non-split torus of `GL₂`

Let `E/F` be a field extension of degree `2`. Choosing an `F`-basis of `E` presents multiplication
by an element of `E` as a `2 × 2` matrix over `F`, and multiplication by a *nonzero* element as an
element of `GL (Fin 2) F`. The image of `Eˣ` is the **non-split torus**
`TauCeti.GL2NonSplitTorus F E hE`, an abelian subgroup of `GL₂(F)` of order `q² - 1` when `F` has
`q` elements. It is the source of the cuspidal (discrete series) representations of `GL₂(𝔽_q)`,
obtained by inducing its characters, exactly as the *split* torus of diagonal matrices is the
source of the principal series.

"Non-split" is the assertion that, away from the scalars, the torus is not conjugate into the Borel
subgroup: `TauCeti.GL2NonSplitTorus.conj_notMem_GL2Borel` says that if `x : Eˣ` does not lie in `F`
then no conjugate of its matrix is upper triangular. Equivalently the matrix has no eigenvalue in
`F` — over a finite field its eigenvalues are a conjugate pair in `E ∖ F` — which is what makes
these the **elliptic** conjugacy classes of `GL₂(𝔽_q)`. The proof is that the determinant of
`x - a` is the norm `N_{E/F}(x - a)`, which is nonzero because `x - a` is.

The construction depends on the chosen basis `TauCeti.nonSplitTorusBasis`; a different choice
conjugates the subgroup, so the statements that are not conjugation-invariant are stated for this
choice, following the convention of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`.

## Main definitions

* `TauCeti.nonSplitTorusBasis`: a chosen `F`-basis of `E`, indexed by `Fin 2`.
* `TauCeti.GL2NonSplitTorusHom`: the embedding `Eˣ ↪ GL (Fin 2) F` by left multiplication.
* `TauCeti.GL2NonSplitTorus`: its range, the non-split torus.

## Main results

* `TauCeti.GL2NonSplitTorus.natCard_eq`: the torus has `q² - 1` elements over a finite field with
  `q` elements.
* `TauCeti.GL2NonSplitTorus.conj_notMem_GL2Borel`: an element of the torus not coming from `F` has
  no conjugate in the Borel subgroup, and
  `TauCeti.GL2NonSplitTorus.exists_forall_conj_notMem_GL2Borel`: such an element exists, so the
  torus is not conjugate into the Borel subgroup.
* `TauCeti.GL2Borel.exists_det_sub_algebraMap_eq_zero`: a matrix with an upper-triangular conjugate
  has an eigenvalue in the base ring; this is what non-splitness contradicts.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 5.2.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- A degree-`2` extension is finite-dimensional: the `Module.finrank` of a module that is not
finite is `0`, not `2`. -/
theorem module_finite_of_finrank_eq_two (hE : Module.finrank F E = 2) : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [hE]; norm_num)

/-- An extension of degree other than `1` has a unit outside the base field: were every element of
`E` a scalar, `algebraMap F E` would be bijective and the degree would be `1`. -/
theorem exists_units_notMem_range_algebraMap (h : Module.finrank F E ≠ 1) :
    ∃ x : Eˣ, (x : E) ∉ Set.range (algebraMap F E) := by
  by_contra hcon
  refine h ?_
  have hsurj : Function.Surjective (algebraMap F E) := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, map_zero _⟩
    · exact not_not.mp (not_exists.mp hcon (Units.mk0 y hy))
  have e : F ≃ₗ[F] E :=
    LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_self]

variable (F E) in
/-- A chosen `F`-basis of a degree-`2` extension `E/F`, indexed by `Fin 2`. The non-split torus is
the image of `Eˣ` under the matrix representation in this basis; another choice of basis conjugates
it. -/
noncomputable def nonSplitTorusBasis (hE : Module.finrank F E = 2) :
    Module.Basis (Fin 2) F E :=
  have := module_finite_of_finrank_eq_two hE
  Module.finBasisOfFinrankEq F E hE

variable (F E) in
/-- **The embedding of the non-split torus**: a nonzero element of a degree-`2` extension `E/F`
acts on `E` by multiplication, hence, in the basis `TauCeti.nonSplitTorusBasis`, as an element of
`GL (Fin 2) F`. -/
noncomputable def GL2NonSplitTorusHom (hE : Module.finrank F E = 2) : Eˣ →* GL (Fin 2) F :=
  unitsLeftMulMatrix (nonSplitTorusBasis F E hE)

variable (F E) in
/-- **The non-split (elliptic) torus** of `GL₂(F)` attached to a degree-`2` extension `E/F`: the
image of `Eˣ` under multiplication on `E`, read in the basis `TauCeti.nonSplitTorusBasis`. -/
noncomputable def GL2NonSplitTorus (hE : Module.finrank F E = 2) : Subgroup (GL (Fin 2) F) :=
  (GL2NonSplitTorusHom F E hE).range

namespace GL2Borel

/-- If some conjugate of `u : GL (Fin 2) R` is upper triangular then `u` has an eigenvalue in the
base ring: writing `a` for the upper-left entry of that conjugate, `det (u - a) = 0`. Conjugation
leaves the determinant alone and `a` clears the whole first column of the conjugate. This is the
eigenvalue that a non-split torus element has to be shown not to have. -/
theorem exists_det_sub_algebraMap_eq_zero {R : Type*} [CommRing R] {u g : GL (Fin 2) R}
    (h : g * u * g⁻¹ ∈ GL2Borel R) :
    ∃ a : R,
      ((u : Matrix (Fin 2) (Fin 2) R) - algebraMap R (Matrix (Fin 2) (Fin 2) R) a).det = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 2) (Fin 2) R,
      ((g * u * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = N := ⟨_, rfl⟩
  refine ⟨N 0 0, ?_⟩
  -- A scalar matrix is central, so conjugating `u - a` conjugates `u` and leaves `a` alone.
  have hgc : (g : Matrix (Fin 2) (Fin 2) R) * algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) := by
    rw [← Algebra.commutes (N 0 0) (g : Matrix (Fin 2) (Fin 2) R), mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]
  have key : (g : Matrix (Fin 2) (Fin 2) R) *
      ((u : Matrix (Fin 2) (Fin 2) R) - algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0)) *
      ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      N - algebraMap R (Matrix (Fin 2) (Fin 2) R) (N 0 0) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hgc, ← hN, Units.val_mul, Units.val_mul]
  have h10 : N 1 0 = 0 := by rw [← hN]; exact mem_iff.mp h
  rw [← Matrix.det_units_conj g, key, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.algebraMap_matrix_apply, h10]

end GL2Borel

namespace GL2NonSplitTorus

variable (hE : Module.finrank F E = 2)

@[simp]
theorem coe_GL2NonSplitTorusHom (x : Eˣ) :
    (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix (nonSplitTorusBasis F E hE) (x : E) :=
  coe_unitsLeftMulMatrix (nonSplitTorusBasis F E hE) x

/-- Distinct elements of `Eˣ` give distinct matrices. -/
theorem GL2NonSplitTorusHom_injective : Function.Injective (GL2NonSplitTorusHom F E hE) :=
  unitsLeftMulMatrix_injective _

@[simp]
theorem mem_iff {g : GL (Fin 2) F} :
    g ∈ GL2NonSplitTorus F E hE ↔ ∃ x : Eˣ, GL2NonSplitTorusHom F E hE x = g :=
  Iff.rfl

theorem apply_mem (x : Eˣ) : GL2NonSplitTorusHom F E hE x ∈ GL2NonSplitTorus F E hE :=
  ⟨x, rfl⟩

/-- The torus is abelian: it is the image of the commutative group `Eˣ`. -/
instance : IsMulCommutative (GL2NonSplitTorus F E hE) :=
  isMulCommutative_iff.mpr fun a b => Subtype.ext <| by
    obtain ⟨x, hx⟩ := (mem_iff hE).mp a.2
    obtain ⟨y, hy⟩ := (mem_iff hE).mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

/-- The determinant of a torus element is the norm of the field element it comes from. -/
theorem val_det_GL2NonSplitTorusHom (x : Eˣ) :
    (Matrix.GeneralLinearGroup.det (GL2NonSplitTorusHom F E hE x) : F) = Algebra.norm F (x : E) :=
  val_det_unitsLeftMulMatrix _ x

/-- The trace of a torus element is the trace of the field element it comes from. -/
theorem trace_GL2NonSplitTorusHom (x : Eˣ) :
    Matrix.trace (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) =
      Algebra.trace F E (x : E) :=
  trace_unitsLeftMulMatrix _ x

/-- The scalar matrices lie in the non-split torus: it contains the centre of `GL₂(F)`. -/
theorem scalar_mem (a : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ GL2NonSplitTorus F E hE :=
  ⟨Units.map (algebraMap F E : F →* E) a, unitsLeftMulMatrix_map_algebraMap _ a⟩

/-- **The order of the non-split torus**: it has one element for each nonzero element of `E`, so
over a field with `q` elements it has `q² - 1` of them. (Over an infinite `F` both sides are `0`,
the `Nat.card` of an infinite type.) -/
theorem natCard_eq : Nat.card (GL2NonSplitTorus F E hE) = Nat.card F ^ 2 - 1 := by
  have := module_finite_of_finrank_eq_two hE
  rw [GL2NonSplitTorus,
    ← Nat.card_congr (MonoidHom.ofInjective (GL2NonSplitTorusHom_injective hE)).toEquiv,
    Nat.card_units, Module.natCard_eq_pow_finrank (K := F) (V := E), hE]

/-- The key computation behind non-splitness: for `x : E` outside `F`, the matrix of multiplication
by `x` has no eigenvalue `a : F`, because `det (x - a) = N_{E/F}(x - a) ≠ 0`. -/
theorem det_sub_algebraMap_ne_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) (a : F) :
    (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE) x -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det ≠ 0 := by
  have := module_finite_of_finrank_eq_two hE
  have hxa : x - algebraMap F E a ≠ 0 := fun h => hx ⟨a, (sub_eq_zero.mp h).symm⟩
  rw [← (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes a, ← map_sub,
    ← Algebra.norm_eq_matrix_det]
  exact Algebra.norm_ne_zero_iff.mpr hxa

/-- **The torus is non-split**: if `x : Eˣ` does not come from `F`, then no conjugate of the
corresponding matrix is upper triangular. Equivalently, that matrix has no eigenvalue in `F`, which
is what makes its conjugacy class elliptic. -/
theorem conj_notMem_GL2Borel {x : Eˣ} (hx : (x : E) ∉ Set.range (algebraMap F E))
    (g : GL (Fin 2) F) :
    g * GL2NonSplitTorusHom F E hE x * g⁻¹ ∉ GL2Borel F := fun hmem => by
  obtain ⟨a, ha⟩ := GL2Borel.exists_det_sub_algebraMap_eq_zero hmem
  rw [coe_GL2NonSplitTorusHom] at ha
  exact det_sub_algebraMap_ne_zero hE hx a ha

/-- **The non-split torus is not conjugate into the Borel subgroup**: it contains an element no
conjugate of which is upper triangular. This is exactly what distinguishes it from the split torus
of diagonal matrices, which lies in the Borel subgroup outright, and it is why the cuspidal
representations induced from it are absent from every principal series. -/
theorem exists_forall_conj_notMem_GL2Borel :
    ∃ u ∈ GL2NonSplitTorus F E hE, ∀ g : GL (Fin 2) F, g * u * g⁻¹ ∉ GL2Borel F := by
  obtain ⟨x, hx⟩ := exists_units_notMem_range_algebraMap (F := F) (E := E) (by rw [hE]; norm_num)
  exact ⟨GL2NonSplitTorusHom F E hE x, apply_mem hE x, conj_notMem_GL2Borel hE hx⟩

end GL2NonSplitTorus

end TauCeti
