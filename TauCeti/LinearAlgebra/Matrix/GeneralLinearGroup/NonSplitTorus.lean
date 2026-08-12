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
-- Non-public: `Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap`,
-- `Algebra.norm_ne_zero_iff`, `Module.natCard_eq_pow_finrank` and `Nat.card_units` are used only
-- inside proofs, so downstream importers do not pay for them.
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The non-split torus of `GL₂`

Let `E/F` be a field extension of degree `2`. Choosing an `F`-basis of `E` presents multiplication
by an element of `E` as a `2 × 2` matrix over `F`, and multiplication by a *nonzero* element as an
element of `GL (Fin 2) F`. The image of `Eˣ` is the **non-split torus**
`TauCeti.GL2NonSplitTorus F E hE`, an abelian subgroup of `GL₂(F)` of order `q² - 1` when `F` has
`q` elements. It is the torus the cuspidal (discrete series) representations of `GL₂(𝔽_q)` are
parametrized by: a character of `Eˣ` in general position determines one of them through the
Deligne–Lusztig construction, which is *not* ordinary induction (the induced representation
`Ind_{Eˣ}^{GL₂(𝔽_q)}` has dimension `q(q - 1)`, while a cuspidal representation has dimension
`q - 1`). This is the elliptic counterpart of the *split* torus of diagonal matrices, whose
characters give the principal series by ordinary induction from the Borel subgroup.

The word *torus* is the algebraic-group one only when `E/F` is separable, which over a finite
field — the setting of the roadmap target — it always is. Degree `2` alone also admits a purely
inseparable `E/F` (characteristic `2` only), where the *algebra* `E ⊗[F] F̄` is the nonreduced
`F̄[X]/(X²)` rather than `F̄ × F̄`. The image of `Eˣ` is then not a torus: after base change to
`F̄` it is the unit group of `F̄[X]/(X²)`, which is `Gₘ × Gₐ` — still smooth and reduced as a
group, but with a nontrivial unipotent part — and its non-scalar elements are not semisimple.
Everything stated below, non-splitness included, is true in that case too: no proof here uses
separability, so no statement assumes it.

"Non-split" is the assertion that, away from the scalars, the torus is not conjugate into the Borel
subgroup: `TauCeti.GL2NonSplitTorus.conj_notMem_gl2Borel` says that if `x : Eˣ` does not lie in `F`
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
* `TauCeti.GL2NonSplitTorus.unitsEquiv`: the resulting multiplicative equivalence `Eˣ ≃*` the
  torus.

## Main results

* `TauCeti.GL2NonSplitTorus.natCard_eq`: the torus has `q² - 1` elements over a finite field with
  `q` elements.
* `TauCeti.GL2NonSplitTorus.conj_notMem_gl2Borel`: an element of the torus not coming from `F` has
  no conjugate in the Borel subgroup, and
  `TauCeti.GL2NonSplitTorus.exists_forall_conj_notMem_gl2Borel`: such an element exists, so the
  torus is not conjugate into the Borel subgroup. What these contradict is
  `TauCeti.GL2Borel.exists_det_sub_algebraMap_eq_zero`, that a matrix with an upper-triangular
  conjugate has an eigenvalue in the base ring.

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

variable (F E) in
/-- A chosen `F`-basis of a degree-`2` extension `E/F`, indexed by `Fin 2`. The non-split torus is
the image of `Eˣ` under the matrix representation in this basis; another choice of basis conjugates
it. -/
noncomputable def nonSplitTorusBasis (hE : Module.finrank F E = 2) :
    Module.Basis (Fin 2) F E :=
  have := Module.finite_of_finrank_eq_succ (n := 1) hE
  Module.finBasisOfFinrankEq F E hE

variable (F E) in
/-- **The embedding of the non-split torus**: a nonzero element of a degree-`2` extension `E/F`
acts on `E` by multiplication, hence, in the basis `TauCeti.nonSplitTorusBasis`, as an element of
`GL (Fin 2) F`. -/
noncomputable def GL2NonSplitTorusHom (hE : Module.finrank F E = 2) : Eˣ →* GL (Fin 2) F :=
  unitsLeftMulMatrix (nonSplitTorusBasis F E hE)

variable (F E) in
/-- **The non-split (elliptic) torus** of `GL₂(F)` attached to a degree-`2` extension `E/F`: the
image of `Eˣ` under multiplication on `E`, read in the basis `TauCeti.nonSplitTorusBasis`. It is a
torus in the algebraic-group sense when `E/F` is separable, in particular whenever `F` is finite;
for a purely inseparable `E/F` it is the same subgroup, still non-split in the sense proved below,
but not an algebraic torus (see the module docstring). -/
noncomputable def GL2NonSplitTorus (hE : Module.finrank F E = 2) : Subgroup (GL (Fin 2) F) :=
  (GL2NonSplitTorusHom F E hE).range

namespace GL2NonSplitTorus

variable (hE : Module.finrank F E = 2)

/-- Membership in the non-split torus: a matrix lies in it exactly when it is left multiplication
by a unit of `E`. -/
theorem mem_iff {g : GL (Fin 2) F} :
    g ∈ GL2NonSplitTorus F E hE ↔ ∃ x : Eˣ, GL2NonSplitTorusHom F E hE x = g :=
  MonoidHom.mem_range

/-- The matrix underlying `GL2NonSplitTorusHom F E hE x` is multiplication by `x` in the basis
`TauCeti.nonSplitTorusBasis`. -/
@[simp, grind =]
theorem coe_gl2NonSplitTorusHom (x : Eˣ) :
    (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix (nonSplitTorusBasis F E hE) (x : E) :=
  coe_unitsLeftMulMatrix (nonSplitTorusBasis F E hE) x

/-- Distinct elements of `Eˣ` give distinct matrices. -/
theorem gl2NonSplitTorusHom_injective : Function.Injective (GL2NonSplitTorusHom F E hE) :=
  unitsLeftMulMatrix_injective _

/-- **The non-split torus is a copy of `Eˣ`**: the embedding `TauCeti.GL2NonSplitTorusHom` is
injective, so it corestricts to a multiplicative equivalence from `Eˣ` onto the torus. This is what
transports a character of `Eˣ` to a character of the torus. -/
noncomputable def unitsEquiv : Eˣ ≃* GL2NonSplitTorus F E hE :=
  MonoidHom.ofInjective (gl2NonSplitTorusHom_injective hE)

/-- `TauCeti.GL2NonSplitTorus.unitsEquiv` is `TauCeti.GL2NonSplitTorusHom` on the nose. -/
@[simp, grind =]
theorem coe_unitsEquiv_apply (x : Eˣ) :
    (unitsEquiv hE x : GL (Fin 2) F) = GL2NonSplitTorusHom F E hE x :=
  (rfl)

/-- The torus is abelian: it is the image of the commutative group `Eˣ`. -/
instance : IsMulCommutative (GL2NonSplitTorus F E hE) :=
  Subgroup.range_isMulCommutative (GL2NonSplitTorusHom F E hE)

/-- The determinant of a torus element is the norm of the field element it comes from. -/
theorem val_det_gl2NonSplitTorusHom (x : Eˣ) :
    (Matrix.GeneralLinearGroup.det (GL2NonSplitTorusHom F E hE x) : F) = Algebra.norm F (x : E) :=
  val_det_unitsLeftMulMatrix _ x

/-- The trace of a torus element is the trace of the field element it comes from. -/
theorem trace_gl2NonSplitTorusHom (x : Eˣ) :
    Matrix.trace (GL2NonSplitTorusHom F E hE x : Matrix (Fin 2) (Fin 2) F) =
      Algebra.trace F E (x : E) :=
  trace_unitsLeftMulMatrix _ x

/-- A unit of `F` is sent to the corresponding scalar matrix. -/
@[simp, grind =]
theorem gl2NonSplitTorusHom_map_algebraMap (a : Fˣ) :
    GL2NonSplitTorusHom F E hE (Units.map (algebraMap F E : F →* E) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a :=
  unitsLeftMulMatrix_map_algebraMap _ a

/-- The scalar matrices lie in the non-split torus: it contains the centre of `GL₂(F)`. -/
theorem scalar_mem (a : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ GL2NonSplitTorus F E hE :=
  ⟨_, gl2NonSplitTorusHom_map_algebraMap hE a⟩

/-- **The order of the non-split torus**: it has one element for each nonzero element of `E`, so
over a field with `q` elements it has `q² - 1` of them. (Over an infinite `F` both sides are `0`,
the `Nat.card` of an infinite type.) -/
theorem natCard_eq : Nat.card (GL2NonSplitTorus F E hE) = Nat.card F ^ 2 - 1 := by
  have := Module.finite_of_finrank_eq_succ (n := 1) hE
  rw [← Nat.card_congr (unitsEquiv hE).toEquiv, Nat.card_units,
    Module.natCard_eq_pow_finrank (K := F) (V := E), hE]

/-- The key computation behind non-splitness: for `x : E` outside `F`, the matrix of multiplication
by `x` has no eigenvalue `a : F`. -/
theorem det_sub_algebraMap_ne_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) (a : F) :
    (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE) x -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det ≠ 0 := by
  have := Module.finite_of_finrank_eq_succ (n := 1) hE
  have hxa : x - algebraMap F E a ≠ 0 := fun h => hx ⟨a, (sub_eq_zero.mp h).symm⟩
  rw [← (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes a, ← map_sub,
    ← Algebra.norm_eq_matrix_det]
  exact Algebra.norm_ne_zero_iff.mpr hxa

/-- **The torus is non-split**: if `x : Eˣ` does not come from `F`, then no conjugate of the
corresponding matrix is upper triangular. Equivalently, that matrix has no eigenvalue in `F`, which
over a finite field is what makes its conjugacy class elliptic. -/
theorem conj_notMem_gl2Borel {x : Eˣ} (hx : (x : E) ∉ Set.range (algebraMap F E))
    (g : GL (Fin 2) F) :
    g * GL2NonSplitTorusHom F E hE x * g⁻¹ ∉ GL2Borel F := fun hmem => by
  obtain ⟨a, ha⟩ := GL2Borel.exists_det_sub_algebraMap_eq_zero hmem
  rw [coe_gl2NonSplitTorusHom] at ha
  exact det_sub_algebraMap_ne_zero hE hx a ha

/-- **The non-split torus is not conjugate into the Borel subgroup**: it contains an element no
conjugate of which is upper triangular. This is exactly what distinguishes it from the split torus
of diagonal matrices, which lies in the Borel subgroup outright, and it is why the cuspidal
representations attached to it are absent from every principal series. -/
theorem exists_forall_conj_notMem_gl2Borel :
    ∃ u ∈ GL2NonSplitTorus F E hE, ∀ g : GL (Fin 2) F, g * u * g⁻¹ ∉ GL2Borel F := by
  have : Algebra.IsQuadraticExtension F E := ⟨hE⟩
  obtain ⟨x, hx⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap F E
  have hx0 : x ≠ 0 := fun h => hx ⟨0, by rw [map_zero, h]⟩
  exact ⟨GL2NonSplitTorusHom F E hE (Units.mk0 x hx0), ⟨_, rfl⟩, conj_notMem_gl2Borel hE hx⟩

end GL2NonSplitTorus

end TauCeti
