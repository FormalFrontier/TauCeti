/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Inversion
public import TauCeti.RepresentationTheory.Compact.ClassFunctionLp
public import TauCeti.RepresentationTheory.Compact.PeterWeyl

/-!
# The irreducible characters are a Hilbert basis of the class functions

Peter-Weyl (`TauCeti/RepresentationTheory/Compact/PeterWeyl.lean`) makes the normalized matrix
coefficients of a skeleton of the unitary dual a Hilbert basis of `L²(G)`. This file cuts that
basis down to the closed subspace `TauCeti.classFunctionLp` of class functions and finds the
irreducible **characters** there: they are a Hilbert basis of the class functions, the
compact-group form of "the irreducible characters are a basis of the class functions".

## The argument

Fix a finite-dimensional irreducible unitary continuous `π` and a class function `f`. The pairing
`A v w = ⟪(π)_{v,w}, f⟫` is linear in `v` and conjugate linear in `w`, so it is `⟪w, T v⟫` for a
unique endomorphism `T` of the carrier. Conjugation-invariance of `f` says exactly that `A` is
unchanged when both vectors are moved by `π h`
(`TauCeti.ContRepresentation.inner_matrixCoeffLp_map_map`), and that makes `T` an intertwiner.
Schur's lemma over an algebraically closed field collapses `T` to a scalar, so

`⟪(π)_{v,w}, f⟫ = c · ⟪w, v⟫`

(`TauCeti.ContRepresentation.exists_forall_inner_matrixCoeffLp_eq`): a class function sees only
the *trace* direction of each Peter-Weyl block. Taking `v = w` over an orthonormal basis and
summing identifies `c · dim V` with the pairing of `f` against the sum of the diagonal matrix
coefficients, which is the **conjugate** of the character, not the character. Inversion
`g ↦ g⁻¹` exchanges the two (`TauCeti.ContRepresentation.invLpₗᵢ_characterLp`), and it is an
isometry preserving the class functions, so running the argument on the inverse-translate of `f`
is what turns orthogonality to every character into the vanishing of every Peter-Weyl coefficient.

## Main definitions

* `TauCeti.characterFamily`: the characters of a family of models, as elements of the class
  functions.
* `TauCeti.characterBasis`: **the Hilbert basis of `classFunctionLp` given by the irreducible
  characters**, for a skeleton of the unitary dual.
* `TauCeti.stdCharacterBasis`: the same on the chosen representatives of `TauCeti.IrrepClass`, so
  that no skeleton has to be supplied.

## Main statements

* `TauCeti.ContRepresentation.exists_forall_inner_matrixCoeffLp_eq`: against a class function, the
  matrix coefficients of an irreducible pair off into a single scalar.
* `TauCeti.eq_zero_of_forall_inner_characterLp_eq_zero`: **class-function completeness.** A class
  function orthogonal to every irreducible character is zero.
* `TauCeti.coe_characterBasis`, `TauCeti.coe_stdCharacterBasis`: the basis is the characters
  themselves.

## References

This is the item "characters span the class functions" of Layer 6 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose first half — the closed subspace of class functions and the membership of the characters in
it — is `TauCeti/RepresentationTheory/Compact/ClassFunctionLp.lean`. The `[Finite G]` shadow of the
statement is that the irreducible characters of a finite group are a basis of its class functions.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Scalar

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable {π : ContRepresentation 𝕜 G V} (hπ : Continuous π)

omit [FiniteDimensional 𝕜 V] in
/-- **A class function does not see a simultaneous move of the two defining vectors.**  Moving both
vectors of a matrix coefficient by `π h` reparametrizes it by the conjugation `g ↦ h⁻¹ * g * h`,
which fixes a class function and preserves the inner product. -/
theorem inner_matrixCoeffLp_map_map (hunitary : IsUnitary π) {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G)) (h : G) (v w : V) :
    ⟪matrixCoeffLp π hπ (π h v) (π h w), f⟫_𝕜 = ⟪matrixCoeffLp π hπ v w, f⟫_𝕜 := by
  calc ⟪matrixCoeffLp π hπ (π h v) (π h w), f⟫_𝕜
      = ⟪conjLpₗᵢ 𝕜 h⁻¹ (matrixCoeffLp π hπ v w), conjLpₗᵢ 𝕜 h⁻¹ f⟫_𝕜 := by
        rw [matrixCoeffLp_map_map π hπ hunitary, conjLpₗᵢ_apply_of_mem_classFunctionLp hf]
    _ = ⟪matrixCoeffLp π hπ v w, f⟫_𝕜 :=
      (conjLpₗᵢ (E := 𝕜) (p := 2) (μ := haarProb G) 𝕜 h⁻¹).toLinearIsometry.inner_map_map _ _

omit [FiniteDimensional 𝕜 V] in
/-- **An endomorphism that represents the pairing against a class function is an intertwiner.**
If `⟪w, T v⟫ = ⟪(π)_{v,w}, f⟫` for all `v, w` and `f` is a class function, then `T` intertwines `π`
with itself. -/
private lemma isIntertwiningMap_of_inner_matrixCoeffLp_eq (hunitary : IsUnitary π)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G)) (T : V →ₗ[𝕜] V)
    (hT : ∀ v w : V, ⟪w, T v⟫_𝕜 = ⟪matrixCoeffLp π hπ v w, f⟫_𝕜) :
    π.toRepresentation.IsIntertwiningMap π.toRepresentation T := by
  refine ⟨fun g v ↦ ext_inner_left 𝕜 fun u ↦ ?_⟩
  -- Conjugation invariance of `f` is what moves `g` across the coefficient.
  have hu : π g (π g⁻¹ u) = u := Representation.self_inv_apply π.toRepresentation g u
  calc ⟪u, T (π g v)⟫_𝕜
      = ⟪π g (π g⁻¹ u), T (π g v)⟫_𝕜 := by rw [hu]
    _ = ⟪matrixCoeffLp π hπ (π g v) (π g (π g⁻¹ u)), f⟫_𝕜 := hT _ _
    _ = ⟪matrixCoeffLp π hπ v (π g⁻¹ u), f⟫_𝕜 :=
        inner_matrixCoeffLp_map_map hπ hunitary hf g v (π g⁻¹ u)
    _ = ⟪π g⁻¹ u, T v⟫_𝕜 := (hT _ _).symm
    _ = ⟪π g (π g⁻¹ u), π g (T v)⟫_𝕜 := (hunitary.inner_map_map g _ _).symm
    _ = ⟪u, π g (T v)⟫_𝕜 := by rw [hu]

/-- **Against a class function, the matrix coefficients of an irreducible collapse to one scalar.**
For `π` irreducible unitary and `f` a class function there is a `c` with
`⟪(π)_{v,w}, f⟫ = c · ⟪w, v⟫` for all `v, w`.

The pairing is `⟪w, T v⟫` for an endomorphism `T` of the carrier, and
`TauCeti.ContRepresentation.inner_matrixCoeffLp_map_map` makes `T` an intertwiner; Schur's lemma
over an algebraically closed field turns it into a scalar. -/
theorem exists_forall_inner_matrixCoeffLp_eq [IsAlgClosed 𝕜] (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G)) :
    ∃ c : 𝕜, ∀ v w : V, ⟪matrixCoeffLp π hπ v w, f⟫_𝕜 = c * ⟪w, v⟫_𝕜 := by
  classical
  have _ : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  set e := stdOrthonormalBasis 𝕜 V
  -- The endomorphism representing the pairing `⟪(π)_{v,w}, f⟫` in its second vector.
  set T : V →ₗ[𝕜] V :=
    { toFun := fun v ↦ ∑ a, ⟪matrixCoeffLp π hπ v (e a), f⟫_𝕜 • e a
      map_add' := fun v₁ v₂ ↦ by
        simp [matrixCoeffLp_add_left, inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        simp [matrixCoeffLp_smul_left, inner_smul_left, mul_smul, Finset.smul_sum] } with hTdef
  have hT : ∀ v w : V, ⟪w, T v⟫_𝕜 = ⟪matrixCoeffLp π hπ v w, f⟫_𝕜 := by
    intro v w
    have hw : ∑ a, ⟪e a, w⟫_𝕜 • e a = w := e.sum_repr' w
    have hsum : matrixCoeffLp π hπ v w = ∑ a, ⟪e a, w⟫_𝕜 • matrixCoeffLp π hπ v (e a) := by
      conv_lhs => rw [← hw]
      simp only [← matrixCoeffLpₛₗ_apply_apply, map_sum, map_smul]
    rw [hsum, hTdef]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right, sum_inner,
      inner_smul_left]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [inner_conj_symm, mul_comm]
  have hcomm : ∀ (g : G) (v : V), T (π g v) = π g (T v) :=
    (isIntertwiningMap_of_inner_matrixCoeffLp_eq hπ hunitary hf T hT).isIntertwining
  -- Schur's lemma turns it into a scalar.
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_irreducible π hirr
    { toContinuousLinearMap := LinearMap.toContinuousLinearMap T
      isIntertwining' := fun g ↦ by ext v; simpa using hcomm g v }
  have hc' := congrArg ContIntertwiningMap.toContinuousLinearMap hc
  simp only [ContIntertwiningMap.toContinuousLinearMap_smul,
    ContIntertwiningMap.toContinuousLinearMap_one, ContinuousLinearMap.one_def] at hc'
  refine ⟨c, fun v w ↦ ?_⟩
  have hTv : T v = c • v := by simpa using congrArg (fun F : V →L[𝕜] V ↦ F v) hc'
  rw [← hT v w, hTv, inner_smul_right]

end Scalar

section Inversion

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Inverting the argument turns the character into the sum of the diagonal matrix
coefficients.**  The character of a unitary representation satisfies `χ g⁻¹ = conj (χ g)`, and the
conjugate of a character is the sum of its diagonal matrix coefficients
(`TauCeti.ContRepresentation.star_character`). This is the identity that lets a statement about
the characters be read off the Peter-Weyl basis, whose blocks are spanned by the matrix
coefficients themselves. -/
theorem invLpₗᵢ_characterLp {π : ContRepresentation 𝕜 G V} (hπ : Continuous π)
    (hunitary : IsUnitary π) {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) :
    invLpₗᵢ 𝕜 (characterLp π hπ) = ∑ a, matrixCoeffLp π hπ (e a) (e a) := by
  have hcomp : (character π hπ).comp ⟨Inv.inv, continuous_inv⟩ = star (character π hπ) :=
    ContinuousMap.ext fun g ↦ character_apply_inv π hπ hunitary g
  rw [characterLp_def, invLpₗᵢ_toLp, hcomp, star_character π hπ e, map_sum]
  simp [matrixCoeffLp_def]

end Inversion

section Model

variable {𝕜 G : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Vanishing against a character kills every matrix coefficient in its irreducible block.**
For an irreducible model, a class function pairs with all matrix coefficients of its inverse-
translate through one scalar. The sum of the diagonal pairings is its pairing with the character,
so that scalar vanishes when the character pairing does. -/
theorem inner_matrixCoeffLp_inv_eq_zero_of_inner_characterLp_eq_zero (m : IrrepModel 𝕜 G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G))
    (horth : ⟪characterLp m.rep m.continuous_rep, f⟫_𝕜 = 0)
    (v w : EuclideanSpace 𝕜 (Fin m.dim)) :
    ⟪matrixCoeffLp m.rep m.continuous_rep v w, invLpₗᵢ 𝕜 f⟫_𝕜 = 0 := by
  classical
  have hinv : invLpₗᵢ 𝕜 f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G) :=
    invLpₗᵢ_mem_classFunctionLp (𝕜 := 𝕜) hf
  obtain ⟨c, hc⟩ := exists_forall_inner_matrixCoeffLp_eq m.continuous_rep m.isUnitary
    m.isIrreducible hinv
  have hdim : (m.dim : 𝕜) ≠ 0 := by
    have hpos : 0 < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin m.dim)) := by
      have _ : Nontrivial (EuclideanSpace 𝕜 (Fin m.dim)) :=
        Representation.IsIrreducible.nontrivial m.isIrreducible
      exact Module.finrank_pos
    rw [finrank_euclideanSpace_fin] at hpos
    exact_mod_cast hpos.ne'
  have hone : ∀ a, ⟪m.basis a, m.basis a⟫_𝕜 = 1 := fun a ↦ by simp
  have hchar : ∑ a, ⟪matrixCoeffLp m.rep m.continuous_rep (m.basis a) (m.basis a),
      invLpₗᵢ 𝕜 f⟫_𝕜 = ⟪characterLp m.rep m.continuous_rep, f⟫_𝕜 := by
    rw [← sum_inner, ← invLpₗᵢ_characterLp m.continuous_rep m.isUnitary m.basis]
    exact (invLpₗᵢ (E := 𝕜) (p := 2) (μ := haarProb G) 𝕜).toLinearIsometry.inner_map_map _ _
  have hsum : c * (m.dim : 𝕜) = 0 := by
    rw [← horth, ← hchar]
    simp only [hc, hone, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_comm]
  rw [hc v w, (mul_eq_zero.1 hsum).resolve_right hdim, zero_mul]

end Model

end ContRepresentation

section Completeness

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {models : ι → IrrepModel 𝕜 G}

omit [T2Space G] in
/-- **Class-function completeness.**  A class function in `L²(G)` orthogonal to the character of
every model in a skeleton of the unitary dual is zero.

The argument runs on the inverse-translate `f(·⁻¹)`, which is again a class function: inversion
turns the pairing against a character into the pairing against the sum of the diagonal matrix
coefficients, which by `TauCeti.ContRepresentation.exists_forall_inner_matrixCoeffLp_eq` is
`dim V_i` times the single scalar that the whole block contributes to. That scalar therefore
vanishes, so the inverse-translate is orthogonal to the whole Peter-Weyl basis. -/
theorem eq_zero_of_forall_inner_characterLp_eq_zero [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G))
    (horth : ∀ i, ⟪ContRepresentation.characterLp (models i).rep (models i).continuous_rep,
      f⟫_𝕜 = 0) :
    f = 0 := by
  classical
  set u := invLpₗᵢ 𝕜 f with hu
  -- On each block the pairing with `u` vanishes because its diagonal sum is the pairing of `f`
  -- against the corresponding character.
  have hblock : ∀ (i : ι) (v w : EuclideanSpace 𝕜 (Fin (models i).dim)),
      ⟪ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v w, u⟫_𝕜 = 0 := by
    intro i v w
    rw [hu]
    exact ContRepresentation.inner_matrixCoeffLp_inv_eq_zero_of_inner_characterLp_eq_zero
      (models i) hf (horth i) v w
  -- Hence `u` is orthogonal to the whole Peter-Weyl basis, so it vanishes.
  have hmem : u ∈ (Submodule.span 𝕜 (Set.range (peterWeylFamily models)))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        rw [peterWeylFamily_apply, inner_smul_left, hblock x.1, mul_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hzero : u = 0 := by
    rw [h.orthogonal_span_peterWeylFamily_eq_bot] at hmem
    simpa using hmem
  rw [hu] at hzero
  simpa using hzero

end Completeness

section Basis

variable {𝕜 G ι : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **The characters of a family of models, inside the class functions.**  A character is a class
function (`TauCeti.ContRepresentation.characterLp_mem_classFunctionLp`), so it is an element of
`classFunctionLp` and not merely of `L²(G)`; the class-function completeness below is a statement
about this family. -/
noncomputable def characterFamily (models : ι → IrrepModel 𝕜 G) (i : ι) :
    classFunctionLp 𝕜 𝕜 2 (haarProb G) :=
  ⟨ContRepresentation.characterLp (models i).rep (models i).continuous_rep,
    ContRepresentation.characterLp_mem_classFunctionLp _ _⟩

omit [IsAlgClosed 𝕜] [T2Space G] in
@[simp]
theorem coe_characterFamily (models : ι → IrrepModel 𝕜 G) (i : ι) :
    (characterFamily models i : Lp 𝕜 2 (haarProb G)) =
      ContRepresentation.characterLp (models i).rep (models i).continuous_rep :=
  (rfl)

variable {models : ι → IrrepModel 𝕜 G}

omit [T2Space G] in
/-- **The characters of a pairwise inequivalent family are orthonormal in the class functions.**
This is the character orthogonality of `TauCeti.ContRepresentation.orthonormal_characterLp`, read
inside the subspace, where the inner product is the restriction of the one on `L²(G)`.  Only
inequivalence is used; exhaustivity of a skeleton is what the completeness below needs. -/
theorem orthonormal_characterFamily
    (hne : Pairwise fun i j ↦
      IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    Orthonormal 𝕜 (characterFamily models) := by
  have hL2 := ContRepresentation.orthonormal_characterLp (fun i ↦ (models i).rep)
    (fun i ↦ (models i).continuous_rep) (fun i ↦ (models i).isUnitary)
    (fun i ↦ (models i).isIrreducible) hne
  exact hL2.codRestrict _ fun i ↦ ContRepresentation.characterLp_mem_classFunctionLp _ _

omit [T2Space G] in
/-- **The characters of a skeleton are complete in the class functions.**  Their span is dense:
its orthogonal complement inside `classFunctionLp` vanishes, which is
`TauCeti.eq_zero_of_forall_inner_characterLp_eq_zero`. -/
theorem orthogonal_span_characterFamily_eq_bot (h : IsIrrepSkeleton models) :
    (Submodule.span 𝕜 (Set.range (characterFamily models)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf ↦ ?_
  have horth : ∀ i, ⟪ContRepresentation.characterLp (models i).rep (models i).continuous_rep,
      (f : Lp 𝕜 2 (haarProb G))⟫_𝕜 = 0 := by
    intro i
    have := (Submodule.mem_orthogonal _ _).1 hf (characterFamily models i)
      (Submodule.subset_span ⟨i, rfl⟩)
    rwa [Submodule.coe_inner, coe_characterFamily] at this
  exact Subtype.ext (eq_zero_of_forall_inner_characterLp_eq_zero h f.2 horth)

/-- **The irreducible characters are a Hilbert basis of the class functions.**  For a skeleton of
the unitary dual of a compact Hausdorff group, the characters of the models are an orthonormal
basis of the closed subspace `classFunctionLp` of `L²(G)`.

This is the "central" restriction of Peter-Weyl: a class function sees only the trace direction of
each block of the Peter-Weyl basis, and that direction is spanned by the character. For a finite
group it is the statement that the irreducible characters are a basis of the class functions. -/
noncomputable def characterBasis (h : IsIrrepSkeleton models) :
    HilbertBasis ι 𝕜 (classFunctionLp 𝕜 𝕜 2 (haarProb G)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_characterFamily h.pairwise_isEmpty_equiv)
    (orthogonal_span_characterFamily_eq_bot h)

omit [T2Space G] in
/-- **The class-function basis is the characters.**  As for `TauCeti.coe_peterWeylBasis`, the
elements are on the nose the characters of the models, not merely some orthonormal basis whose
existence is asserted. -/
@[simp]
theorem coe_characterBasis (h : IsIrrepSkeleton models) :
    ⇑(characterBasis h) = characterFamily models :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

variable (𝕜 G)

/-- **The class-function basis, unconditionally.**  The characters of the models chosen in the
unitary equivalence classes are a Hilbert basis of `classFunctionLp`; no skeleton is assumed,
`TauCeti.isIrrepSkeleton_model` supplies one. -/
noncomputable def stdCharacterBasis :
    HilbertBasis (IrrepClass 𝕜 G) 𝕜 (classFunctionLp 𝕜 𝕜 2 (haarProb G)) :=
  characterBasis (isIrrepSkeleton_model 𝕜 G)

omit [T2Space G] in
/-- The unconditional class-function basis is the characters of the chosen representatives. -/
@[simp]
theorem coe_stdCharacterBasis :
    ⇑(stdCharacterBasis 𝕜 G) = characterFamily (IrrepClass.model (𝕜 := 𝕜) (G := G)) :=
  coe_characterBasis _

end Basis

end TauCeti
