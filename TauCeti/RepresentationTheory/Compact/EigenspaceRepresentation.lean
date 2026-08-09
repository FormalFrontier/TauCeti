/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Convolution
public import TauCeti.RepresentationTheory.Continuous.Representative
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The finite-dimensional representations carried by convolution eigenspaces

A compact group `G` acts on `L²(G)` by right translation, `(π g f) x = f (x * g)`. This action is
isometric, but the map `g ↦ π g` is *not* continuous for the operator norm, so `L²(G)` itself is
not a continuous representation in the sense of `TauCeti.ContRepresentation` together with a
continuity hypothesis. Restricted to an eigenspace of a convolution operator at a nonzero
eigenvalue, it is: that eigenspace is finite-dimensional, right-translation invariant, and made of
continuous functions, all of which `TauCeti.RepresentationTheory.Compact.Convolution` supplies.

This file assembles those three facts into the representation itself, and reads off the
consequence the Peter-Weyl theorem needs: the continuous representative `μ⁻¹ • (k * f)` of an
eigenvector `f` is a **matrix coefficient** of that representation, so it lies in the
representative ring `𝓡(G)`. Since the eigenspaces of a symmetric kernel span a dense subspace of
`L²(G)` and convolution is bounded from `L²(G)` into the uniform norm, *every* function of the form
`k * f` lies in the uniform closure of `𝓡(G)`.

This is where the finite-dimensional representations of a compact group come from. Nothing here
presupposes that `G` has any: the representation is manufactured out of the spectral theory of a
compact self-adjoint operator, and no point-separation property is used, so the argument does not
quietly assume the theorem it serves.

## Main definitions

* `TauCeti.rightRegularLp`: the right regular representation of `G` on `L²(G)`.
* `TauCeti.rightTranslate`: the right translates of a continuous map, as a continuous map
  `G → C(G, X)`; continuity is for the compact-open topology, which for compact `G` is the
  uniform norm.
* `TauCeti.convolutionEigenspaceRep`: the restriction of the right regular representation to an
  eigenspace of a convolution operator.

## Main statements

* `TauCeti.isUnitary_rightRegularLp`: right translation preserves the `L²` inner product.
* `TauCeti.continuous_convolutionEigenspaceRep`: at a nonzero eigenvalue the eigenspace
  representation is continuous, so it is a genuine finite-dimensional continuous representation
  of `G`.
* `TauCeti.isRepresentative_smul_convolutionCLM`: the continuous representative of an eigenvector
  at a nonzero eigenvalue is a matrix coefficient of that representation.
* `TauCeti.convolutionCLM_mem_representativeSubmodule_of_mem_iSup`: convolving a finite sum of
  eigenvectors gives an element of `𝓡(G)`.
* `TauCeti.convolutionCLM_mem_closure_representativeSubmodule`: for a symmetric kernel, `k * f`
  lies in the uniform closure of `𝓡(G)` for *every* `f ∈ L²(G)`.

## Implementation notes

Continuity of `g ↦ π g` on the eigenspace is checked pointwise, which is enough because the
eigenspace is finite-dimensional (`continuous_clm_apply`). Pointwise, the translate `π g f` is the
image under `ContinuousMap.toLp` of the right translate of the *continuous* function
`μ⁻¹ • (k * f)`, and right translates of a continuous function on a compact group vary
continuously in the uniform norm; that last fact is `TauCeti.rightTranslate`, obtained by currying
`(g, x) ↦ F (x * g)`, so no uniform structure has to be put on `G`.

The matrix coefficient is produced from the linear functional `h ↦ μ⁻¹ • (k * h) 1`, evaluation of
the continuous representative at the identity. Its Riesz vector `y` satisfies
`⟪y, π g f⟫ = μ⁻¹ • (k * f) g`, and Mathlib's inner product is conjugate linear in its first
argument, so what appears directly is the *conjugate* of the matrix coefficient
`g ↦ ⟪π g f, y⟫`. The representative functions are closed under conjugation
(`TauCeti.IsRepresentative.star`), so nothing is lost.

## References

This is the `nonzero_eigenspace_finite_dim_continuous_rep` step of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
which asks for each nonzero eigenspace to be finite-dimensional and translation invariant, "so it
carries a continuous finite-dimensional representation whose functions lie in `𝓡(G)`". Combined
with an approximate identity it gives the uniform density of `𝓡(G)` in `C(G)`, the analytic core
of the Peter-Weyl theorem.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), Chapter 5.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

/-! ### Right translates of a continuous map -/

section RightTranslate

variable {G X : Type*} [TopologicalSpace G] [Mul G] [ContinuousMul G] [TopologicalSpace X]

/-- **The right translates of a continuous map**, as a continuous map `G → C(G, X)` sending `g`
to `x ↦ F (x * g)`.

Continuity of this map is continuity for the compact-open topology of `C(G, X)`, which for
compact `G` and normed `X` is the uniform norm; it is exactly the statement that
`(g, x) ↦ F (x * g)` curries, so it needs no uniform structure on `G`. -/
def rightTranslate (F : C(G, X)) : C(G, C(G, X)) :=
  ContinuousMap.curry
    ⟨fun p : G × G => F (p.2 * p.1), F.continuous.comp (continuous_snd.mul continuous_fst)⟩

@[simp]
theorem rightTranslate_apply_apply (F : C(G, X)) (g x : G) : rightTranslate F g x = F (x * g) :=
  (rfl)

end RightTranslate

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### The right regular representation on `L²(G)` -/

/-- Composition with two equal measure-preserving maps agrees; the two measure-preserving proofs
are irrelevant. This is the bookkeeping behind the monoid-homomorphism laws of `rightRegularLp`,
where `(· * (g * h))` and `(· * h) ∘ (· * g)` are equal as functions but come with different
proofs. -/
private theorem compMeasurePreserving_congr {f f' : G → G}
    (hf : MeasurePreserving f (haarProb G) (haarProb G))
    (hf' : MeasurePreserving f' (haarProb G) (haarProb G)) (h : f = f')
    (x : Lp 𝕜 2 (haarProb G)) :
    Lp.compMeasurePreserving f hf x = Lp.compMeasurePreserving f' hf' x := by
  subst h
  rfl

variable (𝕜 G) in
/-- **The right regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (x * g))`, which preserves normalized Haar measure and hence the `L²` norm.

The map `g ↦ π g` is *not* continuous for the operator norm unless `G` is finite, which is why
`ContRepresentation` carries no continuity field; continuity holds after restricting to a
convolution eigenspace (`TauCeti.continuous_convolutionEigenspaceRep`). -/
noncomputable def rightRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (· * g)
        (measurePreserving_mul_right (haarProb G) g)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun x => by
        refine (compMeasurePreserving_congr (𝕜 := 𝕜) _ (MeasurePreserving.id (haarProb G))
          (funext fun y => mul_one y) x).trans ?_
        exact Lp.compMeasurePreserving_id_apply x
      map_mul' g h := ContinuousLinearMap.ext fun x => by
        refine (compMeasurePreserving_congr (𝕜 := 𝕜) _
          (((measurePreserving_mul_right (haarProb G) h).comp
            (measurePreserving_mul_right (haarProb G) g)))
          (funext fun y => (mul_assoc y g h).symm) x).trans ?_
        exact Lp.compMeasurePreserving_comp_apply x _ _ }

/-- Right translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`. This is
implementation bookkeeping; the characterization to use is `coeFn_rightRegularLp`. -/
private theorem rightRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    rightRegularLp 𝕜 G g f
      = Lp.compMeasurePreserving (· * g) (measurePreserving_mul_right (haarProb G) g) f :=
  (rfl)

/-- Right translation on `L²(G)` is represented by right translation of functions. -/
theorem coeFn_rightRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    rightRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (x * g) :=
  Lp.coeFn_compMeasurePreserving f _

variable (𝕜 G) in
/-- **The right regular representation is unitary**, because right translation preserves
normalized Haar measure. -/
theorem isUnitary_rightRegularLp : ContRepresentation.IsUnitary (rightRegularLp 𝕜 G) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro g f
  exact Lp.norm_compMeasurePreserving f _

/-! ### The representation on an eigenspace of a convolution operator -/

/-- **The representation of `G` on an eigenspace of a convolution operator**: the right regular
representation restricted to the eigenspace, which is right-translation invariant because
convolution commutes with right translation. -/
noncomputable def convolutionEigenspaceRep (k : C(G, 𝕜)) (μ : 𝕜) :
    ContRepresentation 𝕜 G
      (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :=
  ContRepresentation.subrepresentation (rightRegularLp 𝕜 G) _
    fun g _ hf => compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator k μ g hf

@[simp]
theorem coe_convolutionEigenspaceRep_apply (k : C(G, 𝕜)) (μ : 𝕜) (g : G)
    (f : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    ((convolutionEigenspaceRep k μ g f : _) : Lp 𝕜 2 (haarProb G))
      = rightRegularLp 𝕜 G g (f : Lp 𝕜 2 (haarProb G)) :=
  ContRepresentation.coe_subrepresentation_apply g f

/-- **The eigenspace representation is unitary**, being a restriction of the unitary right regular
representation. -/
theorem isUnitary_convolutionEigenspaceRep (k : C(G, 𝕜)) (μ : 𝕜) :
    ContRepresentation.IsUnitary (convolutionEigenspaceRep k μ) :=
  (isUnitary_rightRegularLp 𝕜 G).subrepresentation _

/-- **The translate of an eigenvector is the translate of its continuous representative.** At a
nonzero eigenvalue every eigenvector `f` is represented by the continuous function `μ⁻¹ • (k * f)`,
and translating `f` translates that function, because convolution commutes with right
translation. -/
theorem rightRegularLp_eq_toLp_smul_rightTranslate (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0)
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) (g : G) :
    rightRegularLp 𝕜 G g f
      = ContinuousMap.toLp 2 (haarProb G) 𝕜 (μ⁻¹ • rightTranslate (convolutionCLM k f) g) := by
  have hmem := compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator k μ g hf
  rw [rightRegularLp_apply, Lp.ext_iff]
  refine (ae_eq_smul_convolutionCLM_of_mem_eigenspace k hμ hmem).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) _).symm
  refine Filter.Eventually.of_forall fun x => ?_
  simp [convolutionCLM_compMeasurePreserving_mul_right]

/-- **The eigenspace representation at a nonzero eigenvalue is continuous.** The eigenspace is
finite-dimensional, so continuity may be checked one vector at a time; on a vector it is the
continuity of right translation of the corresponding continuous function in the uniform norm.

Together with `TauCeti.finiteDimensional_eigenspace_convolutionOperator` this is the statement
that a nonzero eigenspace of a convolution operator carries a finite-dimensional continuous
representation of `G`. -/
theorem continuous_convolutionEigenspaceRep (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    Continuous (convolutionEigenspaceRep k μ) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  rw [continuous_clm_apply]
  intro f
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  have hval : ∀ g : G, ((convolutionEigenspaceRep k μ g f : _) : Lp 𝕜 2 (haarProb G))
      = ContinuousMap.toLp 2 (haarProb G) 𝕜
          (μ⁻¹ • rightTranslate (convolutionCLM k (f : Lp 𝕜 2 (haarProb G))) g) :=
    fun g => (coe_convolutionEigenspaceRep_apply k μ g f).trans
      (rightRegularLp_eq_toLp_smul_rightTranslate k hμ f.2 g)
  simp only [Function.comp_def, hval]
  exact (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜).continuous.comp
    ((continuous_const_smul μ⁻¹).comp (rightTranslate _).continuous)

/-! ### The eigenvectors are representative functions -/

/-- **The continuous representative of an eigenvector is a representative function.** For a nonzero
eigenvalue `μ`, the continuous function `μ⁻¹ • (k * f)` representing an eigenvector `f` is the
conjugate of a matrix coefficient of `TauCeti.convolutionEigenspaceRep`, at the Riesz vector of the
functional "evaluate the continuous representative at the identity".

This is the point of the whole construction: the eigenspaces do not merely consist of continuous
functions, they consist of matrix coefficients of finite-dimensional continuous representations. -/
theorem isRepresentative_smul_convolutionCLM (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0)
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    IsRepresentative (μ⁻¹ • convolutionCLM k f) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  have hπ := continuous_convolutionEigenspaceRep k hμ
  obtain ⟨y, hy⟩ :
      ∃ y : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
        ∀ h : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
          ⟪y, h⟫_𝕜 = μ⁻¹ * convolutionCLM k (h : Lp 𝕜 2 (haarProb G)) 1 := by
    refine ⟨(InnerProductSpace.toDual 𝕜 _).symm
      (μ⁻¹ • ((ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) (1 : G)).comp
        ((convolutionCLM k).comp
          (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ).subtypeL))),
      fun h => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  have key : μ⁻¹ • convolutionCLM k f
      = star (ContRepresentation.matrixCoeff (convolutionEigenspaceRep k μ) hπ ⟨f, hf⟩ y) := by
    ext g
    have hg : ⟪y, convolutionEigenspaceRep k μ g ⟨f, hf⟩⟫_𝕜 = μ⁻¹ * convolutionCLM k f g := by
      rw [hy, coe_convolutionEigenspaceRep_apply, rightRegularLp_apply,
        convolutionCLM_compMeasurePreserving_mul_right, one_mul]
    rw [ContinuousMap.star_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContRepresentation.matrixCoeff_apply, RCLike.star_def, inner_conj_symm, hg]
  rw [key]
  exact (isRepresentative_matrixCoeff _ hπ _ _).star

/-- **Convolving a `0`-eigenvector gives the zero function.** The convolution is a continuous
function which is almost everywhere zero, and normalized Haar measure is positive on nonempty open
sets. -/
theorem convolutionCLM_eq_zero_of_mem_eigenspace_zero (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap 0) :
    convolutionCLM k f = 0 := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, zero_smul] at hf
  have h0 : ⇑(convolutionCLM k f) =ᵐ[haarProb G] (0 : G → 𝕜) := by
    refine (coeFn_convolutionOperator k f).symm.trans ?_
    rw [hf]
    exact Lp.coeFn_zero 𝕜 2 (haarProb G)
  exact ContinuousMap.ext (congrFun
    (((convolutionCLM k f).continuous.ae_eq_iff_eq (haarProb G) continuous_const).1 h0))

/-- **Convolving a finite sum of eigenvectors gives a representative function.** Each nonzero
eigenvalue contributes a matrix coefficient, and the zero eigenspace contributes nothing. -/
theorem convolutionCLM_mem_representativeSubmodule_of_mem_iSup (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    convolutionCLM k f ∈ representativeSubmodule 𝕜 G := by
  refine Submodule.iSup_induction (motive := fun x => convolutionCLM k x ∈
    representativeSubmodule 𝕜 G) _ hf (fun μ x hx => ?_) (by rw [map_zero]; exact zero_mem _)
    fun x y hx hy => ?_
  · rcases eq_or_ne μ 0 with rfl | hμ
    · rw [convolutionCLM_eq_zero_of_mem_eigenspace_zero k hx]
      exact zero_mem _
    · have hsmul : convolutionCLM k x = μ • (μ⁻¹ • convolutionCLM k x) := by
        rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
      rw [hsmul]
      exact Submodule.smul_mem _ _ (mem_representativeSubmodule_of_isRepresentative
        (isRepresentative_smul_convolutionCLM k hμ hx))
  · rw [map_add]
    exact add_mem hx hy

/-- **Every convolution by a symmetric kernel lies in the uniform closure of the representative
ring.** The eigenspaces of a symmetric convolution operator span a dense subspace of `L²(G)`, each
of them convolves into `𝓡(G)`, and convolution is continuous from `L²(G)` into the uniform norm of
`C(G)`.

With an approximate identity, which lets a continuous function be uniformly approximated by such
convolutions, this gives the uniform density of `𝓡(G)` in `C(G)`, the analytic core of the
Peter-Weyl theorem. -/
theorem convolutionCLM_mem_closure_representativeSubmodule (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionCLM k f ∈ closure (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  set S := ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ
  have htop : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2
      (orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot k hk)
  have hf : f ∈ closure (S : Set (Lp 𝕜 2 (haarProb G))) := by
    rw [← Submodule.topologicalClosure_coe, htop]
    exact Submodule.mem_top
  refine closure_mono ?_
    (image_closure_subset_closure_image (convolutionCLM (G := G) k).continuous ⟨f, hf, rfl⟩)
  rintro - ⟨h, hh, rfl⟩
  exact convolutionCLM_mem_representativeSubmodule_of_mem_iSup k hh

end CompactGroup

end TauCeti
