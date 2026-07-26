module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Pointwise products of `L²` functions on a finite product measure

For a finite family of σ-finite measures `μ i` and `L²(μ i)` functions `f i`, the pointwise product
`x ↦ ∏ i, f i (x i)` belongs to `L²(Measure.pi μ)`, the assignment factors the inner product as a
tensor, and coordinatewise Hilbert bases multiply to a Hilbert basis `TauCeti.piHilbertBasis` of
`L²(Measure.pi μ)`. This is Part B3/D of the `OrthogonalL2Bases` roadmap, and the `Fintype`-indexed
analogue of the binary product basis.

Mathlib has the two Fubini inputs at this arity already — `Integrable.fintype_prod_dep` and
`integral_fintype_prod_eq_prod` (the latter with no integrability side conditions) — so the
orthonormality half is short. The completeness half runs in three moves:

1. `TauCeti.inner_L2piMul_eq_zero_of_forall_basis` — orthogonality to the *basis* tensors upgrades
   to orthogonality to *every* elementary tensor. The coordinates are generalized one at a time by
   `Finset` induction: at each step a single slot is expanded along its basis and the sum is pushed
   through the continuous linear map `TauCeti.L2piMulSlot`. No countability is assumed of any `κ i`.
2. `TauCeti.setIntegral_pi_eq_zero_of_forall_inner` — testing against indicators, since a tensor of
   indicators is the indicator of the box.
3. `TauCeti.setIntegral_eq_zero_of_isPiSystem` — the Dynkin (π-λ) step, stated for a *general*
   π-system generating the σ-algebra (the Bochner analogue of Mathlib's
   `lintegral_eq_lintegral_of_isPiSystem`), applied here to `isPiSystem_pi` inside a finite box,
   followed by a monotone exhaustion along `∏ i, spanningSets (μ i) n`.

## Main definitions

* `TauCeti.L2piMul` — the pointwise product `x ↦ ∏ i, F i (x i)` as a vector of `L²(Measure.pi μ)`.
* `TauCeti.piHilbertBasis` — the Hilbert basis of `L²(Measure.pi μ)` built from coordinatewise
  Hilbert bases.

## Main statements

* `TauCeti.memLp_pi_prod` — the pointwise product of `L²` functions is `L²` for the product measure.
* `TauCeti.inner_L2piMul` — the inner product of two tensors factors coordinatewise.
* `TauCeti.orthonormal_L2piMul` — coordinatewise orthonormal families multiply to an orthonormal
  family.
* `TauCeti.orthogonal_span_range_L2piMul_eq_bot` — the completeness half.
* `TauCeti.coeFn_piHilbertBasis` — the `k`-th basis vector is a.e. `∏ i, b i (k i)`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 ι : Type*} [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]

section NormedCommRing

variable [NormedCommRing 𝕜] [NormOneClass 𝕜]

/-- The pointwise product `x ↦ ∏ i, f i (x i)` of `L²` functions is `L²` for the product measure. -/
theorem memLp_pi_prod {f : ∀ i, α i → 𝕜} (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x : ∀ i, α i => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hmeas : AEStronglyMeasurable (fun x : ∀ i, α i => ∏ i, f i (x i)) (Measure.pi μ) :=
    Finset.aestronglyMeasurable_fun_prod (f := fun i (x : ∀ j, α j) => f i (x i)) _ fun i _ =>
      (hf i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  -- Only the submultiplicative bound `‖∏ aᵢ‖ ≤ ∏ ‖aᵢ‖` is needed, so a normed commutative
  -- ring suffices; the norm need not be multiplicative.
  refine (Integrable.fintype_prod_dep
    (fun i => (memLp_two_iff_integrable_sq_norm (hf i).1).1 (hf i))).mono
    (hmeas.norm.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  have hle : ‖∏ i, f i (x i)‖ ≤ ∏ i, ‖f i (x i)‖ := Finset.norm_prod_le _ _
  have hnn : (0 : ℝ) ≤ ∏ i, ‖f i (x i)‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Finset.prod_pow]
  gcongr

/-- The pointwise product `x ↦ ∏ i, F i (x i)` of a family of `L²(μ i)` vectors, as a vector of
`L²(Measure.pi μ)`. -/
noncomputable def L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : Lp 𝕜 2 (Measure.pi μ) :=
  (memLp_pi_prod (fun i => Lp.memLp (F i))).toLp _

/-- The `Lp` representative of `L2piMul F` is the pointwise product of the representatives. -/
theorem coeFn_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) :
    ⇑(L2piMul F) =ᵐ[Measure.pi μ] fun x : ∀ i, α i => ∏ i, F i (x i) :=
  MemLp.coeFn_toLp _

end NormedCommRing

variable [RCLike 𝕜]

/-- **The tensor inner-product identity, `Fintype`-indexed.** The inner product of two pointwise
products factors as the product of the coordinatewise inner products. -/
@[simp]
theorem inner_L2piMul (F G : ∀ i, Lp 𝕜 2 (μ i)) :
    inner 𝕜 (L2piMul F) (L2piMul G) = ∏ i, inner 𝕜 (F i) (G i) := by
  rw [L2.inner_def]
  calc
    ∫ x, inner 𝕜 (L2piMul F x) (L2piMul G x) ∂(Measure.pi μ)
        = ∫ x : ∀ i, α i, ∏ i, inner 𝕜 (F i (x i)) (G i (x i)) ∂(Measure.pi μ) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2piMul F, coeFn_L2piMul G] with x hF hG
          rw [hF, hG]
          simp only [RCLike.inner_apply', map_prod, Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, inner 𝕜 (F i x) (G i x) ∂(μ i) :=
          integral_fintype_prod_eq_prod (fun i x => inner 𝕜 (F i x) (G i x))
    _ = ∏ i, inner 𝕜 (F i) (G i) :=
          Finset.prod_congr rfl fun i _ => (L2.inner_def _ _).symm

/-- **Orthonormality of the tensor family, `Fintype`-indexed.** Coordinatewise orthonormal families
multiply to an orthonormal family of `L²(Measure.pi μ)`, indexed by the dependent function type. -/
theorem orthonormal_L2piMul {κ : ι → Type*} {b : ∀ i, κ i → Lp 𝕜 2 (μ i)}
    (hb : ∀ i, Orthonormal 𝕜 (b i)) :
    Orthonormal 𝕜 (fun k : ∀ i, κ i => L2piMul (fun i => b i (k i))) := by
  classical
  simp_rw [orthonormal_iff_ite] at hb ⊢
  intro k l
  rw [inner_L2piMul]
  simp_rw [hb]
  by_cases hkl : k = l
  · subst hkl
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hkl
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), if_neg hkl]

/-- The tensor construction is norm-multiplicative. -/
@[simp]
theorem norm_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : ‖L2piMul F‖ = ∏ i, ‖F i‖ := by
  have h : ((‖L2piMul F‖ : ℝ) : 𝕜) ^ 2 = ∏ i, ((‖F i‖ : ℝ) : 𝕜) ^ 2 := by
    simpa only [inner_self_eq_norm_sq_to_K] using inner_L2piMul F F
  have h3 : ‖L2piMul F‖ ^ 2 = (∏ i, ‖F i‖) ^ 2 := by
    have hc : ((‖L2piMul F‖ ^ 2 : ℝ) : 𝕜) = (((∏ i, ‖F i‖) ^ 2 : ℝ) : 𝕜) := by
      push_cast
      rw [h, ← Finset.prod_pow]
    exact_mod_cast hc
  exact (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)).1 h3

section Slot

variable [DecidableEq ι]

/-- Splitting off the `j`-th coordinate of a tensor. -/
theorem coeFn_L2piMul_update (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    ⇑(L2piMul (Function.update F j v)) =ᵐ[Measure.pi μ]
      fun x : ∀ i, α i => v (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  filter_upwards [coeFn_L2piMul (Function.update F j v)] with x hx
  rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The tensor is additive in the `j`-th coordinate. -/
@[simp]
theorem L2piMul_update_add (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v w : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (v + w))
      = L2piMul (Function.update F j v) + L2piMul (Function.update F j w) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (v + w), coeFn_L2piMul_update j F v,
    coeFn_L2piMul_update j F w,
    Lp.coeFn_add (L2piMul (Function.update F j v)) (L2piMul (Function.update F j w)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_add v w)]
    with x h h1 h2 hadd hv
  rw [h, hadd, Pi.add_apply, h1, h2, hv, Pi.add_apply, add_mul]

/-- The tensor is homogeneous in the `j`-th coordinate. -/
@[simp]
theorem L2piMul_update_smul (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (c : 𝕜) (v : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (c • v)) = c • L2piMul (Function.update F j v) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (c • v), coeFn_L2piMul_update j F v,
    Lp.coeFn_smul c (L2piMul (Function.update F j v)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_smul c v)]
    with x h h1 hsmul hv
  rw [h, hsmul, Pi.smul_apply, h1, hv, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The tensor vanishes when its `j`-th coordinate does. -/
@[simp]
theorem L2piMul_update_zero (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) :
    L2piMul (Function.update F j 0) = 0 := by
  simpa using L2piMul_update_smul j F 0 0

/-- The norm of a tensor with its `j`-th coordinate replaced. -/
theorem norm_L2piMul_update (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    ‖L2piMul (Function.update F j v)‖ = (∏ i ∈ Finset.univ.erase j, ‖F i‖) * ‖v‖ := by
  rw [norm_L2piMul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Tensoring with all coordinates but `j` held fixed, as a continuous linear map. -/
noncomputable def L2piMulSlot (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) :
    Lp 𝕜 2 (μ j) →L[𝕜] Lp 𝕜 2 (Measure.pi μ) :=
  LinearMap.mkContinuous
    { toFun := fun v => L2piMul (Function.update F j v)
      map_add' := L2piMul_update_add j F
      map_smul' := fun c v => L2piMul_update_smul j F c v }
    (∏ i ∈ Finset.univ.erase j, ‖F i‖) fun v => le_of_eq (norm_L2piMul_update j F v)

/-- `L2piMulSlot` applies as the tensor. -/
@[simp]
theorem L2piMulSlot_apply (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    L2piMulSlot j F v = L2piMul (Function.update F j v) :=
  LinearMap.mkContinuous_apply _ _ _ _

end Slot

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from
coordinatewise Hilbert bases is orthogonal to *every* elementary tensor. -/
theorem inner_L2piMul_eq_zero_of_forall_basis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ k : ∀ i, κ i, inner 𝕜 h (L2piMul (fun i => b i (k i))) = 0)
    (F : ∀ i, Lp 𝕜 2 (μ i)) : inner 𝕜 h (L2piMul F) = 0 := by
  classical
  have key : ∀ S : Finset ι, ∀ F : ∀ i, Lp 𝕜 2 (μ i),
      (∀ i, i ∉ S → ∃ c, F i = b i c) → inner 𝕜 h (L2piMul F) = 0 := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro F hF
        choose k hk using fun i => hF i (by simp)
        have hFk : F = fun i => b i (k i) := funext hk
        rw [hFk]
        exact hz k
    | @insert j S hj ih =>
        intro F hF
        have hsum := ((b j).hasSum_repr (F j)).mapL ((innerSL 𝕜 h).comp (L2piMulSlot j F))
        have hzero : HasSum (fun _ : κ j => (0 : 𝕜))
            ((innerSL 𝕜 h).comp (L2piMulSlot j F) (F j)) := by
          refine hsum.congr_fun fun c => ?_
          have hupd : inner 𝕜 h (L2piMul (Function.update F j (b j c))) = 0 := by
            refine ih _ fun i hi => ?_
            by_cases hij : i = j
            · subst hij
              exact ⟨c, by rw [Function.update_self]⟩
            · rw [Function.update_of_ne hij]
              exact hF i fun hmem => (Finset.mem_insert.1 hmem).elim hij hi
          simp only [ContinuousLinearMap.comp_apply, map_smul, L2piMulSlot_apply,
            innerSL_apply_apply, hupd, smul_zero]
        have hfin := (hasSum_zero.unique hzero).symm
        rw [ContinuousLinearMap.comp_apply, L2piMulSlot_apply, Function.update_eq_self,
          innerSL_apply_apply] at hfin
        exact hfin
  exact key Finset.univ F fun i hi => absurd (Finset.mem_univ i) hi

/-- The tensor of indicators is the indicator of the box, so orthogonality to every elementary
tensor makes the integral over every finite-measure box vanish. -/
theorem setIntegral_pi_eq_zero_of_forall_inner {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0)
    (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ i (s i) ≠ ⊤) :
    ∫ x in Set.univ.pi s, h x ∂(Measure.pi μ) = 0 := by
  set F : ∀ i, Lp 𝕜 2 (μ i) := fun i => indicatorConstLp 2 (hs i) (hfin i) (1 : 𝕜) with hFdef
  have hFc : ∀ᵐ x : ∀ i, α i ∂(Measure.pi μ),
      ∀ i, F i (x i) = (s i).indicator (fun _ => (1 : 𝕜)) (x i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval μ i).tendsto_ae.eventually
      (indicatorConstLp_coeFn (s := s i) (hμs := hfin i) (c := (1 : 𝕜)))
  calc ∫ x in Set.univ.pi s, h x ∂(Measure.pi μ)
      = ∫ x, (Set.univ.pi s).indicator (fun y => h y) x ∂(Measure.pi μ) :=
        (integral_indicator (MeasurableSet.univ_pi hs)).symm
    _ = ∫ x, inner 𝕜 ((L2piMul F) x) (h x) ∂(Measure.pi μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_L2piMul F, hFc] with x hx hF
        rw [hx]
        simp_rw [hF]
        by_cases hmem : ∀ i, x i ∈ s i
        · simp [hmem]
        · obtain ⟨i, hi⟩ := not_forall.1 hmem
          rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
          simp [hmem]
    _ = inner 𝕜 (L2piMul F) h := (L2.inner_def _ _).symm
    _ = 0 := hz F

/-- A vector orthogonal to every elementary tensor has vanishing integral over every measurable set
of finite measure. -/
theorem setIntegral_eq_zero_of_forall_inner_pi {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0)
    (u : Set (∀ i, α i)) (hu : MeasurableSet u) (hfin : Measure.pi μ u < ⊤) :
    ∫ x in u, h x ∂(Measure.pi μ) = 0 := by
  classical
  have hboxm : ∀ n, MeasurableSet (Set.univ.pi fun i => spanningSets (μ i) n) := fun n =>
    MeasurableSet.univ_pi fun i => measurableSet_spanningSets (μ i) n
  have hboxfin : ∀ n, Measure.pi μ (Set.univ.pi fun i => spanningSets (μ i) n) < ⊤ := by
    intro n
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun i _ => measure_spanningSets_lt_top (μ i) n
  have hb : ∀ n, ∫ x in u ∩ (Set.univ.pi fun i => spanningSets (μ i) n),
      h x ∂(Measure.pi μ) = 0 := by
    intro n
    have huniv : ∫ x, h x ∂((Measure.pi μ).restrict
        (Set.univ.pi fun i => spanningSets (μ i) n)) = 0 :=
      setIntegral_pi_eq_zero_of_forall_inner hz _ (fun i => measurableSet_spanningSets (μ i) n)
        (fun i => (measure_spanningSets_lt_top (μ i) n).ne)
    have hS : ∀ t ∈ (Set.pi Set.univ '' Set.pi Set.univ fun i => {v : Set (α i) | MeasurableSet v}),
        ∫ x in t, h x ∂((Measure.pi μ).restrict
          (Set.univ.pi fun i => spanningSets (μ i) n)) = 0 := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Measure.restrict_restrict
        (MeasurableSet.univ_pi fun i => ht i (Set.mem_univ i)), ← Set.pi_inter_distrib]
      exact setIntegral_pi_eq_zero_of_forall_inner hz _
        (fun i => (ht i (Set.mem_univ i)).inter (measurableSet_spanningSets (μ i) n))
        (fun i => (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_spanningSets_lt_top (μ i) n)).ne)
    have hdyn := setIntegral_eq_zero_of_isPiSystem generateFrom_pi.symm isPiSystem_pi
      (integrableOn_Lp_of_measure_ne_top h one_le_two (hboxfin n).ne) huniv hS u hu
    rwa [Measure.restrict_restrict hu] at hdyn
  have hmono : Monotone fun n => u ∩ (Set.univ.pi fun i => spanningSets (μ i) n) := fun m n hmn =>
    Set.inter_subset_inter_right _ (Set.pi_mono fun i _ => monotone_spanningSets (μ i) hmn)
  have hcover : ⋃ n, u ∩ (Set.univ.pi fun i => spanningSets (μ i) n) = u := by
    rw [← Set.inter_iUnion]
    have hcov : ⋃ n, (Set.univ.pi fun i => spanningSets (μ i) n) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : ∀ i, ∃ m, x i ∈ spanningSets (μ i) m := fun i =>
        Set.mem_iUnion.1 (by rw [iUnion_spanningSets]; trivial)
      choose m hm using hx
      exact Set.mem_iUnion.2 ⟨Finset.univ.sup m, fun i _ =>
        monotone_spanningSets (μ i) (Finset.le_sup (Finset.mem_univ i)) (hm i)⟩
    rw [hcov, Set.inter_univ]
  have htend := tendsto_setIntegral_of_monotone (fun n => hu.inter (hboxm n)) hmono
    (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
  rw [hcover] at htend
  simp only [hb] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- **Completeness of the tensor family.** The tensors built from coordinatewise Hilbert bases have
trivial orthogonal complement in `L²(Measure.pi μ)`. -/
theorem orthogonal_span_range_L2piMul_eq_bot {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) :
    (Submodule.span 𝕜 (Set.range fun k : ∀ i, κ i => L2piMul fun i => b i (k i)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh => ?_
  rw [Submodule.mem_orthogonal] at hh
  have hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0 := by
    intro F
    rw [inner_eq_zero_symm]
    refine inner_L2piMul_eq_zero_of_forall_basis b (fun k => ?_) F
    rw [inner_eq_zero_symm]
    exact hh _ (Submodule.subset_span ⟨k, rfl⟩)
  have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero h (by norm_num) (by norm_num)
    (fun s _ hs' => integrableOn_Lp_of_measure_ne_top h one_le_two hs'.ne)
    (fun s hs hs' => setIntegral_eq_zero_of_forall_inner_pi hz s hs hs')
  rw [Lp.ext_iff]
  exact hae.trans (Lp.coeFn_zero 𝕜 2 (Measure.pi μ)).symm

/-- **The `Fintype`-indexed product Hilbert basis.** Pointwise products of coordinatewise Hilbert
bases form a Hilbert basis of `L²(Measure.pi μ)`, indexed by the dependent function type. -/
noncomputable def piHilbertBasis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) :
    HilbertBasis (∀ i, κ i) 𝕜 (Lp 𝕜 2 (Measure.pi μ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_L2piMul fun i => (b i).orthonormal)
    (orthogonal_span_range_L2piMul_eq_bot b)

/-- The `k`-th vector of `piHilbertBasis` is the tensor of the `k i`-th basis vectors. -/
@[simp]
theorem piHilbertBasis_apply {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) (k : ∀ i, κ i) :
    piHilbertBasis b k = L2piMul fun i => b i (k i) := by
  rw [piHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The `k`-th vector of `piHilbertBasis` is a.e. the pointwise product `∏ i, b i (k i)`. -/
theorem coeFn_piHilbertBasis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) (k : ∀ i, κ i) :
    ⇑(piHilbertBasis b k) =ᵐ[Measure.pi μ] fun x : ∀ i, α i => ∏ i, b i (k i) (x i) := by
  rw [piHilbertBasis_apply]
  exact coeFn_L2piMul _

end TauCeti
