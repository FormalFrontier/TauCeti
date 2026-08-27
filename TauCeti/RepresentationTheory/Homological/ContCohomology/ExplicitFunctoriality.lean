/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Functoriality of explicit continuous cohomology in degrees one and two

A compatible pair consists of a continuous monoid homomorphism `φ : H →ₜ* G` and a continuous
additive homomorphism `f : M →+ N` satisfying
`f (φ h • m) = h • f m`. It pulls a continuous cochain `c : G → M` back to
`h ↦ f (c (φ h))`. This file proves that pullback preserves continuous cocycles and
coboundaries, and descends it to the roadmap's explicit groups `H¹ = Z¹/B¹` and `H² = Z²/B²`.

The resulting maps are `TauCeti.ContCohomology.explicitMap1` and `explicitMap2`. Their identity
and composition laws make the construction genuinely functorial, while the `_mk` theorems fix
their values on cocycle classes. The named specializations `explicitRes1`, `explicitRes2`,
`explicitCoeff1`, and `explicitCoeff2` provide restriction and coefficient maps in positive
degrees.

This is functoriality of the *explicit* model: the carriers are the quotients `Z¹/B¹` and `Z²/B²`
of plain continuous cochains. Mathlib's `ContinuousCohomology.map` is the compatible-pair pullback
on the canonical bundled carrier, and it is what the sibling file
`TauCeti/RepresentationTheory/Homological/ContCohomology/Functoriality.lean` specialises to
restriction, inflation and coefficient maps; the two pullbacks are compared in Layer 3 of the
roadmap, once the explicit complex is identified with the canonical one.

This implements the positive-degree part of the "compatible-pair functoriality" and "three named
instances" milestones in Layer 2 of `TauCetiRoadmap/ProfiniteCohomology/README.md`. The formulas
follow Mathlib's `groupCohomology.cochainsMap₁`, `cochainsMap₂`, `mapCocycles₁`, and
`mapCocycles₂`, but are stated for the roadmap's universe-polymorphic unbundled continuous
modules.
-/

public section

namespace TauCeti.ContCohomology

universe uG uH uM uN uK uP

section Cochains

variable {G : Type uG} {H : Type uH} {M : Type uM} {N : Type uN}
  [Monoid G] [Monoid H] [AddMonoid M] [AddMonoid N]

/-- Pullback of degree-one cochains along a monoid map and a coefficient map. -/
def cochainsMap1 (φ : H →* G) (f : M →+ N) : (G → M) →+ (H → N) where
  toFun c h := f (c (φ h))
  map_zero' := by
    ext h
    simp
  map_add' c d := by
    ext h
    simp

/-- Pullback of degree-two cochains along a monoid map and a coefficient map: the degree-one
pullback along the pair `φ × φ` of the domain. -/
def cochainsMap2 (φ : H →* G) (f : M →+ N) : (G × G → M) →+ (H × H → N) :=
  cochainsMap1 (φ.prodMap φ) f

/-- The defining formula for the degree-one cochain pullback. -/
@[simp]
theorem cochainsMap1_apply (φ : H →* G) (f : M →+ N) (c : G → M) (h : H) :
    cochainsMap1 φ f c h = f (c (φ h)) :=
  by rfl

/-- The defining formula for the degree-two cochain pullback. -/
@[simp]
theorem cochainsMap2_apply (φ : H →* G) (f : M →+ N) (c : G × G → M) (h k : H) :
    cochainsMap2 φ f c (h, k) = f (c (φ h, φ k)) :=
  by rfl

/-- Pullback preserves continuity of degree-one cochains. -/
theorem continuous_cochainsMap1 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    {c : G → M} (hc : Continuous c) : Continuous (cochainsMap1 (φ : H →* G) f c) :=
  hf.comp (hc.comp φ.continuous)

/-- Pullback preserves continuity of degree-two cochains. -/
theorem continuous_cochainsMap2 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    {c : G × G → M} (hc : Continuous c) : Continuous (cochainsMap2 (φ : H →* G) f c) :=
  continuous_cochainsMap1 (φ.prodMap φ) f hf hc

/-- Pullback of degree-one cochains along the identity compatible pair is the identity. -/
@[simp]
theorem cochainsMap1_id :
    cochainsMap1 (MonoidHom.id G) (AddMonoidHom.id M) =
      AddMonoidHom.id (G → M) := by
  ext c g
  rfl

/-- Pullback of degree-two cochains along the identity compatible pair is the identity. -/
@[simp]
theorem cochainsMap2_id :
    cochainsMap2 (MonoidHom.id G) (AddMonoidHom.id M) =
      AddMonoidHom.id (G × G → M) :=
  cochainsMap1_id

/-- Pullback of degree-one cochains along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map. -/
@[simp]
theorem cochainsMap1_comp {K : Type uK} {P : Type uP} [Monoid K] [AddMonoid P]
    (φ : H →* G) (ψ : K →* H) (f : M →+ N) (q : N →+ P) :
    cochainsMap1 (φ.comp ψ) (q.comp f) = (cochainsMap1 ψ q).comp (cochainsMap1 φ f) := by
  ext c k
  rfl

/-- Pullback of degree-two cochains along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map. -/
@[simp]
theorem cochainsMap2_comp {K : Type uK} {P : Type uP} [Monoid K] [AddMonoid P]
    (φ : H →* G) (ψ : K →* H) (f : M →+ N) (q : N →+ P) :
    cochainsMap2 (φ.comp ψ) (q.comp f) = (cochainsMap2 ψ q).comp (cochainsMap2 φ f) :=
  cochainsMap1_comp (φ.prodMap φ) (ψ.prodMap ψ) f q

end Cochains

section Naturality

/-! The naturality squares are where the differentials enter, so this is the first point at which
the coefficients have to be commutative groups carrying a distributive scalar action. Commutativity
is necessary because `d0` and `d1` are additive homomorphisms; their formulas are not additive for
a general noncommutative additive group. -/

variable {G : Type uG} {H : Type uH} {M : Type uM} {N : Type uN}
  [Monoid G] [Monoid H] [AddCommGroup M] [AddCommGroup N]
  [DistribSMul G M] [DistribSMul H N]

/-- The degree-zero differential is natural in compatible pairs. -/
theorem cochainsMap1_d0 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (m : M) :
    cochainsMap1 φ f (d0 G M m) = d0 H N (f m) := by
  ext h
  simp only [cochainsMap1_apply, d0_apply, map_sub, hequiv]

/-- The degree-one differential is natural in compatible pairs. -/
theorem cochainsMap2_d1 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : G → M) :
    cochainsMap2 φ f (d1 G M c) = d1 H N (cochainsMap1 φ f c) := by
  ext p
  obtain ⟨h, k⟩ := p
  simp only [cochainsMap2_apply, d1_apply, map_add, map_sub, hequiv, cochainsMap1_apply,
    map_mul]

/-- A compatible pair sends degree-one coboundaries to degree-one coboundaries. -/
theorem cochainsMap1_mem_B1 (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G → M} (hc : c ∈ B1 G M) :
    cochainsMap1 φ f c ∈ B1 H N := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hc
  refine mem_B1_iff.2 ⟨f m, fun h => ?_⟩
  rw [cochainsMap1_apply, ← hm (φ h), map_sub, hequiv]

/-- A compatible pair sends continuous degree-two coboundaries to continuous degree-two
coboundaries. -/
theorem cochainsMap2_mem_B2 [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalAddGroup M]
    [IsTopologicalAddGroup N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : Continuous f) (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G × G → M} (hc : c ∈ B2 G M) :
    cochainsMap2 (φ : H →* G) f c ∈ B2 H N := by
  obtain ⟨b, hb, rfl⟩ := mem_B2_iff.1 hc
  refine mem_B2_iff.2 ⟨cochainsMap1 (φ : H →* G) f b,
    continuous_cochainsMap1 φ f hf hb, ?_⟩
  exact (cochainsMap2_d1 (φ : H →* G) f hequiv b).symm

end Naturality

/-- Compatible coefficient maps remain compatible after composition: this is the compatibility
hypothesis of the composite pair `(φ.comp ψ, q.comp f)`. -/
theorem comp_apply_smul
    {G : Type uG} {H : Type uH} {K : Type uK}
    [Monoid G] [Monoid H] [Monoid K]
    {M : Type uM} {N : Type uN} {P : Type uP}
    [AddMonoid M] [AddMonoid N] [AddMonoid P]
    [SMul G M] [SMul H N] [SMul K P]
    (φ : H →* G) (ψ : K →* H) (f : M →+ N) (q : N →+ P)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (hq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) (k : K) (m : M) :
    (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m := by
  simp only [MonoidHom.comp_apply, AddMonoidHom.comp_apply, hf, hq]

section Cocycles

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]
  (H : Type uH) [Monoid H] [TopologicalSpace H]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N]

/-- A compatible pair sends continuous degree-one cocycles to continuous degree-one cocycles. -/
theorem cochainsMap1_mem_Z1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) {c : G → M} (hc : c ∈ Z1 G M) :
    cochainsMap1 (φ : H →* G) f c ∈ Z1 H N := by
  refine mem_Z1_iff.2 ⟨continuous_cochainsMap1 φ f hf (mem_Z1_iff.1 hc).1,
    d1_apply_eq_zero_iff.1 ?_⟩
  rw [← cochainsMap2_d1 (φ : H →* G) f hequiv, d1_apply_eq_zero_iff.2 (mem_Z1_iff.1 hc).2,
    map_zero]

/-- A compatible pair sends continuous degree-two cocycles to continuous degree-two cocycles. -/
theorem cochainsMap2_mem_Z2 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    {c : G × G → M} (hc : c ∈ Z2 G M) :
    cochainsMap2 (φ : H →* G) f c ∈ Z2 H N := by
  refine mem_Z2_iff.2 ⟨continuous_cochainsMap2 φ f hf (mem_Z2_iff.1 hc).1, ?_⟩
  intro h k j
  simp only [cochainsMap2_apply, map_mul]
  rw [← hequiv h, ← map_add, ← map_add]
  exact congrArg f ((mem_Z2_iff.1 hc).2 ((φ : H →* G) h) ((φ : H →* G) k)
    ((φ : H →* G) j))

/-- The pullback of continuous degree-one cocycles along a compatible pair, sending a cocycle `c`
to `h ↦ f (c (φ h))`. -/
def cocyclesMap1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : Z1 G M →+ Z1 H N :=
  AddMonoidHom.codRestrict ((cochainsMap1 (φ : H →* G) f).domRestrict (Z1 G M))
    (Z1 H N) fun c => cochainsMap1_mem_Z1 G M H N φ f hf hequiv c.property

/-- The underlying cochain of `cocyclesMap1` is the degree-one cochain pullback. -/
@[simp]
theorem cocyclesMap1_coe (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) :
    (cocyclesMap1 G M H N φ f hf hequiv c : H → N) = cochainsMap1 (φ : H →* G) f c := by
  ext h
  rfl

/-- The defining formula for the degree-one cocycle pullback, the pointwise form of
`cocyclesMap1_coe`. -/
theorem cocyclesMap1_apply (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) (h : H) :
    (cocyclesMap1 G M H N φ f hf hequiv c : H → N) h =
      f ((c : G → M) (φ h)) :=
  by rfl

/-- Pullback of continuous cocycles along the identity compatible pair is the identity. -/
@[simp]
theorem cocyclesMap1_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m) :
    cocyclesMap1 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  ext c g
  simp only [cocyclesMap1_apply, ContinuousMonoidHom.coe_id, id_eq, AddMonoidHom.id_apply]

/-- Pullback of continuous cocycles along a composite compatible pair is the composite of the
pullbacks: it is contravariant in the group homomorphism and covariant in the coefficient map.
The compatibility hypothesis `hcomp` of the composite pair is supplied by `comp_apply_smul`. -/
theorem cocyclesMap1_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m) :
    cocyclesMap1 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (cocyclesMap1 H N K P ψ q hq hequivq).comp
        (cocyclesMap1 G M H N φ f hf hequiv) := by
  ext c k
  simp only [cocyclesMap1_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]

/-- The pullback of continuous degree-two cocycles along a compatible pair. -/
def cocyclesMap2 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : Z2 G M →+ Z2 H N :=
  AddMonoidHom.codRestrict ((cochainsMap2 (φ : H →* G) f).domRestrict (Z2 G M))
    (Z2 H N) fun c => cochainsMap2_mem_Z2 G M H N φ f hf hequiv c.property

/-- The underlying cochain of `cocyclesMap2` is the degree-two cochain pullback. -/
@[simp]
theorem cocyclesMap2_coe (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    (cocyclesMap2 G M H N φ f hf hequiv c : H × H → N) =
      cochainsMap2 (φ : H →* G) f c := by
  ext p
  rfl

/-- The defining formula for the degree-two cocycle pullback. -/
theorem cocyclesMap2_apply (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (c : Z2 G M) (h k : H) :
    (cocyclesMap2 G M H N φ f hf hequiv c : H × H → N) (h, k) =
      f ((c : G × G → M) (φ h, φ k)) :=
  by rfl

/-- Pullback of continuous degree-two cocycles along the identity compatible pair is the
identity. -/
@[simp]
theorem cocyclesMap2_id :
    cocyclesMap2 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id
      (fun g m => by simp) =
      AddMonoidHom.id _ := by
  ext c p
  obtain ⟨g, h⟩ := p
  simp only [cocyclesMap2_apply, ContinuousMonoidHom.coe_id, id_eq, AddMonoidHom.id_apply]

/-- Pullback of continuous degree-two cocycles respects composition of compatible pairs. -/
theorem cocyclesMap2_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) :
    cocyclesMap2 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf)
      (fun k m => by
        exact comp_apply_smul (φ : H →* G) (ψ : K →* H) f q hequiv hequivq k m) =
      (cocyclesMap2 H N K P ψ q hq hequivq).comp
        (cocyclesMap2 G M H N φ f hf hequiv) := by
  ext c p
  obtain ⟨k, l⟩ := p
  simp only [cocyclesMap2_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]

end Cocycles

section Cohomology

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (H : Type uH) [Monoid H] [TopologicalSpace H]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- Pullback on the explicit first continuous cohomology group along a compatible pair. -/
noncomputable def explicitMap1 (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : H1 G M →+ H1 H N :=
  QuotientAddGroup.map ((B1 G M).addSubgroupOf (Z1 G M))
    ((B1 H N).addSubgroupOf (Z1 H N)) (cocyclesMap1 G M H N φ f hf hequiv)
    fun _ hc => cochainsMap1_mem_B1 (φ : H →* G) f hequiv hc

/-- `explicitMap1` sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem explicitMap1_mk (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) :
    explicitMap1 G M H N φ f hf hequiv (c : H1 G M) =
      (cocyclesMap1 G M H N φ f hf hequiv c : H1 H N) :=
  QuotientAddGroup.map_mk _ _ _ _ c

/-- Pullback by the identity compatible pair is the identity on explicit `H¹`. -/
@[simp]
theorem explicitMap1_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m) :
    explicitMap1 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id hid =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap1_mk, AddMonoidHom.id_apply]
      exact congrArg (fun z : Z1 G M => (z : H1 G M))
        (DFunLike.congr_fun (cocyclesMap1_id G M hid) c)

/-- Pullback on explicit `H¹` respects composition of compatible pairs: it is contravariant in the
group homomorphism and covariant in the coefficient map. The compatibility hypothesis `hcomp` of
the composite pair is supplied by `comp_apply_smul`. -/
theorem explicitMap1_comp
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n)
    (hcomp : ∀ (k : K) (m : M), (q.comp f) ((φ.comp ψ) k • m) = k • (q.comp f) m) :
    explicitMap1 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf) hcomp =
      (explicitMap1 H N K P ψ q hq hequivq).comp
        (explicitMap1 G M H N φ f hf hequiv) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap1_mk, AddMonoidHom.comp_apply, explicitMap1_mk, explicitMap1_mk]
      exact congrArg (fun z : Z1 K P => (z : H1 K P))
        (DFunLike.congr_fun
          (cocyclesMap1_comp G M H N φ f hf hequiv K P ψ q hq hequivq hcomp) c)

/-- Pullback on the explicit second continuous cohomology group along a compatible pair. -/
noncomputable def explicitMap2 [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) : H2 G M →+ H2 H N :=
  QuotientAddGroup.map ((B2 G M).addSubgroupOf (Z2 G M))
    ((B2 H N).addSubgroupOf (Z2 H N)) (cocyclesMap2 G M H N φ f hf hequiv)
    fun _ hc => cochainsMap2_mem_B2 (φ := φ) f hf hequiv hc

/-- `explicitMap2` sends the class of a cocycle to the class of its pullback. -/
@[simp]
theorem explicitMap2_mk [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    explicitMap2 G M H N φ f hf hequiv (c : H2 G M) =
      (cocyclesMap2 G M H N φ f hf hequiv c : H2 H N) :=
  QuotientAddGroup.map_mk _ _ _ _ c

/-- Pullback by the identity compatible pair is the identity on explicit `H²`. -/
@[simp]
theorem explicitMap2_id [ContinuousMul G] :
    explicitMap2 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) continuous_id
      (fun g m => by simp) =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap2_mk, AddMonoidHom.id_apply]
      exact congrArg (fun z : Z2 G M => (z : H2 G M))
        (DFunLike.congr_fun (cocyclesMap2_id G M) c)

/-- Pullback on explicit `H²` respects composition of compatible pairs. -/
theorem explicitMap2_comp
    [ContinuousMul G] [ContinuousMul H]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K : Type uK) [Monoid K] [TopologicalSpace K] [ContinuousMul K]
    (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : Continuous q)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) :
    explicitMap2 G M K P (φ.comp ψ) (q.comp f) (hq.comp hf)
      (fun k m => by
        exact comp_apply_smul (φ : H →* G) (ψ : K →* H) f q hequiv hequivq k m) =
      (explicitMap2 H N K P ψ q hq hequivq).comp
        (explicitMap2 G M H N φ f hf hequiv) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitMap2_mk, AddMonoidHom.comp_apply, explicitMap2_mk, explicitMap2_mk]
      exact congrArg (fun z : Z2 K P => (z : H2 K P))
        (DFunLike.congr_fun
          (cocyclesMap2_comp G M H N φ f hf hequiv K P ψ q hq hequivq) c)

end Cohomology

section NamedMaps

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Restriction on explicit `H¹`, induced by the subgroup inclusion and the identity coefficient
map. -/
noncomputable def explicitRes1 (S : Subgroup G) : H1 G M →+ H1 S M :=
  explicitMap1 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    continuous_id fun _ _ => rfl

/-- Restriction sends the class of a continuous `1`-cocycle to the class of its restriction. -/
@[simp]
theorem explicitRes1_mk (S : Subgroup G) (c : Z1 G M) :
    explicitRes1 G M S (c : H1 G M) =
      (cocyclesMap1 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (fun _ _ => rfl) c : H1 S M) :=
  explicitMap1_mk G M S M _ _ _ _ c

/-- Restricting explicit `H¹` first to `S` and then to a subgroup `T` of `S` is restriction
along the composite inclusion. -/
theorem explicitRes1_comp (S : Subgroup G) (T : Subgroup S) :
    (explicitRes1 S M T).comp (explicitRes1 G M S) =
      explicitMap1 G M T M
        ((ContinuousMonoidHom.subgroupSubtype S).comp
          (ContinuousMonoidHom.subgroupSubtype T))
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) := by
  exact (explicitMap1_comp G M S M (ContinuousMonoidHom.subgroupSubtype S)
    (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) T M
    (ContinuousMonoidHom.subgroupSubtype T) (AddMonoidHom.id M) continuous_id
    (fun _ _ => rfl) (fun _ _ => rfl)).symm

/-- Restriction on explicit `H²`, induced by the subgroup inclusion and the identity coefficient
map. -/
noncomputable def explicitRes2 (S : Subgroup G) [ContinuousMul G] [ContinuousMul S] :
    H2 G M →+ H2 S M :=
  explicitMap2 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    continuous_id fun _ _ => rfl

/-- Restriction sends the class of a continuous `2`-cocycle to the class of its restriction. -/
@[simp]
theorem explicitRes2_mk (S : Subgroup G) [ContinuousMul G] [ContinuousMul S] (c : Z2 G M) :
    explicitRes2 G M S (c : H2 G M) =
      (cocyclesMap2 G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
        continuous_id (fun _ _ => rfl) c : H2 S M) :=
  explicitMap2_mk G M S M _ _ _ _ c

/-- Restricting explicit `H²` first to `S` and then to a subgroup `T` of `S` is restriction
along the composite inclusion. -/
theorem explicitRes2_comp (S : Subgroup G) (T : Subgroup S)
    [ContinuousMul G] [ContinuousMul S] [ContinuousMul T] :
    (explicitRes2 S M T).comp (explicitRes2 G M S) =
      explicitMap2 G M T M
        ((ContinuousMonoidHom.subgroupSubtype S).comp
          (ContinuousMonoidHom.subgroupSubtype T))
        (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) := by
  exact (explicitMap2_comp G M S M (ContinuousMonoidHom.subgroupSubtype S)
    (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) T M
    (ContinuousMonoidHom.subgroupSubtype T) (AddMonoidHom.id M) continuous_id
    (fun _ _ => rfl)).symm

/-- The coefficient map on explicit `H¹` induced by a continuous equivariant additive
homomorphism. -/
noncomputable def explicitCoeff1 {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) : H1 G M →+ H1 G N :=
  explicitMap1 G M G N (ContinuousMonoidHom.id G) f hf fun g m => f.map_smul g m

/-- A coefficient map sends a `1`-cocycle class to the class obtained by postcomposition. -/
@[simp]
theorem explicitCoeff1_mk {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) (c : Z1 G M) :
    explicitCoeff1 G M f hf (c : H1 G M) =
      (cocyclesMap1 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => f.map_smul g m) c : H1 G N) :=
  explicitMap1_mk G M G N _ _ _ _ c

/-- The identity coefficient map induces the identity on explicit `H¹`. -/
@[simp]
theorem explicitCoeff1_id :
    explicitCoeff1 G M (DistribMulActionHom.id G) continuous_id = AddMonoidHom.id _ :=
  explicitMap1_id G M fun _ _ => rfl

/-- Coefficient maps on explicit `H¹` respect composition. -/
theorem explicitCoeff1_comp {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
    (f : M →+[G] N) (q : N →+[G] P) (hf : Continuous f) (hq : Continuous q) :
    explicitCoeff1 G M (q.comp f) (hq.comp hf) =
      (explicitCoeff1 G N q hq).comp (explicitCoeff1 G M f hf) := by
  -- The generic law writes the two identity group maps as their composite and the coefficient
  -- maps as unbundled additive homomorphisms; extensionality identifies those wrappers.
  convert explicitMap1_comp G M G N (ContinuousMonoidHom.id G) f hf
    (fun g m => f.map_smul g m) G P (ContinuousMonoidHom.id G) q hq
    (fun g n => q.map_smul g n) (fun g m => (q.comp f).map_smul g m) using 1 <;>
    ext <;> rfl

/-- The coefficient map on explicit `H²` induced by a continuous equivariant additive
homomorphism. -/
noncomputable def explicitCoeff2 [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) : H2 G M →+ H2 G N :=
  explicitMap2 G M G N (ContinuousMonoidHom.id G) f hf fun g m => f.map_smul g m

/-- A coefficient map sends a `2`-cocycle class to the class obtained by postcomposition. -/
@[simp]
theorem explicitCoeff2_mk [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) (c : Z2 G M) :
    explicitCoeff2 G M f hf (c : H2 G M) =
      (cocyclesMap2 G M G N (ContinuousMonoidHom.id G) f hf
        (fun g m => f.map_smul g m) c : H2 G N) :=
  explicitMap2_mk G M G N _ _ _ _ c

/-- The identity coefficient map induces the identity on explicit `H²`. -/
@[simp]
theorem explicitCoeff2_id [ContinuousMul G] :
    explicitCoeff2 G M (DistribMulActionHom.id G) continuous_id = AddMonoidHom.id _ :=
  explicitMap2_id G M

/-- Coefficient maps on explicit `H²` respect composition. -/
theorem explicitCoeff2_comp [ContinuousMul G]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction G N] [ContinuousSMul G N]
    {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
    (f : M →+[G] N) (q : N →+[G] P) (hf : Continuous f) (hq : Continuous q) :
    explicitCoeff2 G M (q.comp f) (hq.comp hf) =
      (explicitCoeff2 G N q hq).comp (explicitCoeff2 G M f hf) := by
  -- As in degree one, extensionality identifies the generic compatible-pair composites with the
  -- identity group map and the bundled composite coefficient map.
  convert explicitMap2_comp G M G N (ContinuousMonoidHom.id G) f hf
    (fun g m => f.map_smul g m) G P (ContinuousMonoidHom.id G) q hq
    (fun g n => q.map_smul g n) using 1 <;>
    ext <;> rfl

end NamedMaps

end TauCeti.ContCohomology
