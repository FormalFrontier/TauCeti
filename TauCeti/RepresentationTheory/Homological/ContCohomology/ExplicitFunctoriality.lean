/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Functoriality of explicit continuous cohomology in degree one

A compatible pair consists of a continuous monoid homomorphism `φ : H →ₜ* G` and a continuous
additive homomorphism `f : M →+ N` satisfying
`f (φ h • m) = h • f m`. It pulls a continuous cochain `c : G → M` back to
`h ↦ f (c (φ h))`. This file proves that pullback preserves continuous cocycles and
coboundaries, and descends it to the roadmap's explicit group `H¹ = Z¹/B¹`.

The resulting map is `TauCeti.ContCohomology.explicitMap1`. Its identity and composition laws
make the construction genuinely functorial, while `explicitMap1_mk` fixes its value on a cocycle
class. The cochain maps in degrees one and two are exposed because degree-two functoriality uses
the same naturality square for `d¹`.

This is functoriality of the *explicit* model: the carrier is the quotient `Z¹/B¹` of plain
continuous cochains. Mathlib's `ContinuousCohomology.map` is the compatible-pair pullback on the
canonical bundled carrier, and it is what the sibling file
`TauCeti/RepresentationTheory/Homological/ContCohomology/Functoriality.lean` specialises to
restriction, inflation and coefficient maps; the two pullbacks are compared in Layer 3 of the
roadmap, once the explicit complex is identified with the canonical one.

This implements the degree-one part of the "compatible-pair functoriality" milestone in Layer 2
of `TauCetiRoadmap/ProfiniteCohomology/README.md`. The formulas follow Mathlib's
`groupCohomology.cochainsMap₁`, `cochainsMap₂`, and `mapCocycles₁`, but are stated for the
roadmap's universe-polymorphic unbundled continuous modules.
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

end Cohomology

end TauCeti.ContCohomology
