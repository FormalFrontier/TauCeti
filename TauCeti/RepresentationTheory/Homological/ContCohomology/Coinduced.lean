/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import TauCeti.Topology.Algebra.Group.ProfiniteSection

/-!
# The coinduced discrete module of a subgroup

For a topological group `G`, a subgroup `U` and a `U`-module `A`, the **coinduced module**
```
Coind_U^G A = {f : G → A | f locally constant, f (u * g) = u • f g for all u ∈ U, g ∈ G}
```
carries the right-translation action `(g • f) x = f (x * g)` of `G`. It is Milne's `M_*`
(*Arithmetic Duality Theorems*, Remark 0.11) and Ribes-Zalesskii's `Coind_U^G`
(*Profinite Groups*, Thm. 6.10.5), and it is the coefficient module Shapiro's lemma is stated
against.

This file builds `TauCeti.coind` and the properties Shapiro's lemma and the dimension-shifting
argument consume:

* it is a `G`-module (`TauCeti.instDistribMulActionCoind`) whose right-translation stabilizers are
  open for compact `G` (`TauCeti.isOpen_stabilizer_coind`), which is exactly what makes it a
  *discrete* `G`-module in the sense of a continuous action on a discrete module;
* it is functorial in `A` along `U`-equivariant additive maps (`TauCeti.coindMap`), the counit
  being evaluation at `1` (`TauCeti.coindEval`);
* it is **exact** in `A`: `TauCeti.coindMap_injective`, `TauCeti.coindMap_surjective` and
  `TauCeti.coindMap_range_eq_ker` send a short exact sequence of discrete `U`-modules to a short
  exact sequence;
* the two degenerate subgroups are computed: `TauCeti.mem_coind_bot_iff` characterizes membership
  in `Coind_1^G A` as local constancy, so it is the group of all locally constant maps `G → A`,
  the acyclic module of the dimension-shifting argument, and
  `TauCeti.coindEvalTopEquiv` says `Coind_G^G A` is `A`.

Surjectivity is where the topology does real work. Lifting a locally constant `U`-equivariant map
`G → B` through a surjection `A ↠ B` means choosing preimages coherently along the right cosets
`U \ G`, and the choice has to stay locally constant. Layer 0's continuous section of `G → G ⧸ U`
(`TauCeti.exists_continuous_section`, Ribes-Zalesskii Prop. 2.2.2) supplies it: inverting turns a
continuous section of the *left* coset space into a continuous choice `s'` of representatives of
the *right* cosets, and `g ↦ g * (s' g)⁻¹` is then a continuous `U`-valued cocycle by which the
lift is transported. Discreteness of `A` and continuity of the `U`-action are what make the
transported lift locally constant again.

## Implementation notes

Mathlib's `ContRepresentation.coindV` is the same construction in the bundled continuous-
representation language: in this file's notation, a `Submodule R C(G, V)` attached to a
`ContRepresentation R U V` and the inclusion `U → G`. It is not used here because the
`ContRepresentation` carrier imposes no continuity of the action in the group variable, which is
needed by the topology-dependent results `TauCeti.coindMap_surjective` and
`TauCeti.coindEvalTopEquiv`, and because the roadmap fixes the unbundled classes
`[DistribMulAction U A]`, `[DiscreteTopology A]`, `[ContinuousSMul U A]` for this layer, with local
constancy as a predicate on plain functions rather than a bundled `C(G, A)`. Transporting `coind`
into the bundled language is a separate step, and belongs with the smooth-discrete dictionary that
owns that translation.

This is the "coinduced module" milestone of Layer 7 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`.
-/

public section

namespace TauCeti

section Defs

variable (G : Type*) [Group G] [TopologicalSpace G] (U : Subgroup G)
  (A : Type*) [AddCommGroup A] [DistribMulAction U A]

/-- The **coinduced module** `Coind_U^G A` of a subgroup `U ≤ G` and a `U`-module `A`: the locally
constant maps `f : G → A` with `f (u * g) = u • f g` for every `u : U` and `g : G`. The
`G`-action is right translation, `(g • f) x = f (x * g)`. -/
def coind : AddSubgroup (G → A) where
  carrier := {f | IsLocallyConstant f ∧ ∀ (u : U) (g : G), f ((u : G) * g) = u • f g}
  add_mem' {a b} ha hb :=
    ⟨(ha.1.prodMk hb.1).comp fun p => p.1 + p.2, fun u g => by
      simp [ha.2 u g, hb.2 u g, smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun u g => by simp⟩
  neg_mem' {a} ha := ⟨ha.1.comp fun x => -x, fun u g => by simp [ha.2 u g, smul_neg]⟩

variable {G U A}

theorem mem_coind_iff {f : G → A} :
    f ∈ coind G U A ↔
      IsLocallyConstant f ∧ ∀ (u : U) (g : G), f ((u : G) * g) = u • f g := Iff.rfl

/-- A member of the coinduced module is locally constant. -/
theorem isLocallyConstant_of_mem_coind {f : G → A} (hf : f ∈ coind G U A) :
    IsLocallyConstant f := hf.1

/-- A member of the coinduced module is `U`-equivariant. -/
theorem apply_mul_of_mem_coind {f : G → A} (hf : f ∈ coind G U A) (u : U) (g : G) :
    f ((u : G) * g) = u • f g := hf.2 u g

/-- The equivariance of a bundled element of the coinduced module, in the form `simp` can use
without a separate membership hypothesis. -/
@[simp]
theorem coind_apply_mul (f : coind G U A) (u : U) (g : G) :
    (f : G → A) ((u : G) * g) = u • (f : G → A) g := apply_mul_of_mem_coind f.2 u g

end Defs

section Action

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  {A : Type*} [AddCommGroup A] [DistribMulAction U A]

theorem rightTranslation_mem_coind {f : G → A} (hf : f ∈ coind G U A) (g : G) :
    (fun x : G => f (x * g)) ∈ coind G U A :=
  ⟨(isLocallyConstant_of_mem_coind hf).comp_continuous (continuous_mul_const g),
    fun u x => by simpa [mul_assoc] using apply_mul_of_mem_coind hf u (x * g)⟩

instance instSMulCoind : SMul G (coind G U A) where
  smul g f := ⟨fun x => (f : G → A) (x * g), rightTranslation_mem_coind f.2 g⟩

@[simp]
theorem coind_smul_apply (g : G) (f : coind G U A) (x : G) :
    ((g • f : coind G U A) : G → A) x = (f : G → A) (x * g) := rfl

instance instDistribMulActionCoind : DistribMulAction G (coind G U A) where
  one_smul f := by ext x; simp
  mul_smul g g' f := by ext x; simp [mul_assoc]
  smul_zero g := by ext x; simp
  smul_add g f f' := by ext x; simp

/-- The `G`-stabilizer of a coinduced element is its right-translation stabilizer. -/
theorem stabilizer_coind_eq (f : coind G U A) :
    MulAction.stabilizer G f = rightTranslationStabilizer (f : G → A) := by
  ext g
  rw [mem_rightTranslationStabilizer]
  exact ⟨fun h x => congrFun (Subtype.ext_iff.mp h) x,
    fun h => Subtype.ext (funext fun x => h x)⟩

end Action

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [CompactSpace G]
  {U : Subgroup G} {A : Type*} [AddCommGroup A] [DistribMulAction U A]

/-- **The coinduced module of a compact group is a discrete `G`-module**: every stabilizer of the
right-translation action is open. This is uniform local constancy
(`TauCeti.isOpen_rightTranslationStabilizer`), and it is the reason the coinduced module can be
used as coefficients for continuous cohomology. -/
theorem isOpen_stabilizer_coind (f : coind G U A) :
    IsOpen (MulAction.stabilizer G f : Set G) := by
  rw [stabilizer_coind_eq]
  exact isOpen_rightTranslationStabilizer (isLocallyConstant_of_mem_coind f.2)

end Smooth

section Functoriality

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A B C : Type*} [AddCommGroup A] [DistribMulAction U A] [AddCommGroup B]
  [DistribMulAction U B] [AddCommGroup C] [DistribMulAction U C]

variable (G U) in
/-- **Evaluation at `1`**, the counit of coinduction: `Coind_U^G A →+ A`. It is `U`-equivariant
(`TauCeti.coindEval_smul`) and natural in `A` (`TauCeti.coindEval_coindMap`). -/
def coindEval : coind G U A →+ A where
  toFun f := (f : G → A) 1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coindEval_apply (f : coind G U A) : coindEval G U f = (f : G → A) 1 := (rfl)

/-- The counit is `U`-equivariant for the restriction of the right-translation action. -/
theorem coindEval_smul [ContinuousMul G] (u : U) (f : coind G U A) :
    coindEval G U ((u : G) • f) = u • coindEval G U f := by
  simpa using apply_mul_of_mem_coind f.2 u 1

variable (G U) in
/-- **Coinduction is functorial in the coefficients**: a `U`-equivariant additive map `φ : A →+ B`
induces `Coind_U^G A →+ Coind_U^G B` by postcomposition. -/
def coindMap (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) :
    coind G U A →+ coind G U B where
  toFun f := ⟨fun g => φ ((f : G → A) g),
    ⟨(isLocallyConstant_of_mem_coind f.2).comp φ, fun u g => by simp [hφ]⟩⟩
  map_zero' := by ext g; simp
  map_add' _ _ := by ext g; simp

@[simp]
theorem coindMap_apply (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (f : coind G U A) (g : G) :
    ((coindMap G U φ hφ f : coind G U B) : G → B) g = φ ((f : G → A) g) := (rfl)

/-- Coinduction of the identity is the identity. -/
@[simp]
theorem coindMap_id : coindMap G U (AddMonoidHom.id A) (fun _ _ => rfl) = AddMonoidHom.id _ := by
  ext f g; simp

/-- Coinduction of a composite is the composite of the coinductions. -/
@[simp]
theorem coindMap_comp (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (ψ : B →+ C) (hψ : ∀ (u : U) (b : B), ψ (u • b) = u • ψ b) :
    coindMap G U (ψ.comp φ) (fun u a => by rw [AddMonoidHom.comp_apply, hφ, hψ]; rfl) =
      (coindMap G U ψ hψ).comp (coindMap G U φ hφ) := by
  ext f g; simp

/-- The counit is natural in the coefficients. -/
theorem coindEval_coindMap (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (f : coind G U A) : coindEval G U (coindMap G U φ hφ f) = φ (coindEval G U f) := (rfl)

/-- `coindMap` is `G`-equivariant. -/
@[simp]
theorem coindMap_smul [ContinuousMul G] (φ : A →+ B)
    (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) (g : G) (f : coind G U A) :
    coindMap G U φ hφ (g • f) = g • coindMap G U φ hφ f := by
  ext x; simp

end Functoriality

section Exactness

variable {G : Type*} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A B C : Type*} [AddCommGroup A] [DistribMulAction U A] [AddCommGroup B]
  [DistribMulAction U B] [AddCommGroup C] [DistribMulAction U C]

/-- **Coinduction preserves injectivity.** No topological hypothesis is needed: the induced map is
postcomposition. -/
theorem coindMap_injective (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (hinj : Function.Injective φ) : Function.Injective (coindMap G U φ hφ) := fun _ _ h =>
  Subtype.ext (funext fun g => hinj (congrFun (Subtype.ext_iff.mp h) g))

/-- **Coinduction is exact in the middle.** If `A →+ B →+ C` is exact at `B` with `φ` injective,
then the coinduced sequence is exact at `Coind_U^G B`. Choosing the preimage is unambiguous, so no
section of the group is needed here; that is only the case in
`TauCeti.coindMap_surjective`. -/
theorem coindMap_range_eq_ker (φ : A →+ B) (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a)
    (ψ : B →+ C) (hψ : ∀ (u : U) (b : B), ψ (u • b) = u • ψ b) (hinj : Function.Injective φ)
    (hexact : AddMonoidHom.range φ = AddMonoidHom.ker ψ) :
    AddMonoidHom.range (coindMap G U φ hφ) = AddMonoidHom.ker (coindMap G U ψ hψ) := by
  have : Nonempty A := ⟨0⟩
  have hli : ∀ a : A, Function.invFun φ (φ a) = a := Function.leftInverse_invFun hinj
  ext F
  simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩
    refine Subtype.ext (funext fun g => ?_)
    have h : φ ((f : G → A) g) ∈ AddMonoidHom.ker ψ := hexact ▸ ⟨_, rfl⟩
    simpa using h
  · intro hF
    have hmem : ∀ g : G, (F : G → B) g ∈ AddMonoidHom.range φ := fun g => by
      rw [hexact]
      exact congrFun (Subtype.ext_iff.mp hF) g
    have hinvFun : ∀ g : G, φ (Function.invFun φ ((F : G → B) g)) = (F : G → B) g := fun g =>
      Function.invFun_eq (hmem g)
    refine ⟨⟨fun g => Function.invFun φ ((F : G → B) g),
      (isLocallyConstant_of_mem_coind F.2).comp (Function.invFun φ), fun u g => ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := hmem g
      have h1 : (F : G → B) ((u : G) * g) = φ (u • a) := by
        rw [apply_mul_of_mem_coind F.2 u g, ← ha, hφ]
      simp only [h1, ← ha, hli]
    · exact Subtype.ext (funext hinvFun)

end Exactness

section Surjectivity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {U : Subgroup G}
  {A B : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A] [AddCommGroup B] [DistribMulAction U B]

/-- **Coinduction preserves surjectivity**, and this is where the topology does the work: a
locally constant `U`-equivariant map `G → B` is lifted through `φ` by choosing preimages along a
*continuous* factorization of `G` over the right cosets of `U`
(`TauCeti.exists_continuous_rightCosetFactorization`, from Layer 0's continuous section). The
factor `w g •` is forced — without it the lift is not `U`-equivariant — and it is exactly what
discreteness of `A` and continuity of the `U`-action make locally constant again.

Together with `TauCeti.coindMap_injective` and `TauCeti.coindMap_range_eq_ker` this says that
coinduction along a closed subgroup of a profinite group sends a short exact sequence of discrete
`U`-modules to a short exact sequence of discrete `G`-modules. -/
theorem coindMap_surjective (hU : IsClosed (U : Set G)) (φ : A →+ B)
    (hφ : ∀ (u : U) (a : A), φ (u • a) = u • φ a) (hsurj : Function.Surjective φ) :
    Function.Surjective (coindMap G U φ hφ) := by
  obtain ⟨w, r, hw_cont, hr_cont, hwr, hw_mul, hr_mul⟩ :=
    exists_continuous_rightCosetFactorization U hU
  intro F
  have hF : IsLocallyConstant fun g : G => (F : G → B) (r g) :=
    (isLocallyConstant_of_mem_coind F.2).comp_continuous hr_cont
  refine ⟨⟨fun g => w g • Function.surjInv hsurj ((F : G → B) (r g)), ?_, fun u g => ?_⟩, ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2 (continuous_smul.comp
      (hw_cont.prodMk (hF.comp (Function.surjInv hsurj)).continuous))
  · simp only [hw_mul u g, hr_mul u g, mul_smul]
  · refine Subtype.ext (funext fun g => ?_)
    rw [coindMap_apply, hφ, Function.surjInv_eq hsurj,
      ← apply_mul_of_mem_coind F.2 (w g) (r g), hwr g]

end Surjectivity

section Degenerate

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **`Coind_1^G A` is the group of all locally constant maps `G → A`**: for the trivial subgroup
the equivariance condition is vacuous. This is the module the dimension-shifting argument
embeds a discrete module into. -/
@[simp]
theorem mem_coind_bot_iff {A : Type*} [AddCommGroup A] [DistribMulAction (⊥ : Subgroup G) A]
    {f : G → A} : f ∈ coind G ⊥ A ↔ IsLocallyConstant f :=
  ⟨fun hf => hf.1, fun hf => ⟨hf, fun u g => by
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp u.2)
    rw [hu, OneMemClass.coe_one, one_mul, one_smul]⟩⟩

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction (⊤ : Subgroup G) A] [ContinuousSMul (⊤ : Subgroup G) A]

/-- For `U = ⊤` the orbit map `g ↦ g • a` is a member of the coinduced module: it is locally
constant because the action is continuous and `A` is discrete. -/
theorem smul_mem_coind_top {a : A} :
    (fun g : G => (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a) ∈ coind G ⊤ A := by
  refine ⟨(IsLocallyConstant.iff_continuous _).2 (continuous_smul.comp
    ((Continuous.subtype_mk continuous_id fun g : G => Subgroup.mem_top g).prodMk
      continuous_const)), fun u g => ?_⟩
  have h : (⟨(u : G) * g, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
      u * ⟨g, Subgroup.mem_top g⟩ := Subtype.ext rfl
  simp only [h, mul_smul]

variable (G A) in
/-- **`Coind_G^G A` is `A`**: evaluation at `1` is an isomorphism, with inverse `a ↦ (g ↦ g • a)`.
The inverse is where continuity of the action is used; without it `g ↦ g • a` need not be locally
constant. -/
def coindEvalTopEquiv : coind G ⊤ A ≃+ A where
  toFun f := (f : G → A) 1
  invFun a := ⟨_, smul_mem_coind_top (a := a)⟩
  left_inv f := Subtype.ext (funext fun g => by
    simpa using (apply_mul_of_mem_coind f.2 ⟨g, Subgroup.mem_top g⟩ 1).symm)
  right_inv a := by
    have h : (⟨(1 : G), Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) = 1 := Subtype.ext rfl
    simp [h]
  map_add' _ _ := (rfl)

@[simp]
theorem coindEvalTopEquiv_apply (f : coind G ⊤ A) : coindEvalTopEquiv G A f = (f : G → A) 1 :=
  (rfl)

@[simp]
theorem coindEvalTopEquiv_symm_apply (a : A) (g : G) :
    (((coindEvalTopEquiv G A).symm a : coind G ⊤ A) : G → A) g =
      (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) • a := (rfl)

end Degenerate

end TauCeti
