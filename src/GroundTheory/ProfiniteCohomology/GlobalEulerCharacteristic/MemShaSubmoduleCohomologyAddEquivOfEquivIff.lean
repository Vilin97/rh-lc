module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSeq
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaDescent
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerShaOpen
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaTwist

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Representation

universe u

noncomputable section

section Coordinates

variable {k H N : Type*} [CommRing k] [AddCommGroup H] [Module k H] [AddCommGroup N] [Module k N]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι k N)

def coordTensor (i : ι) : TensorProduct k H N →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H (b.coord i)

omit [Fintype ι] in
theorem coordTensor_tmul (i : ι) (y : H) (m : N) : coordTensor b i (y ⊗ₜ[k] m) = b.coord i m • y := by
  simp [coordTensor]

theorem sum_coordTensor_tmul (z : TensorProduct k H N) : ∑ i, coordTensor b i z ⊗ₜ[k] b i = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | tmul y m =>
    calc ∑ i, coordTensor b i (y ⊗ₜ[k] m) ⊗ₜ[k] b i = ∑ i, y ⊗ₜ[k] (b.repr m i • b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coordTensor_tmul, TensorProduct.smul_tmul, Module.Basis.coord_apply]
      _ = y ⊗ₜ[k] m := by rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add z w hz hw =>
    simp only [map_add (f := _), TensorProduct.add_tmul]
    rw [Finset.sum_add_distrib, hz, hw]


omit [Fintype ι] in
theorem coordTensor_rTensor {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H) (i : ι)
    (w : TensorProduct k X N) : coordTensor b i (f.rTensor N w) = f (coordTensor b i w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rw [LinearMap.rTensor_tmul, coordTensor_tmul, coordTensor_tmul, map_smul]
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

theorem mem_range_rTensor_iff {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H)
    (z : TensorProduct k H N) :
    z ∈ LinearMap.range (f.rTensor N) ↔ ∀ i, coordTensor b i z ∈ LinearMap.range f := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨coordTensor b i w, (coordTensor_rTensor b f i w).symm⟩
  · intro h
    choose w hw using h
    refine ⟨∑ i, w i ⊗ₜ[k] b i, ?_⟩

    rw [map_sum]
    simp_rw [LinearMap.rTensor_tmul, hw]
    exact sum_coordTensor_tmul b z

end Coordinates

section Twist

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)]
  (Q : Subgroup G) (ψ : ∀ v, Hv v →ₜ* Q) (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hM : ∀ (g : Q) (m : M), M.ρ g m = m) {ιb : Type*} [Fintype ιb] (b : Module.Basis ιb k M)

def resTensorFormMor (f : M →ₗ[k] k) : Rep.res Q.subtype (T ⊗ M) ⟶ Rep.res Q.subtype T :=
  (resTensorIso Q.subtype T M).hom ≫
    tensorFormMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) f
      (form_invariant_of_forall_eq (M := Rep.res Q.subtype M) hM f)

theorem cohomologyMap_resTensorFormMor_twistResMap (f : M →ₗ[k] k) (n : ℕ)
    (y : cohomology (Rep.res Q.subtype T) n) (m : M) :
    (cohomologyMap (resTensorFormMor Q T M hM f) n).hom (twistResMap Q T M hM n (y ⊗ₜ[k] m)) = f m • y := by
  rw [twistResMap_tmul, ← ModuleCat.comp_apply, ← cohomologyMap_comp]
  have e : (tensorRightMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) m (fun h => hM h m) ≫
      (resTensorIso Q.subtype T M).inv) ≫ resTensorFormMor Q T M hM f = f m • 𝟙 _ := by
    ext t
    change f m • t = f m • t
    rfl
  rw [e, cohomologyMap_smul, cohomologyMap_id]
  rfl


omit [Fintype ιb] in
theorem cohomologyMap_resTensorFormMor_coord_twistResMap (n : ℕ) (i : ιb)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    (cohomologyMap (resTensorFormMor Q T M hM (b.coord i)) n).hom (twistResMap Q T M hM n z) =
      coordTensor b i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y m => rw [cohomologyMap_resTensorFormMor_twistResMap, coordTensor_tmul]
  | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw, map_add (f := _)]

theorem twistResMap_mem_shaSubmodule_iff (n : ℕ)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    twistResMap Q T M hM n z ∈ shaSubmodule ψ (Rep.res Q.subtype (T ⊗ M)) n ↔
      ∀ i, coordTensor b i z ∈ shaSubmodule ψ (Rep.res Q.subtype T) n := by
  constructor
  · intro h i
    rw [← cohomologyMap_resTensorFormMor_coord_twistResMap Q T M hM b n i z]
    exact cohomologyMap_mem_shaSubmodule ψ _ h
  · intro h

    rw [← sum_coordTensor_tmul b z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twistResMap_tmul]
    exact cohomologyMap_mem_shaSubmodule ψ _ (h i)

end Twist

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)
  [Module.Finite k M] (hTr : Module.finrank k T = 1) (hP : ((P : Subgroup G).index : k) ≠ 0)

theorem coe_coprimeTwistEquiv (n : ℕ) (x : cohomology M n) :
    haveI := isDiscreteRep_homRep P T M hT hM
    haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
    haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
    twistResEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n
        (coprimeTwistEquiv P T M hT hM hTr hP n x) =
      (cohomologyRes (T ⊗ homRep T M) (P : Subgroup G) n).hom
        ((cohomologyMap (evalInv T M hTr) n).hom x) := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  rw [← twistInvariantsEquiv_apply]
  simp only [coprimeTwistEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem mem_shaSubmodule_iff_coprimeTwistEquiv {ιb : Type*} [Fintype ιb]
    (b : Module.Basis ιb k (homRep T M)) (n : ℕ) (x : cohomology M n) :
    x ∈ shaSubmodule φ M n ↔
      ∀ i, coordTensor b i (coprimeTwistEquiv P T M hT hM hTr hP n x : TensorProduct k
        (cohomology (Rep.res (P : Subgroup G).subtype T) n) (homRep T M)) ∈
          shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))

  have h1 : x ∈ shaSubmodule φ M n ↔
      (cohomologyMap (evalInv T M hTr) n).hom x ∈ shaSubmodule φ (T ⊗ homRep T M) n := by
    refine ⟨cohomologyMap_mem_shaSubmodule φ _, fun h => ?_⟩
    have e : (cohomologyMap (evalMor T M) n).hom ((cohomologyMap (evalInv T M hTr) n).hom x) = x := by
      rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, evalInv_comp_evalMor, cohomologyMap_id]
      rfl
    rw [← e]
    exact cohomologyMap_mem_shaSubmodule φ _ h
  rw [h1, mem_shaSubmodule_iff_cohomologyRes φ P _ (bijective_nsmul_of_ne_zero hP), ← coe_coprimeTwistEquiv P T M hT hM hTr hP n x,
    twistResEquiv_apply]
  exact twistResMap_mem_shaSubmodule_iff (P : Subgroup G) (mackeyFamily P φ) T (homRep T M)
    (homRep_ρ_of_mem P T M hT hM) b n _


include hTr hP in
theorem finrank_shaSubmodule_eq_finrank_invariants (n : ℕ) {X : Type u} [AddCommGroup X] [Module k X]
    (ρX : Representation k (G ⧸ (P : Subgroup G)) X)
    (e : X →ₗ[k] cohomology (Rep.res (P : Subgroup G).subtype T) n)
    (he : ρX.IsIntertwiningMap (cohomologyConjRep T (P : Subgroup G) n) e) (hinj : Function.Injective e)
    (hrange : ∀ y, y ∈ shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n ↔
      y ∈ LinearMap.range e) :
    Module.finrank k (shaSubmodule φ M n) = Module.finrank k
      (ρX.tprod (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants := by
  classical
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  set σ := quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM)
  set E := coprimeTwistEquiv P T M hT hM hTr hP n
  set R := e.rTensor (homRep T M)
  have hR : (ρX.tprod σ).IsIntertwiningMap ((cohomologyConjRep T (P : Subgroup G) n).tprod σ) R :=
    isIntertwiningMap_rTensor σ he
  have hRinj : Function.Injective R := Module.Flat.rTensor_preserves_injective_linearMap e hinj
  let Ψ : (ρX.tprod σ).invariants →ₗ[k] ((cohomologyConjRep T (P : Subgroup G) n).tprod σ).invariants :=
    R.restrict (mapsTo_invariants hR)
  let Φ : (ρX.tprod σ).invariants →ₗ[k] cohomology M n := E.symm.toLinearMap ∘ₗ Ψ
  have hΦinj : Function.Injective Φ := fun w w' h =>
    Subtype.ext (hRinj (congrArg Subtype.val (E.symm.injective h)))
  let b := Module.Free.chooseBasis k (homRep T M)
  have hrangeΦ : LinearMap.range Φ = shaSubmodule φ M n := by
    ext x
    rw [mem_shaSubmodule_iff_coprimeTwistEquiv φ P T M hT hM hTr hP b n x]
    constructor
    · rintro ⟨w, rfl⟩ i
      have hEw : (E (Φ w) : TensorProduct k (cohomology (Rep.res (P : Subgroup G).subtype T) n)
          (homRep T M)) = R w := by
        change ((E (E.symm (Ψ w)) : _)) = R w
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [hEw, coordTensor_rTensor]
      exact (hrange _).2 ⟨_, rfl⟩
    · intro h
      obtain ⟨w₀, hw₀⟩ := (mem_range_rTensor_iff b e _).2 fun i => (hrange _).1 (h i)
      have hinv : w₀ ∈ (ρX.tprod σ).invariants := fun q => hRinj (by
        rw [hR.isIntertwining, hw₀]
        exact (E x).2 q)
      refine ⟨⟨w₀, hinv⟩, ?_⟩
      change E.symm (Ψ ⟨w₀, hinv⟩) = x
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hw₀
  rw [← hrangeΦ, LinearMap.finrank_range_of_inj hΦinj]

end Descent

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.MemShaSubmoduleCohomologyAddEquivOfEquivIff

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global Representation

universe u

noncomputable section

section Scalars

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A] [IsDiscreteRep A'] (e : A ≃+ A')
  (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

theorem mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv e he n x ∈ shaSubmodule φ A' n ↔ x ∈ shaSubmodule φ A n := by
  refine forall_congr' fun v => ?_
  have key := cohomologyAddEquivOfEquiv_mapAlong e he (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (B := Rep.res (φ v).toMonoidHom A) (B' := Rep.res (φ v).toMonoidHom A') e (fun _ a => he _ a) (𝟙 _) (𝟙 _)
    (fun _ => rfl) n x
  rw [← key]
  constructor
  · intro h
    exact (cohomologyAddEquivOfEquiv (A := Rep.res (φ v).toMonoidHom A) (A' := Rep.res (φ v).toMonoidHom A')
      e (fun _ a => he _ a) n).injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Scalars

section Card

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (hM : ∀ m : M, ℓ • m = 0)

end Card

section KummerZMod

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  {T O : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep T] [IsDiscreteRep O] {ℓ : ℕ} {f : T ⟶ O}
  {w : f ≫ (ℓ • 𝟙 O) = 0} (hS : (ShortComplex.mk f (ℓ • 𝟙 O) w).ShortExact) (hT : ∀ t : T, ℓ • t = 0)

def kummerModNZMod (i : ℕ) :
    ModN (cohomology (Rep.res N.subtype O) i) ℓ →ₗ[ZMod ℓ]
      cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) :=
  ((cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).toAddMonoidHom.comp
      (kummerModNHom N hS i)).toZModLinearMap ℓ

theorem kummerModNZMod_apply (i : ℕ) (y : ModN (cohomology (Rep.res N.subtype O) i) ℓ) :
    kummerModNZMod N hS hT i y =
      cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1) (kummerModNHom N hS i y) :=
  rfl

theorem kummerModNZMod_injective (i : ℕ) : Function.Injective (kummerModNZMod N hS hT i) :=
  (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).injective.comp (kummerModNHom_injective N hS i)

variable [N.Normal] [CompactSpace N]

theorem isIntertwiningMap_kummerModNZMod (i : ℕ) :
    (letI := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i;
      modNRep (G ⧸ N) (cohomology (Rep.res N.subtype O) i) ℓ).IsIntertwiningMap
      (cohomologyConjRep (zmodRepOfTorsion ℓ T hT) N (i + 1)) (kummerModNZMod N hS hT i) := by
  let _ := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i
  refine ⟨fun q x => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have hs : (g : G ⧸ N) • y = (cohomologyConj O N i g).hom y :=
        conjActionOf_smul N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i g y
      rw [modNRep_mk, hs, cohomologyConjRep_mk, kummerModNZMod_apply, kummerModNZMod_apply,
        kummerModNHom_cohomologyConj]
      exact cohomologyAddEquivOfEquiv_cohomologyConj (A := T) (A' := zmodRepOfTorsion ℓ T hT)
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) N (i + 1) g _


omit [N.Normal] [CompactSpace N] in
theorem mem_shaSubmodule_iff_mem_range_kummerModNZMod {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)]
    [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] (ψ : ∀ v, Hv v →ₜ* N) (i : ℕ)
    (hsha : ∀ x : cohomology (Rep.res N.subtype T) (i + 1),
      x ∈ ptSha ψ (Rep.res N.subtype T) (i + 1) ↔ ∃ y, kummerModNHom N hS i y = x)
    (y : cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1)) :
    y ∈ shaSubmodule ψ (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) ↔
      y ∈ LinearMap.range (kummerModNZMod N hS hT i) := by
  set E := cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)
  obtain ⟨y', rfl⟩ := E.surjective y
  refine (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff ψ (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl)
    (i + 1) y').trans ?_
  refine (mem_ptSha_iff_mem_shaSubmodule ψ _ y').symm.trans ((hsha y').trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [kummerModNZMod_apply, hz]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, E.injective (by rw [← hz, kummerModNZMod_apply])⟩

end KummerZMod

section GS

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ℓ : ℕ) [Fact ℓ.Prime]

abbrev gsRootsZMod : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  zmodRepOfTorsion ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)

theorem finrank_gsRootsZMod {S} (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcard : Nat.card (gsRootsZMod S ℓ) = ℓ ^ 1 := by
    rw [pow_one]
    obtain ⟨f⟩ := nonempty_addEquiv_gsRoots_of_mem S (n := ℓ) (fun v hv =>
      by_contra fun h => hℓS v h hv)
    exact (Nat.card_congr f.toEquiv).trans (Nat.card_zmod ℓ)
  have : Finite (gsRootsZMod S ℓ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  exact finrank_eq_of_natCard_zmod ℓ hcard

variable {S} (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]

abbrev gsH1SUnitsModRep :
    Representation (ZMod ℓ)
      (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
      (ModN (cohomology (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (galSUnitsMax K.1 ℚ̄ S)) 1) ℓ) :=
  letI := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le (galSUnitsMax K.1 ℚ̄ S) 1
  modNRep _ _ ℓ

theorem finrank_shaSubmodule_two_eq_finrank_invariants (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hT : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (t : gsRootsZMod S ℓ),
      (gsRootsZMod S ℓ).ρ g t = t)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M hT hM))).invariants := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hP : (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 hcop.symm
  let P := gsOpenSubgroup S hL
  let N : Subgroup (galUnramifiedOutside K.1 ℚ̄ S) := P
  have hS := gsKummer_shortExact S ℓ hℓS
  have hTorsion := nsmul_gsRoots S ℓ
  refine finrank_shaSubmodule_eq_finrank_invariants (gsFinFamily S ιs) P (gsRootsZMod S ℓ) M
    hT hM (finrank_gsRootsZMod ℓ hℓS) hP 2 (gsH1SUnitsModRep ℓ hL)
    (kummerModNZMod N hS hTorsion 1) ?_ ?_ ?_
  · exact isIntertwiningMap_kummerModNZMod N hS hTorsion 1
  · exact kummerModNZMod_injective N hS hTorsion 1
  · exact mem_shaSubmodule_iff_mem_range_kummerModNZMod N hS hTorsion
      (mackeyFamily P (gsFinFamily S ιs)) 1
      (mem_ptSha_mackey_iff_exists_kummerModN hL ιs hℓ hℓS hK)

end GS

end

end GroundTheory.ProfCoh
end
end
