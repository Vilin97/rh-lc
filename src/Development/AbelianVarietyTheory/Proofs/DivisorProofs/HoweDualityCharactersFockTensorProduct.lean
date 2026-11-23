module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommuteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernelStatement
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactorStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensQuad

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  rcases eq_or_ne i w with rfl | h
  · simp
  · simp [Function.update_of_ne h]

noncomputable def atPlLin (w : T) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem atPlLin_apply (w : T) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := rfl

theorem atPl_mul (w : T) (L₁ L₂ : Module.End ℂ (V w)) : atPl w (L₁ * L₂) = atPl w L₁ * atPl w L₂ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod, Module.End.mul_apply]

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod]

theorem qop_atPl {ι : Type} [Fintype ι] [DecidableEq ι] (w : T) (F : ι → ι → Module.End ℂ (V w)) (α β : ℂ) (i j : ι) :
    qop (fun a b => atPl w (F a b)) α β i j = atPl w (qop F α β i j) := by

  simp only [qop, ← atPlLin_apply, map_sub, map_sum, map_smul, apply_ite (atPlLin w), map_zero]
  simp only [atPlLin_apply, atPl_mul, atPl_one]

theorem mem_of_atPl (C : ∀ w, Submodule ℂ (V w)) (w : T) (L : Module.End ℂ (V w)) (hL : ∀ x, L x ∈ C w)
    (v : ⨂[ℂ] i, V i) : atPl w L v ∈ tensAny C := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, atPl_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨w, by simpa using hL (f w)⟩, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.HoweR.TensQuad

open GlobalTheory.HoweR.TensQuad in
theorem GlobalTheory.HoweR.quadMod_actAt : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  intro T _ _ V _ _ C w p q a α β α' β' h i j v _
  have hu : units (actAt w a) = fun i j => atPl w (units a i j) := rfl
  have hn : negT (units (actAt w a)) = fun i j => atPl w (negT (units a) i j) := by
    funext i j
    simp only [negT, units, actAt_apply, ← atPlLin_apply, map_neg]
  refine ⟨?_, ?_⟩
  · rw [hu, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).1) v
  · rw [hn, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).2) v
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactorStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  first | exact @GlobalTheory.HoweR.quadMod_actAt | exact GlobalTheory.HoweR.quadMod_actAt | (intros; apply GlobalTheory.HoweR.quadMod_actAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton

section

@[expose] public section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingletonStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧ ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧ ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  first | exact @GlobalTheory.HoweR.TensSup.main | exact GlobalTheory.HoweR.TensSup.main | (intros; apply GlobalTheory.HoweR.TensSup.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors

section

@[expose] public section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensAlg

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_eq_toLinearMap (w : T) (L : Module.End ℂ (V w)) :
    atPl w L = (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L := rfl

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  unfold atPl
  have h : Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id := by
    funext i
    by_cases hi : i = w
    · subst hi; simp; rfl
    · simp [hi]
  rw [h]; exact PiTensorProduct.map_id

theorem atPl_sub_smul (w : T) (L : Module.End ℂ (V w)) (c : ℂ) (y : ⨂[ℂ] i, V i) :
    atPl w (L - c • 1) y = atPl w L y - c • y := by
  rw [atPl_eq_toLinearMap, map_sub, map_smul, ← atPl_eq_toLinearMap, ← atPl_eq_toLinearMap, atPl_one]
  simp

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp
  · simp [hi]

theorem atPl_tprod_eq_zero (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) (h : L (v w) = 0) :
    atPl w L (PiTensorProduct.tprod ℂ v) = 0 := by
  rw [atPl_tprod, h]
  exact MultilinearMap.map_update_zero _ _ _

theorem tensAll_mono {H H' : ∀ w, Submodule ℂ (V w)} (h : ∀ w, H w ≤ H' w) : tensAll H ≤ tensAll H' := by
  apply Submodule.span_mono
  rintro y ⟨f, hf, rfl⟩
  exact ⟨f, fun w => h w (hf w), rfl⟩

theorem iInf_hwSub_le {R S : T → ℕ} (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (μ : ∀ w, Ix (R w) (S w) → ℚ) :
    (⨅ w, hwSub (actAt w (a w)) (μ w)) ≤ tensAll (fun w => hwSub (a w) (μ w)) := by
  intro y hy
  rw [Submodule.mem_iInf] at hy
  refine GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel T V
    (fun w => {l | (∃ c, l = a w (Eab c c) - ((μ w c : ℚ) : ℂ) • 1) ∨ ∃ c d, posC c d ∧ l = a w (Eab c d)})
    (fun w => hwSub (a w) (μ w)) ?_ y ?_
  · intro w x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun c => ?_, fun c d hcd => ?_⟩
    · exact hx _ (Or.inl ⟨c, rfl⟩)
    · exact hx _ (Or.inr ⟨c, d, hcd, rfl⟩)
  · intro w l hl
    have hyw := hy w
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyw
    rcases hl with ⟨c, rfl⟩ | ⟨c, d, hcd, rfl⟩
    · rw [atPl_sub_smul]
      have h1 := hyw.1 c
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply] at h1
      exact h1
    · have h2 := hyw.2 c d hcd
      rw [actAt_apply] at h2
      exact h2

end GlobalTheory.HoweR.TensAlg

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.TensAlg in
theorem howeAlg_tensAny : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  intro T _ _ V _ _ R S a C hP
  have hG := GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute T V R S a (fun w => (hP w).1)
  choose α β α' β' hQ using fun w => (hP w).2.2.1
  choose μ v hv hgen hmul using fun w => (hP w).2.2.2.2
  refine GlobalTheory.T.howeAlg_of_cyclic_highest_weight T R S (⨂[ℂ] i, V i) (fun w => actAt w (a w)) hG.1 hG.2 (tensAny C) α β α' β'
    (fun w => GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor T V C w (R w) (S w) (a w) _ _ _ _ (hQ w)) ?_ ?_
  · intro B
    choose U hUfd hU using fun w => (hP w).2.2.2.1 B
    refine ⟨tensAll U, (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).2.1 hUfd, fun ν hν => ?_⟩
    exact (iInf_hwSub_le a ν).trans
      ((tensAll_mono (fun w => hU w (ν w) (fun c => hν w c))).trans (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).1)
  · refine ⟨μ, PiTensorProduct.tprod ℂ v, fun w => ?_,
      fun N hN hC hvN => GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor T V R S a C v hgen N hN hC hvN, ?_⟩
    · have h := hv w
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h ⊢
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply, ← atPl_sub_smul]
        exact atPl_tprod_eq_zero w _ v (h.1 c)
      · rw [actAt_apply]
        exact atPl_tprod_eq_zero w _ v (h.2 c d hcd)
    · refine (iInf_hwSub_le a μ).trans ((tensAll_mono (fun w => hmul w)).trans ?_)
      refine (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).1.trans ?_
      exact sup_le_sup_right ((GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).2.2 v) _

end GlobalTheory.HoweR

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactorsStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.howe_finite_length_tensor_product_factors : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  first | exact @GlobalTheory.HoweR.howeAlg_tensAny | exact GlobalTheory.HoweR.howeAlg_tensAny | (intros; apply GlobalTheory.HoweR.howeAlg_tensAny <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomialsStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.fock_pack | exact GlobalTheory.HoweR.fock_pack | (intros; apply GlobalTheory.HoweR.fock_pack <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProduct

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory
theorem howeAlg_fock_tensor : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  intro T _ _ P Q R S x
  exact GlobalTheory.T.howe_finite_length_tensor_product_factors T (fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) _ _ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) (fun w => coinv (P w) (Q w) (R w) (S w) (x w)) (fun w => GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials (P w) (Q w) (R w) (S w) (x w))
end GlobalTheory
end
end
