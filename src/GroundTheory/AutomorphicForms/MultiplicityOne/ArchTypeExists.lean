module

public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

-- Source module: GroundTheory.AutomorphicForms.MultiplicityOne.NormOne

section

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def openSubgroupOf (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    OpenSubgroup (AdelicGLn.FiniteAdelicGL K n) where
  toSubgroup := U.map (AdelicGLn.integralFiniteGL K n).subtype
  isOpen' := by
    change IsOpen ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
      Set (AdelicGLn.FiniteAdelicGL K n))
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU

def IsSmoothTest (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) : Prop :=
  ∃ (ν : Measure (ArchUnits K n)) (_ : ν.IsHaarMeasure) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (β : ArchMatrix K n → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ),
    f = archConv ν hβ.continuous hβc hβu (finAvg U hU g)

theorem IsSmoothTest.exists_finOne_mul {f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ}
    (hf : IsSmoothTest f) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      ∀ u ∈ U, ∀ x, f (finOne K n u * x) = f x := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  refine ⟨U, hU, fun u hu x => ?_⟩
  rw [archConv_apply, archConv_apply]
  exact archConvFun_finOne_mul _ _ u (fun y => finAvgFun_finOne_mul U hU g ⟨u, hu⟩ y) x

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem exists_isSmoothTest_near (g : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ,
      IsSmoothTest f ∧ ∫ x, ‖g x - f x‖ ∂μ ≤ ε := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ArchUnits K n), ν.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨U, hU, β, hβ, hβc, hβu, -, hclose⟩ := exists_smooth_approx μ ν g hε
  exact ⟨_, ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩,
    le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)) hclose⟩

theorem _root_.GroundTheory.Automorphic.UnitaryRep.integrated_eq_zero_of_dense {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (P : CompactlySupportedContinuousMap G ℂ → Prop)
    (hP : ∀ (g : CompactlySupportedContinuousMap G ℂ) (ε : ℝ), 0 < ε →
      ∃ f, P f ∧ ∫ x, ‖g x - f x‖ ∂ν ≤ ε)
    {v : H} (h : ∀ f, P f → π.integrated ν (UnitaryRep.ccToL1 ν f) v = 0)
    (g : CompactlySupportedContinuousMap G ℂ) : π.integrated ν (UnitaryRep.ccToL1 ν g) v = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hε' : 0 < ε / (‖v‖ + 1) := div_pos hε (by positivity)
  obtain ⟨f, hfs, hclose⟩ := hP g _ hε'
  have hf0 := h f hfs
  have hd := π.dist_integrated_ccToL1_le ν g f
  have hv1 : ‖v‖ / (‖v‖ + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [dist_eq_norm] at hd
  calc ‖π.integrated ν (UnitaryRep.ccToL1 ν g) v‖
      = ‖(π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)) v‖ := by
        rw [sub_apply, hf0, sub_zero]
    _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ v
    _ ≤ (ε / (‖v‖ + 1)) * ‖v‖ := by gcongr; exact hd.trans hclose
    _ = ε * (‖v‖ / (‖v‖ + 1)) := by ring
    _ ≤ ε * 1 := by gcongr
    _ = 0 + ε := by ring

end MultiplicityOne

end

end GroundTheory.Automorphic
end
end

-- Source module: GroundTheory.AutomorphicForms.MultiplicityOne.FiniteFactor

section

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSubspace (σ : UnitaryRep (normOneGL (K := K) (n := n)) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, σ (finProj K n u) v = v}
  add_mem' hv hw u hu := by rw [map_add (f := _), hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

variable (σ : UnitaryRep (normOneGL (K := K) (n := n)) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n))

variable {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]


end MultiplicityOne

end

end GroundTheory.Automorphic
end
end

-- Source module: GroundTheory.AutomorphicForms.MultiplicityOne.ArchTypeExists

section

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL (K := K) (n := n)) H}
variable {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]

theorem map_integrated_of_left_invariant {f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ}
    {h : normOneGL (K := K) (n := n)} (hf : ∀ x, f (h⁻¹ * x) = f x) (v : H) :
    σ h (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) = σ.integrated μ (UnitaryRep.ccToL1 μ f) v := by
  have e := σ.map_comp_integrated μ h (UnitaryRep.ccToL1 μ f)
  have e2 : UnitaryRep.leftTranslate μ h (UnitaryRep.ccToL1 μ f) = UnitaryRep.ccToL1 μ f := by
    refine Lp.ext ?_
    have hc := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate μ h (UnitaryRep.ccToL1 μ f), hc,
      (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 μ f : normOneGL (K := K) (n := n) → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 μ f) x
    rw [show (UnitaryRep.ccToL1 μ f : normOneGL (K := K) (n := n) → ℂ) (h⁻¹ * x) = f (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 μ f : normOneGL (K := K) (n := n) → ℂ) x = f x from h2]
    exact hf x
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

theorem exists_fixedSubspace_ne_bot (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (hσ : σ.IsIrreducible) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) ≠ ⊥ := by
  have := hσ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨g, hg⟩ := UnitaryRep.exists_integrated_ne_zero σ μ hv
  obtain ⟨f, hf, hfv⟩ : ∃ f, IsSmoothTest f ∧ σ.integrated μ (UnitaryRep.ccToL1 μ f) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (UnitaryRep.integrated_eq_zero_of_dense σ μ IsSmoothTest
      (fun g' ε hε => exists_isSmoothTest_near μ g' hε) hcon g)
  obtain ⟨U, hU, hinv⟩ := hf.exists_finOne_mul
  refine ⟨U, hU, fun hbot => hfv ?_⟩
  have hmem : σ.integrated μ (UnitaryRep.ccToL1 μ f) v ∈
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.coe_subtype, finProj_eq_finOne]
    refine map_integrated_of_left_invariant (fun x => ?_) v
    rw [← map_inv]
    exact hinv u⁻¹ (U.inv_mem hu) x
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

end MultiplicityOne

end

end GroundTheory.Automorphic
end
end
