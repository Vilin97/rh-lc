module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.GmSingleIsTestForm
public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem
public import ReciprocityTheory.L2DbarEstimates.Localization.ChartFlat
public import ReciprocityTheory.L2DbarEstimates.Localization.Choice
public import ReciprocityTheory.L2DbarEstimates.Localization.Closure
public import ReciprocityTheory.L2DbarEstimates.Localization.Cutoff
public import ReciprocityTheory.L2DbarEstimates.Localization.DerivSmoothTransitionOfOneLt
public import ReciprocityTheory.L2DbarEstimates.Localization.Extend
public import ReciprocityTheory.L2DbarEstimates.Localization.IntegrableFd
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.Localization.LeviZCoordChart
public import ReciprocityTheory.L2DbarEstimates.Localization.Locality
public import ReciprocityTheory.L2DbarEstimates.Localization.Localize
public import ReciprocityTheory.L2DbarEstimates.Localization.MultAdj
public import ReciprocityTheory.L2DbarEstimates.Localization.PrimZeroOfNonpos
public import ReciprocityTheory.L2DbarEstimates.Localization.Primed
public import ReciprocityTheory.L2DbarEstimates.Localization.SSmooth
public import ReciprocityTheory.L2DbarEstimates.Localization.ShellCeilEq
public import ReciprocityTheory.L2DbarEstimates.Localization.SplitTest
public import ReciprocityTheory.L2DbarEstimates.Localization.TestIneq
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBack
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightRel

-- Source module: ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Hormander

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hTI : TestIneqStatement n M) (hReg : RegMStatement n M) :
    HStatement n M := by
  intro X ph F0 h hph hlevi hF0 hh hpt
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hphc : Continuous ph := gm_cont_of_smoothR n X.z hz ph hph
  have hphm : Measurable ph := hphc.measurable
  have hF0c : Continuous F0 := Smooth.continuous n X.z hz F0 hF0
  by_cases hA : (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z) = ⊤
  · exact ⟨fun _ => 0, Holo.const n X.z 0, by rw [hA]; exact le_top⟩
  set Ae := ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z with hAe
  have hAe' : ENNReal.ofReal Ae.toReal = Ae := ENNReal.ofReal_toReal hA
  have hv : Continuous (dbarF n X.z F0) :=
    gm_form_continuous _ fun k => Smooth.continuous n X.z hz _ (Smooth.db n X.z k F0 hF0)

  have hθ : ∀ e : gmTestForms n X.z,
      ENNReal.ofReal (‖gmTheta n X.z hz ph hph e‖ ^ 2) =
        wint n X.z (tstar n X.z ph ph e) ph := by
    intro e
    rw [gm_norm_sq]
    have hae : (gmTheta n X.z hz ph hph e : M → ℂ) =ᵐ[wvol n X.z ph] tstar n X.z ph ph e :=
      (gm_memLp_tstar n X.z hz ph hph e e.2).coeFn_toLp
    have hae2 : (fun x => ‖(gmTheta n X.z hz ph hph e : M → ℂ) x‖ₑ ^ (2:ℝ)) =ᵐ[wvol n X.z ph]
        fun x => ‖tstar n X.z ph ph e x‖ₑ ^ (2:ℝ) :=
      hae.mono fun x hx => congrArg (fun t : ℂ => ‖t‖ₑ ^ (2:ℝ)) hx
    rw [lintegral_congr_ae hae2]
    exact gm_lintegral_wvol n X.z ph hphm _
  have hbound : ∀ e : gmTestForms n X.z,
      ‖gmEll n X.z hz ph hph (dbarF n X.z F0) hv e‖ ^ 2 ≤
        Ae.toReal * ‖gmTheta n X.z hz ph hph e‖ ^ 2 := by
    intro e
    have h1 : ENNReal.ofReal (‖ipV n X.z (dbarF n X.z F0) e ph‖ ^ 2) ≤
        Ae * wint n X.z (tstar n X.z ph ph e) ph :=
      hTI X ph F0 h hph hlevi hF0 hh hpt hA e e.2
    rw [← hθ e, ← hAe', ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))).1 h1
  obtain ⟨u, -, hu2, hu⟩ := rieszOnRange (gmTestForms n X.z) (Lp ℂ 2 (wvol n X.z ph))
    (gmTheta n X.z hz ph hph) (gmEll n X.z hz ph hph (dbarF n X.z F0) hv) Ae.toReal
    ENNReal.toReal_nonneg hbound
  have hexp : ∀ x, (Real.exp (-ph x) : ℂ) * (Real.exp (ph x) : ℂ) = 1 := by
    intro x
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

  have hweak : ∀ φ : M → ℂ, IsTest n X.z φ → ∀ j : Fin n,
      ∫ x, (F0 x - u x) * db n X.z j φ x ∂vol n X.z = 0 := by
    intro φ hφ j
    have hdφc : Continuous (db n X.z j φ) :=
      Smooth.continuous n X.z hz _ (Smooth.db n X.z j φ hφ.1)
    have hdφs : HasCompactSupport (db n X.z j φ) :=
      hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n X.z j φ))
    have hIF : Integrable (fun x => F0 x * db n X.z j φ x) (vol n X.z) :=
      integrable_of_continuous n X.z hz _ (hF0c.mul hdφc) hdφs.mul_left
    have hS := gm_single_isTestForm n X.z ph hph φ hφ j
    have hmem : MemLp (tstar n X.z ph ph (gmSingle ph φ j)) 2 (wvol n X.z ph) :=
      gm_memLp_tstar n X.z hz ph hph _ hS
    obtain ⟨hin, hint⟩ := gm_inner_toLp n X.z ph hphm u _ hmem
    have key := hu ⟨gmSingle ph φ j, hS⟩
    have k1 : gmTheta n X.z hz ph hph ⟨gmSingle ph φ j, hS⟩ = hmem.toLp _ := rfl
    have k2 : gmEll n X.z hz ph hph (dbarF n X.z F0) hv ⟨gmSingle ph φ j, hS⟩ =
        ipV n X.z (dbarF n X.z F0) (gmSingle ph φ j) ph := rfl
    have hfun : (fun x => (Real.exp (-ph x) : ℂ) *
        (conj (u x) * tstar n X.z ph ph (gmSingle ph φ j) x)) =
          fun x => -(conj (u x * db n X.z j φ x)) := by
      funext x
      rw [gm_tstar_single, map_mul]
      linear_combination (-(conj (u x) * conj (db n X.z j φ x))) * hexp x
    rw [k1, k2, hin, gm_ipV_single, hfun, integral_neg, integral_conj,
      integral_db_mul n X.z hz j F0 φ (Smooth.ck n X.z 1 F0 hF0) (Smooth.ck n X.z 1 φ hφ.1) hφ.2,
      map_neg] at key
    have hEq : ∫ x, u x * db n X.z j φ x ∂vol n X.z = ∫ x, F0 x * db n X.z j φ x ∂vol n X.z :=
      (starRingEnd ℂ).injective (neg_inj.mp key)
    have hI : Integrable (fun x => -(conj (u x * db n X.z j φ x))) (vol n X.z) := by
      rw [← hfun]; exact hint
    have hIu : Integrable (fun x => u x * db n X.z j φ x) (vol n X.z) := by
      refine Integrable.mono' hI.norm ?_ (Eventually.of_forall fun x => by simp)
      have hm := Complex.continuous_conj.comp_aestronglyMeasurable hI.aestronglyMeasurable.neg
      simpa using hm
    have hsplit : (fun x => (F0 x - u x) * db n X.z j φ x) =
        fun x => F0 x * db n X.z j φ x - u x * db n X.z j φ x := by
      funext x; ring
    rw [hsplit, integral_sub hIF hIu, hEq, sub_self]
  obtain ⟨G, hG, hGae⟩ := hReg X.z hz (fun x => F0 x - u x)
    (locL2_sub_weightedL2 n X.z hz ph hph F0 hF0c u) hweak
  refine ⟨G, hG, ?_⟩
  have hae : (fun x => ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * Real.exp (-ph x))) =ᵐ[vol n X.z]
      fun x => ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    filter_upwards [hGae] with x hx
    have hx' : F0 x - u x = G x := hx
    rw [← hx', sub_sub_cancel]
  calc wint n X.z (fun x => F0 x - G x) ph
      = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂vol n X.z := lintegral_congr_ae hae
    _ = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n X.z ph := (gm_lintegral_wvol n X.z ph hphm _).symm
    _ = ENNReal.ofReal (‖u‖ ^ 2) := (gm_norm_sq u).symm
    _ ≤ ENNReal.ofReal Ae.toReal := ENNReal.ofReal_le_ofReal hu2
    _ = Ae := hAe'

end

end ReciprocityTheory.L2DbarEstimates.F
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.Localization.Imports

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem dens (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCut : CutoffStatement n M) (hUR : UnweightRelStatement n M)
    (hUB : UnweightBackStatement n M) (hLoc : LocalizeStatement n M)
    (hCh : ChartFlatStatement n M) : DensStatement n M := by
  intro z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone
  refine hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone
  intro f w σ hf hw hσ hadj hone hcf hcw hcσ
  obtain ⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩ :=
    hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone
  refine hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_
  exact hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar
    (hcG hcf) (hcD hcw) (hcS hcf hcσ)

end

end ReciprocityTheory.L2DbarEstimates.F
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.Localization.KPsiHasCompactSupport

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem wvol_finiteOnCompacts {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by
  have := vol_isFiniteMeasureOnCompacts n z hz
  refine ⟨fun K hK => ?_⟩
  have hc : ContinuousOn (fun x => Real.exp (-ph x)) K :=
    (Real.continuous_exp.comp hph.neg).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  unfold wvol
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂vol n z := by
        refine setLIntegral_mono' hK.measurableSet fun x hx => ENNReal.ofReal_le_ofReal ?_
        have h := hC x hx
        rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at h
    _ = ENNReal.ofReal C * vol n z K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

def kPsi {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (φ : M → ℂ)
    (j k : Fin n) : M → V n :=
  fun x => ((Real.exp (ph x) : ℝ) : ℂ) •
    ((starRingEnd ℂ) (db n z j φ x) • bas n k - (starRingEnd ℂ) (db n z k φ x) • bas n j)

theorem kPsi_inner {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (φ : M → ℂ) (j k : Fin n) (v : V n) (x : M) :
    (ENNReal.ofReal (Real.exp (-ph x))).toReal • ⟪kPsi n z ph φ j k x, v⟫_ℂ =
      v k * db n z j φ x - v j * db n z k φ x := by
  have h1 : (Real.exp (-ph x) : ℂ) * (Real.exp (ph x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [kPsi, bas, inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left,
    Complex.conj_ofReal, Complex.conj_conj, map_one, one_mul, Complex.real_smul]
  linear_combination (v k * db n z j φ x - v j * db n z k φ x) * h1

theorem kPsi_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) (φ : M → ℂ)
    (hφ : IsTest n z φ) (j k : Fin n) : Continuous (kPsi n z ph φ j k) := by
  have hj := Smooth.continuous n z hz _ (Smooth.db n z j φ hφ.1)
  have hk := Smooth.continuous n z hz _ (Smooth.db n z k φ hφ.1)
  unfold kPsi
  refine (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph)).smul ?_
  exact ((Complex.continuous_conj.comp hj).smul continuous_const).sub
    ((Complex.continuous_conj.comp hk).smul continuous_const)

theorem kPsi_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (φ : M → ℂ) (hφ : IsTest n z φ) (j k : Fin n) :
    HasCompactSupport (kPsi n z ph φ j k) := by
  refine hφ.2.mono' fun x hx => ?_
  by_contra hnot
  have hj : db n z j φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z j φ (subset_tsupport _ h))
  have hk : db n z k φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z k φ (subset_tsupport _ h))
  exact hx (by simp [kPsi, hj, hk])

theorem kSub (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : KSubStatement n M := by
  unfold KSubStatement
  intro z hz ph₂ hph
  have : IsFiniteMeasureOnCompacts (wvol n z ph₂) := wvol_finiteOnCompacts n z hz ph₂ hph
  have hmem : ∀ φ, IsTest n z φ → ∀ j k, MemLp (kPsi n z ph₂ φ j k) 2 (wvol n z ph₂) :=
    fun φ hφ j k => (kPsi_continuous n z hz ph₂ hph φ hφ j k).memLp_of_hasCompactSupport
      (kPsi_hasCompactSupport n z ph₂ φ hφ j k)
  have hmeas : Measurable fun x => ENNReal.ofReal (Real.exp (-ph₂ x)) :=
    (Real.continuous_exp.comp hph.neg).measurable.ennreal_ofReal

  have hw : ∀ g : M → ℂ, ∫ x, g x ∂wvol n z ph₂ =
      ∫ x, (ENNReal.ofReal (Real.exp (-ph₂ x))).toReal • g x ∂vol n z :=
    fun g => integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g
  have key : ∀ φ (hφ : IsTest n z φ) j k (F : Lp (V n) 2 (wvol n z ph₂)),
      ⟪(hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k), F⟫_ℂ =
        ∫ x, (F x k * db n z j φ x - F x j * db n z k φ x) ∂vol n z := by
    intro φ hφ j k F
    rw [MeasureTheory.L2.inner_def]
    have hae := (hmem φ hφ j k).coeFn_toLp
    rw [integral_congr_ae (g := fun x => ⟪kPsi n z ph₂ φ j k x, F x⟫_ℂ)
      (by filter_upwards [hae] with x hx; rw [hx]), hw]
    exact integral_congr_ae (ae_of_all _ fun x => kPsi_inner n z ph₂ φ j k (F x) x)
  refine ⟨⨅ (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) (k : Fin n),
      LinearMap.ker ((innerSL ℂ ((hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k)) :
        Lp (V n) 2 (wvol n z ph₂) →L[ℂ] ℂ) : Lp (V n) 2 (wvol n z ph₂) →ₗ[ℂ] ℂ), ?_, ?_⟩
  · simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun j =>
      isClosed_iInter fun k => ContinuousLinearMap.isClosed_ker _
  · intro F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    unfold IsWeakS
    refine forall_congr' fun φ => forall_congr' fun hφ => forall_congr' fun j =>
      forall_congr' fun k => ?_
    beta_reduce
    rw [key φ hφ j k F]
    simp

end

end ReciprocityTheory.L2DbarEstimates.F
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

theorem hStatement_of (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hAP : APStatement n M) (hTIbp : TStarIbpStatement n M) (hChain : ChainStatement n M)
    (hReg : C.RegStatement) (hGraph : B.GraphSt (V n) MeasureTheory.volume ℝ)
    (hSmooth : B.SmoothSt (V n) MeasureTheory.volume) (hSupp : B.SupportSt (V n) MeasureTheory.volume)
    (hStd : B.StdSt (V n) MeasureTheory.volume) : HStatement n M :=
  hormander n M
    (testIneq n M
      (choice n M chi (psi n M) (shell n M) (leviNormSq n M) hChain)
      (primedIneq n M hAP)
      (closureIneq n M
        (dens n M (cutoff n M (multAdj n M) (multS n M)) (unweightRel n M) (unweightBack n M)
          (localize n M (multDiv n M) (multS n M))
          (chartFlat n M (extend n M) (flatGraph n hGraph hSmooth hSupp hStd))))
      (splitTest n M (kSub n M) (weakSSmooth n M) (sbarDbar n M) hTIbp)
      (locality n M) (weakSSmooth n M) (sbarDbar n M))
    (regM n M hReg (extend n M))

end ReciprocityTheory.L2DbarEstimates.F
end
end
