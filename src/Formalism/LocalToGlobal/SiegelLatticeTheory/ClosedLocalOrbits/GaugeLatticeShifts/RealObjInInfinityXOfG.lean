module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTrunc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsPoint
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsDefs
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrameLocX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWSec
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEnergy

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem continuous_hsA_Xop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (μS ν μS' ν' : Measure G) (d : ℝ)
    (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) := by
  have hc : ∀ a : HH, Continuous (fun g => σ g a) := hσ.2.2.2
  unfold hsA Xop sand
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_norm.comp ?_).pow 2
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply]
  exact ((ContinuousLinearMap.adjoint _).continuous.comp (hc _)).const_smul _

theorem lintegral_hsA_Xop {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hSch : IsSchur μ σ d)
    (μS ν μS' ν' : Measure G) (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    ∫⁻ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) ∂μ =
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W A (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' A' (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
  have hd : 0 < d := hSch.1
  have h1 : ∀ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) =
      ENNReal.ofReal (d ^ 2) *
        ENNReal.ofReal (hsA (sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') g)) := by
    intro g
    rw [Xop, hsA_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg d)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_hsA_sand hSch,
    ← ENNReal.ofReal_mul (sq_nonneg d)]
  congr 1
  simp only [Yop_apply_basis]
  field_simp

theorem tendsto_energy {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by
  have key : ∀ n, (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n) =
      ENNReal.ofReal (d * (N n / (a n).toReal) * (N' n / (b n).toReal)) := by
    intro n
    obtain ⟨ha0, hat⟩ := ha n
    obtain ⟨hb0, hbt⟩ := hb n
    have ha' : 0 < (a n).toReal := ENNReal.toReal_pos ha0.ne' hat.ne
    have hb' : 0 < (b n).toReal := ENNReal.toReal_pos hb0.ne' hbt.ne
    have hab : (a n * b n)⁻¹ = ENNReal.ofReal (((a n).toReal * (b n).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ← ENNReal.toReal_mul,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat.ne hbt.ne)]
    rw [hab, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos ha' hb').le)]
    congr 1
    field_simp
  simp_rw [key]
  apply ENNReal.tendsto_ofReal
  have hlim := (hN.const_mul d).mul hN'
  rwa [show d * (1 / d) * (1 / d) = 1 / d by field_simp] at hlim

end Formalism.L2.S.Pv.EnergyAbs
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsMain

section

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

theorem energyAbs_holds : EnergyAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ _ HH _ _ _ σ d w V V' _ _ _ _ _ _ S S' μS μS' ν ν' τ τ' W W' C _ m h
    hσ hSch hw hS hS' hF hF' hν hν' hq hq' hW hW' hD hhm hOOi hB hC hC'
  haveI := hν
  haveI := hν'
  haveI : SigmaFinite μS := hS.2.2.2.2.1
  haveI : SigmaFinite μS' := hS'.2.2.2.2.1
  obtain ⟨Ω, hΩ, hΩF⟩ := folner_seq hS hF
  obtain ⟨Ω', hΩ', hΩF'⟩ := folner_seq hS' hF'
  have hlim := folner_limit hσ hSch hw hS hν hq hW hC Ω hΩ hΩF
  have hlim' := folner_limit hσ hSch hw hS' hν' hq' hW' hC' Ω' hΩ' hΩF'
  have hd : 0 < d := hSch.1
  set φn : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g))
    with hφn
  have hφm : ∀ n, Measurable (φn n) := fun n =>
    ENNReal.measurable_ofReal.comp (continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)).measurable
  set Fn : ℕ → C → ℝ≥0∞ := fun n c => (μS (Ω n) * μS' (Ω' n))⁻¹ *
    ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS with hFn
  have hpt : ∀ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ≤ liminf (fun n => Fn n c) atTop :=
    fun c => point_lower hσ hS hS' hq hq' hW hW' Ω Ω' hΩ hΩ' hΩF hΩF'
      (fun n => continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)) (h c) (hB c)
  have hinner : ∀ n, Measurable (fun c => ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS) := by
    intro n
    have h3 : Measurable (fun r : (C × G) × G => φn n (r.1.2 * h r.1.1 * r.2⁻¹)) :=
      (hφm n).comp (((measurable_snd.comp measurable_fst).mul (hhm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hmeasF : ∀ n, Measurable (Fn n) := fun n => (hinner n).const_mul _
  have hint : ∀ n, ∫⁻ c, Fn n c ∂m = (μS (Ω n) * μS' (Ω' n))⁻¹ *
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' (Ω' n) (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
    intro n
    rw [lintegral_const_mul _ (hinner n), ← hD (φn n) (hφm n), lintegral_hsA_Xop hSch]
  have htend := tendsto_energy hd (fun n => ⟨(hΩ n).2.2.1, (hΩ n).2.2.2⟩)
    (fun n => ⟨(hΩ' n).2.2.1, (hΩ' n).2.2.2⟩) hlim hlim'
  calc ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m
      ≤ ∫⁻ c, liminf (fun n => Fn n c) atTop ∂m := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ c, Fn n c ∂m) atTop := lintegral_liminf_le hmeasF
    _ = ENNReal.ofReal (1 / d) := by
        simp only [hint]
        exact htend.liminf_eq

end Formalism.L2.S.Pv.EnergyAbs
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWGlob

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepSection_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSection := by
  intro D X u u' sc hsc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  let i0 : Fin D.R.k := ⟨0, hk⟩
  choose w Fw using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u v
  choose w' Fw' using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u' v
  have hdim : ∀ v, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun v => (ProductExactness.frameLoc_X X u u v).dim
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hT' : 0 < Tw (D := D) u' := ProductExactness.Tw_pos u'
  refine ⟨fun c v => secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 (c v), ?_, ?_⟩
  · exact Measurable.of_eval fun v => (measurable_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0).comp
      (measurable_pi_apply v)
  · intro c hc v
    have hcv := hc v
    have hg := ProductExactness.normSq_last_sub_pos_of_Gv_diagonal_pos (Tw (D := D) u) (Tw (D := D) u') (c v) hcv.2
    exact zhat_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 hcv.1 hg

end Formalism.L2.S.Pv.SecW
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAt

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepIntAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StepConvAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

def StepEnergyAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem stepEnergyAt_of_inst (D : D7) (hE : EnergyAbs) (hS : StepSchurG) (hG : StepSubG) (hSec : StepSection)
    (hC : StepConvAt D) (hI : StepIntAt D) : StepEnergyAt D := by
  classical
  intro X u u' sc hsc h27 _
  obtain ⟨hUR, hSch, hw, -⟩ := hS D X
  obtain ⟨hHu, hFu, -, -, hSFu⟩ := hG D X u
  obtain ⟨hHu', hFu', -, -, hSFu'⟩ := hG D X u'
  obtain ⟨hh, hhm, hhd⟩ := hSec D X u u' sc hsc
  have hGood : MeasurableSet (Good X u u') := by
    rw [Formalism.L2.SG.RealObj.EnergyCut.good_eq_pi X u u']
    exact MeasurableSet.univ_pi fun _ => Formalism.L2.SG.RealObj.EnergyCut.goodV_meas u u'
  by_cases hne : (Good X u u').Nonempty
  swap
  · have h0 : Good X u u' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [intOOe, nuM, h0]
  obtain ⟨c₀, hc₀⟩ := hne
  let g : Cinf X → X.B.I.Ginf := (Good X u u').piecewise hh (fun _ => hh c₀)
  have hgm : Measurable g := Measurable.piecewise hGood hhm measurable_const
  have hgG : ∀ c ∈ Good X u u', g c = hh c := fun c hc => Set.piecewise_eq_of_mem _ _ _ hc
  have hgd : ∀ c, ∃ c' ∈ Good X u u', HasDiag X u u' sc c' (g c) := by
    intro c
    by_cases hc : c ∈ Good X u u'
    · exact ⟨c, hc, by rw [hgG c hc]; exact hhd c hc⟩
    · refine ⟨c₀, hc₀, ?_⟩
      have : g c = hh c₀ := Set.piecewise_eq_of_notMem _ _ _ hc
      rw [this]; exact hhd c₀ hc₀
  have hgD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (g c) := fun c hc => by
    rw [hgG c hc]; exact hhd c hc
  have hOfD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (hOf X u u' sc c) := by
    intro c hc
    have hex : ∃ γ, HasDiag X u u' sc c γ := ⟨hh c, hhd c hc⟩
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  have hD : Disint X u u' sc (DisintegrationConstant X u u' sc) := by
    have e : DisintegrationConstant X u u' sc = h27.choose := dif_pos h27
    rw [e]
    exact h27.choose_spec.2
  have hm : Measurable fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) :=
    ENNReal.measurable_ofReal.comp ((Formalism.L2.SG.RealObj.InfCut.wt_cont X u u').measurable.const_mul _)
  have hDis : Formalism.L2.SG.Pf.EnergyAbs.IsDisint (Formalism.L2.SG.ProjRows.muInf X.B.I) (muS X u) (muS X u')
      (nuM X u u' sc) g := by
    intro φ hφ
    rw [hD φ hφ, nuM, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae (ae_restrict_of_forall_mem hGood fun c hc => ?_)
    simp only [Pi.mul_apply]
    congr 1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      InfCut.UnitaryIsometries.StepDiagDC_holds D X u u' sc c hc _ _ (hOfD c hc) (hgD c hc)
    exact (inner_transfer X hG u u' φ hφ _ _ a ha b hb hab).symm
  have key := hE X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ X.B.σs (degX X) (X.B.tens X.B.w)
    (X.Vpi u) (X.Vpi u') (X.SinfU u) (X.SinfU u') (muS X u) (muS X u') (X.nuQ u) (X.nuQ u')
    (tauU X u) (tauU X u') (X.Wu u) (X.Wu u') (Cinf X) inferInstance (nuM X u u' sc) g
    hUR hSch hw hHu hHu' hFu hFu' hSFu hSFu' (fun f hf => X.nuQ_weil u f hf)
    (fun f hf => X.nuQ_weil u' f hf) (isWAbs_of X hS hG u) (isWAbs_of X hS hG u') hDis hgm
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact integrableOn_univ.mp (hI X u u' sc hsc c' hc' (g c) hd))
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact (hC X u u' sc hsc).1 c' hc' (g c) hd)
    ((hC X u u' sc hsc).2 u) ((hC X u u' sc hsc).2 u')
  refine le_trans (le_of_eq ?_) key
  have hae : ∀ᵐ c ∂(nuM X u u' sc), c ∈ Good X u u' := by
    rw [nuM]
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_mem hGood)
  have hIndep : OOIndep X u u' sc := InfCut.ooIndep_of_step X InfCut.UnitaryIsometries.StepDiagDC_holds u u' sc
  unfold intOOe
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with c hc
  rw [hilbertSchmidtSqGram, hIndep c hc _ _ (hOfD c hc) (hgD c hc)]
  simp only [OOinf, TermOp.OO, Measure.restrict_univ]
  rfl

theorem inInfinityXAt (hI : StepIntAt D) (hC : StepConvAt D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc) :
    InInfinityX X u u' sc := by
  have h27 : DisintegrationConstantPositive X u u' sc := InfCut.ProductExactness.haar_disintegration_real_holds D X u u' sc hsc
  have hR := InfCut.ProductExactness.StepReal_holds D X u u' sc hsc
  have hco : CoordOK X u u' sc := by
    refine ⟨hR, fun c hc => ?_⟩
    have hex := hR c hc
    refine hI X u u' sc hsc c hc _ ?_
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  exact ⟨h27, hco, stepEnergyAt_of_inst D S.Pv.EnergyAbs.energyAbs_holds S.Pv.SchurTens.stepSchurG_holds
    S.Pv.HaarSubS.stepSubG_holds S.Pv.SecW.stepSection_holds hC hI X u u' sc hsc h27 hco⟩

end Formalism.L2.SG.RealObj.EnergyInst
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inInfinityX_ofG (hI : Formalism.L2.SG.RealObj.EnergyInt.StepIntG) (hC : Formalism.L2.S.Pv.ConvG.StepConvG)
    {D : D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : InInfinityX X u u' sc := Formalism.L2.SG.RealObj.EnergyInst.inInfinityXAt (X := X) (hI D hg) (hC D hg) u u' sc hsc

end Formalism.L2.SG.Pf
end
end
