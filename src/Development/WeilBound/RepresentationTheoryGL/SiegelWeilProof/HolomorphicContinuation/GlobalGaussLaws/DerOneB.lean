module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneSt
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRangeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul

section

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaInv

def rmulEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) :
    GlobalTheory.AutomorphicL2Unitary.Quot Γ ≃ᵐ GlobalTheory.AutomorphicL2Unitary.Quot Γ where
  toFun := rmul Γ g
  invFun := rmul Γ g⁻¹
  left_inv q := by rw [← rmul_mul, mul_inv_cancel, rmul_one]
  right_inv q := by rw [← rmul_mul, inv_mul_cancel, rmul_one]
  measurable_toFun := measurable_rmul g
  measurable_invFun := measurable_rmul g⁻¹

end GlobalTheory.ThetaInv
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneAbs

section

@[expose] public section

noncomputable section

open MeasureTheory intervalIntegral

namespace PositivityTheory.Rg.Sw.Glob.DerOneAbsH

theorem integral_deriv_zero {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hae : ∀ ξ, AEMeasurable (fun p : X × ℝ => ‖F' p.1 p.2 ξ‖ₑ) (m.prod μ) := fun ξ => (hmeas ξ).enorm
  have hle : ∀ ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≤ ∫⁻ p, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) :=
    fun ξ => lintegral_mono fun p => ENNReal.le_tsum (f := fun ξ => ‖F' p.1 p.2 ξ‖ₑ) ξ
  have hI : ∀ ξ, Integrable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod μ) := fun ξ =>
    ⟨hmeas ξ, lt_of_le_of_lt (hle ξ) hfin.lt_top⟩
  have htsum : ∑' ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≠ ⊤ := by
    rw [← lintegral_tsum hae]; exact hfin

  have hftc : ∀ x ξ, ∫ t, F' x t ξ ∂μ = F x 1 ξ - F x 0 ξ := by
    intro x ξ
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x ξ) ((hcont x ξ).intervalIntegrable 0 1)

  have hswap : ∀ ξ, ∫ x, (∫ t, F' x t ξ ∂μ) ∂m = ∫ t, (∫ x, F' x t ξ ∂m) ∂μ := fun ξ =>
    integral_integral_swap (f := fun x t => F' x t ξ) (hI ξ)

  have hbx : ∑' ξ, ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≤ ∫⁻ x, ∫⁻ t, ‖F' x t ξ‖ₑ ∂μ ∂m :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod _ (hae ξ)).symm
  have hbt : ∑' ξ, ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≤ ∫⁻ t, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ :=
          lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod_symm _ (hae ξ)).symm
  have S1 : ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_left.aestronglyMeasurable) hbx
  have S2 : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_right.aestronglyMeasurable) hbt

  have hslice : ∀ᵐ t ∂μ, ∀ ξ, AEStronglyMeasurable (fun x => F' x t ξ) m := by
    rw [ae_all_iff]
    intro ξ
    exact ((hmeas ξ).prod_swap).prodMk_left
  have hfinT : ∀ᵐ t ∂μ, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ≠ ⊤ := by
    have hmξ : ∀ ξ, AEMeasurable (fun t => ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := fun ξ => by
      simpa using ((hae ξ).prod_swap).lintegral_prod_right'
    have hm' : AEMeasurable (fun t => ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := AEMeasurable.tsum hmξ
    have : ∫⁻ t, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hmξ]
      refine ne_top_of_le_ne_top htsum (le_of_eq (tsum_congr fun ξ => ?_))
      exact (lintegral_prod_symm _ (hae ξ)).symm
    filter_upwards [ae_lt_top' hm' this] with t ht using ht.ne
  have S3 : ∀ᵐ t ∂μ, ∫ x, ∑' ξ, F' x t ξ ∂m = ∑' ξ, ∫ x, F' x t ξ ∂m := by
    filter_upwards [hslice, hfinT] with t h1 h2 using integral_tsum h1 h2
  have hIoc : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc

  set c := ∫ x, ∑' ξ, F' x 0 ξ ∂m with hc
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc]; simp
  have key : c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := by
    have : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∫ _t, c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [S3, hIoc] with t h1 h2
      rw [← h1, hconst t h2]
    rw [this, MeasureTheory.integral_const, Measure.real, hμ1, ENNReal.toReal_one, one_smul]
  have hsub : ∀ᵐ x ∂m, ∑' ξ, ∫ t, F' x t ξ ∂μ = ∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ := by
    filter_upwards [hsum0, hsum1] with x h0 h1
    simp only [hftc]
    exact (h1.of_norm).tsum_sub h0.of_norm
  calc c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := key
    _ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ := S2
    _ = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m := tsum_congr fun ξ => (hswap ξ).symm
    _ = ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m := S1.symm
    _ = ∫ x, (∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ) ∂m := integral_congr_ae hsub
    _ = ∫ x, ∑' ξ, F x 1 ξ ∂m - ∫ x, ∑' ξ, F x 0 ξ ∂m := integral_sub hint1 hint0
    _ = 0 := by rw [hends, sub_self]

end PositivityTheory.Rg.Sw.Glob.DerOneAbsH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneB

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneBH

variable {D : D7} {n : ℕ}

theorem mt_mul' (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem shiftPt (V : HSp D) (x k : GA D V) (y : Mx D V.rank n) :
    HMul.hMul (mt V (x * k⁻¹)⁻¹) y = HMul.hMul (mt V k) (HMul.hMul (mt V x⁻¹) y) := by
  rw [mul_inv_rev, inv_inv, mt_mul', Matrix.mul_assoc]

theorem leftInv_absTheta (V : HSp D) (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show ‖φ (HMul.hMul (mt V (γ * h)⁻¹) (rat ξ))‖ₑ = ‖φ (HMul.hMul (mt V h⁻¹) (rat (u.1 * ξ)))‖ₑ
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

section Quot

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure]

theorem absTheta_eq (φ : Mx D V.rank n → ℂ) (y : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V φ y =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (rat ξ : Mx D V.rank n))‖ₑ := rfl

theorem absThetaInt_eq (φ : Mx D V.rank n → ℂ) :
    GlobalTheory.SiegelFormula.absThetaInt V ν φ = ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V ν := rfl

theorem int_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ∫ q, descend (GQ V) f q ∂autMeasure V ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, integral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact integral_congr_ae (.of_forall fun x => hf.descend_mk x)

theorem lint_q (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) :
    ∫⁻ q, descend (GQ V) f q ∂autMeasure V ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, lintegral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact lintegral_congr fun x => hf.descend_mk x

theorem intg_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν)) :
    Integrable f (ν.restrict (stdDom (GQ V))) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [← memLp_one_iff_integrable] at hi ⊢
  have := (memLp_quotMeasure_iff (isFundamentalDomain_stdDom (GQ V) ν)).1 hi
  rwa [hf.lift_descend] at this

theorem desc_r {X' : Type} (f : GA D V → X') (hf : LeftInv (GQ V) f) (k : GA D V) (q : GlobalTheory.AutomorphicL2Unitary.Quot (GQ V)) :
    descend (GQ V) (fun x => f (x * k)) q = descend (GQ V) f (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k q) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  induction q using Quotient.inductionOn with
  | h x => exact ((hf.mul_right k).descend_mk x).trans (hf.descend_mk (x * k)).symm

theorem mp_r (k : GA D V) :
    MeasurePreserving (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k) (autMeasure V ν) (autMeasure V ν) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : ν.IsMulRightInvariant := GlobalTheory.RegSch.Ibp.isMulRightInvariant ν
  exact measurePreserving_rmul k

theorem int_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫ x in stdDom (GQ V), f (x * k) ∂ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  rw [← int_q V ν _ (hf.mul_right k), ← int_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).integral_comp' (descend (GQ V) f)

theorem lint_r (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫⁻ x in stdDom (GQ V), f (x * k) ∂ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  rw [← lint_q V ν _ (hf.mul_right k), ← lint_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (descend (GQ V) f)

theorem intg_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν))
    (k : GA D V) : Integrable (fun x => f (x * k)) (ν.restrict (stdDom (GQ V))) := by
  refine intg_q V ν _ (hf.mul_right k) ?_
  have e : descend (GQ V) (fun x => f (x * k)) = descend (GQ V) f ∘ GlobalTheory.ThetaInv.rmulEquiv (GQ V) k :=
    funext fun q => desc_r V f hf k q
  rw [e]
  exact ((mp_r V ν k).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi

end Quot

section Kernel

variable (V : HSp D)

def tK (φ : Mx D V.rank n → ℂ) (x : GA D V) : ℂ :=
  ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, φ (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n))

def FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) : ℂ :=
  φ (HMul.hMul (Formalism.L2.Theta.mt V (hh t)) (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)))

theorem leftInv_tK (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (tK V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show φ (HMul.hMul (Formalism.L2.Theta.mt V (γ * h)⁻¹) (rat ξ)) = φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (rat (u.1 * ξ)))
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

theorem tsum_FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, FF V φ hh x t ξ = tK V φ (x * (hh t)⁻¹) :=
  tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

theorem tsum_nFF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, ‖FF V φ hh x t ξ‖ₑ = GlobalTheory.SiegelFormula.absTheta V φ (x * (hh t)⁻¹) := by
  rw [absTheta_eq]
  exact tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

end Kernel

end PositivityTheory.Rg.Sw.Glob.DerOneBH

namespace PositivityTheory.Rg.Sw.Glob

open DerOneBH


theorem derivOne_of (hW : GlobalTheory.Published.WeilThetaConvergence) (hC : DerOneH.CurveSt) : DerivOne := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX Θ Θ' hΘ'
  obtain ⟨h0, -, hΦ⟩ := hC D n V θ τ s ε fr X hx.hθ hx.hs hx.hfr hX
  haveI : ν.IsHaarMeasure := hx.hν
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (autMeasure V ν) := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure ν
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  letI : MeasurableSpace (Matrix (Fin V.rank) (Fin n) D.host.E) := ⊤
  haveI : MeasurableSingletonClass (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun _ => trivial⟩
  haveI : IsFiniteMeasure (ν.restrict (stdDom (GQ V))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ (isFundamentalDomain_stdDom (GQ V) ν)]
        exact measure_lt_top _ _⟩
  have hT : ∀ Φ : schwartzA θ V.rank n, theta ω Φ 1 = tK V Φ.1 := fun Φ => by
    funext x
    simp only [theta, map_one, Module.End.one_apply, tK]
  have hfinA : ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤ :=
    fun Φ => hW D n V hx.hn (Or.inr hx.hr.2.2) θ hx.hθ ν hx.hν Φ
  have hfinA' : ∀ (Φ : schwartzA θ V.rank n) (k : GA D V),
      ∫⁻ x in stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V Φ.1 (x * k) ∂ν = GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 :=
    fun Φ k => by
      rw [lint_r V ν _ (leftInv_absTheta V Φ.1) k, ← lint_q V ν _ (leftInv_absTheta V Φ.1), absThetaInt_eq]
  have hintT : ∀ Φ : schwartzA θ V.rank n, Integrable (descend (GQ V) (tK V Φ.1)) (autMeasure V ν) := fun Φ => by
    rw [← hT]; exact GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hx.hn hx.hr.2.2 θ hx.hθ ω ν hx.hν Φ 1
  have hhinv0 : (DerOneH.hhT θ V τ fr X 0)⁻¹ = 1 := by rw [h0, inv_one]
  have hmeasA : ∀ (Φ : schwartzA θ V.rank n) (t : ℝ), Measurable fun x : GA D V =>
      ∑' ξ, ‖FF V Φ.1 (DerOneH.hhT θ V τ fr X) x t ξ‖ₑ :=
    fun Φ t => Measurable.tsum fun ξ =>
      (((hΦ Φ).1 (rat ξ : Mx D V.rank n)).comp (Continuous.prodMk continuous_id continuous_const)).enorm.measurable
  have key := DerOneAbsH.integral_deriv_zero (ν.restrict (stdDom (GQ V)))
    (FF V Θ.1 (DerOneH.hhT θ V τ fr X)) (FF V Θ'.1 (DerOneH.hhT θ V τ fr X))
    (fun x ξ t _ => by
      have := (hΦ Θ).2 (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)) t
      rw [← hΘ'] at this
      exact this)
    (fun x ξ => by
      have h := ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).comp
        (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (x, t))
      exact h)
    (fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).aestronglyMeasurable)
    (by
      have hm : Measurable fun p : GA D V × ℝ => ∑' ξ, ‖FF V Θ'.1 (DerOneH.hhT θ V τ fr X) p.1 p.2 ξ‖ₑ :=
        Measurable.tsum fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).enorm.measurable
      rw [lintegral_prod_symm _ hm.aemeasurable]
      simp only [tsum_nFF, hfinA']
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      simp only [sub_zero, ENNReal.ofReal_one, mul_one]
      exact (hfinA Θ').ne)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 0).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 1).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact intg_q V ν _ (leftInv_tK V Θ.1) (hintT Θ))
    (by
      simp only [tsum_FF]
      exact intg_r V ν _ (leftInv_tK V Θ.1) (hintT Θ) _)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ.1) _)
    (fun t _ => by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ'.1) _)
  simp only [tsum_FF, hhinv0, mul_one] at key
  rw [thetaInt, hT, average_eq, int_q V ν _ (leftInv_tK V Θ'.1), key, smul_zero]

end PositivityTheory.Rg.Sw.Glob
end
end
end
