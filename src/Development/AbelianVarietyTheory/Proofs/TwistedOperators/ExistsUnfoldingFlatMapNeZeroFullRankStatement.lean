module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBumpStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupportStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompactStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinateStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordin

section

namespace I195MixedCoordinates_acb50ed7a993b068b784d65f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_acb50ed7a993b068b784d65f

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ClassFromMixed.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ), p.Is dV dW x ψ → ∀ (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → (∀ x', (_root_.I195MixedCoordinates_acb50ed7a993b068b784d65f.source dV) W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ a ∈ p.A₁, ∀ z, β₁ (z + a) = β₁ z) → (∀ z, β₁ z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (x + r) ∈ p.A₁) → (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧ ∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS p x hp β₁ g' Φ hΦ hmix hper hsupp
  obtain ⟨hX, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Φ hΦ
  change ∀ x', I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g' at hmix
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _) hΦ).1 V₀ ρ dV vS
      fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extX W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x'
    rw [hX, hmix, hmix, hper a ha]
  · refine (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _)
      (GlobalTheory.WeilVacMove.isTheta_smul _ hΦ)).1 V₀ ρ dV vS fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extY W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x'
    have hsmul := GlobalTheory.HandHom.mixS_smul dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a))) Φ x'
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x' = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' at hsmul
    rw [hY, hsmul, hmix]
    by_cases hb : β₁ x' = 0
    · rw [hb, zero_smul, smul_zero, smul_zero]
    · obtain ⟨r, hr, hx'⟩ := hsupp x' hb
      have hfinA : MxAt (fun _ => True) a := hp.a₂.fin a ha
      have hYa : (dV.extY W a).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul]
        have : a.map (infPart D) = 0 := Matrix.ext fun i j => GlobalTheory.FinPlLoc.infPart_of_idAt (hfinA i j)
        rw [this, Matrix.zero_mul]
      have hXr : (dV.extX W r).map (finPart D) = 0 := by
        rw [HypDec.extX_apply, Matrix.map_mul, hr, Matrix.zero_mul]
      have h1 : ψ (symplO V W (dV.extX W (x' - (x + r))) (dV.extY W a)) = 1 :=
        (hp.dualA _ (hp.a₁.fin _ hx')).1 hx' a ha
      have hsplit : x' = x + r + (x' - (x + r)) := by abel
      have key : ψ (symplO V W (dV.extX W x') (dV.extY W a)) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) := by
        rw [hsplit, map_add (f := _), map_add (f := _), GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
          GlobalTheory.SplitScalar.symplO_real_fin V W hXr hYa, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1,
          AddChar.map_zero_eq_one, mul_one, mul_one]
      rw [key]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordinStatement

section

namespace I195MixedCoordinates_684fc6d6042eff6a430ef673

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_684fc6d6042eff6a430ef673

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.class_conditions_isotropicHom_from_firstMixedCoordinate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ), p.Is dV dW x ψ → ∀ (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → (∀ x', (_root_.I195MixedCoordinates_684fc6d6042eff6a430ef673.source dV) W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ a ∈ p.A₁, ∀ z, β₁ (z + a) = β₁ z) → (∀ z, β₁ z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (x + r) ∈ p.A₁) → (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧ ∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ := by
  first | exact @GlobalTheory.ClassFromMixed.main | exact GlobalTheory.ClassFromMixed.main | (intros; apply GlobalTheory.ClassFromMixed.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finsetSum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhdsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  first | exact @GlobalTheory.PosNhdsChar.posNhds | exact GlobalTheory.PosNhdsChar.posNhds | (intros; apply GlobalTheory.PosNhdsChar.posNhds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnfoldingFlatMapNeZeroFullRank

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinNe

variable {D : D7}

theorem left_inv_of_li {n ρ : ℕ} (x₀ : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x₀.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) D.host.E, L * x₀ = 1 := by
  have hinj : Function.Injective (Matrix.toLin' x₀) := by
    show Function.Injective x₀.mulVec
    exact mulVec_injective_iff.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x₀) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' x₀]
  rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem flat_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hx₀ p hp
  obtain ⟨g, hgv, hg0⟩ := hp.vac₀
  obtain ⟨β₂, hβ₂, hβ₂y, hβ₂per, hβ₂supp⟩ := GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice D V₀ W W₀ σ dW p.B₂ hp.b₂ y
  obtain ⟨L, hL⟩ := left_inv_of_li x₀ hx₀
  obtain ⟨b, hb, hbx, hb01, hbsupp, hbper⟩ := exists_bump_le (rat x₀) p.A₁ hp.a₁ _
    (GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds D ψ hψ W.rank ρ (rat L) (rat x₀))
  have hpos : ∀ u : UX D ρ, b (rat x₀ ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re := by
    intro u hu
    obtain ⟨r, hr, hrU, hrA⟩ := hbsupp _ hu
    rw [GlobalTheory.T.genericCharacter_eq_realPartChar_on_bumpSupport D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr hrA]
    simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using hrU
  have hcpt : HasCompactSupport (fun u : UX D ρ => b (rat x₀ ⬝ u.1.1)) := by
    refine HasCompactSupport.intro' (GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact D W.rank ρ x₀ hx₀ _ (HasCompactSupport.isCompact (f := fun z => (b z : ℂ)) hb.supp))
      ((isClosed_tsupport _).preimage (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))) ?_
    intro u hu
    by_contra h
    exact hu (subset_tsupport _ (by simpa using h))
  obtain ⟨g', hg', hg'm⟩ := GlobalTheory.T.mixedModelTarget_bump_mul_coreTheta_exists D ψ hψ V₀ W W₀ σ dW s.vT β₂ g hβ₂ hgv.1
  obtain ⟨Φ, hΦ, hΦm⟩ := GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ V V₀ W ρ dV s.vS (fun z => (b z : ℂ)) g' hb hg'
  have hbper' : ∀ a ∈ p.A₁, ∀ z, (fun z => (b z : ℂ)) (z + a) = (fun z => (b z : ℂ)) z := fun a ha z => by
    simp only [hbper a ha z]
  have hbsupp' : ∀ z, (fun z => (b z : ℂ)) z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (rat x₀ + r) ∈ p.A₁ :=
    fun z hz => by
      obtain ⟨r, hr, -, hrA⟩ := hbsupp z (by simpa using hz)
      exact ⟨r, hr, hrA⟩
  obtain ⟨hB₁, hB₂, hvac⟩ := GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vT p (rat x₀) y hp β₂ g g' hgv hg' hg'm hβ₂per hβ₂supp
  obtain ⟨hA₁, hA₂⟩ := GlobalTheory.T.class_conditions_isotropicHom_from_firstMixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p (rat x₀) hp _ g' Φ hΦ hΦm hbper' hbsupp'
  obtain ⟨hC₁, hC₂, hCv⟩ := GlobalTheory.T.class_conditions_core_from_mixedCoordinateFunction D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p y _ g' Φ hg' hΦ hΦm hB₁ hB₂ hvac
  refine ⟨Φ, ⟨hΦ, hA₁, hA₂, hC₁, hC₂, hCv⟩, ?_⟩
  exact GlobalTheory.T.flatMap_productDatum_eq_unitriangularIntegral_bump D ψ hψ V V₀ W W₀ ρ σ dV dW s (rat x₀) y b β₂ g g' Φ hg0 hβ₂y hΦm hg'm
    (Complex.continuous_re.comp hb.cont |>.congr fun z => by simp) hbx (fun z => (hb01 z).1) hpos hcpt

end GlobalTheory.AscFinNe

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnfoldingFlatMapNeZeroFullRankStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_unfolding_flatMap_ne_zero_fullRank : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  first | exact @GlobalTheory.AscFinNe.flat_ne_zero | exact GlobalTheory.AscFinNe.flat_ne_zero | (intros; apply GlobalTheory.AscFinNe.flat_ne_zero <;> assumption)
end
end
