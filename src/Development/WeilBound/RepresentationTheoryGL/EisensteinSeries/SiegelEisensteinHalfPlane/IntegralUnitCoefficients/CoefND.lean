module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRangeStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompactStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawaStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MatchMono
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SphericalBigCell.IfrBAddOfWeilThetaConvergence
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.UnrWhitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.FactorCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.WXMain
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.ChapterTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Imports
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRangeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.GenAHf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top7
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WlocTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactParts

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWDict

open PositivityTheory.PfSWUS GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

theorem dictKA_of_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  intro hF hW hI hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, hsum, hmono⟩ := hF D n V ψ χ θ μ ω H l s ν Φ hS hR k hk
  refine ⟨N, φs, fun j => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
    IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k N φs hmono
    exact ⟨t, fun z hz => by rw [hsum]; exact ht z hz⟩
  · rw [hsum, hI D n V ψ χ θ μ ω H l s ν Φ hS hR β hβ a N φs hmono, Finset.mul_sum]
  · exact fun j => hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk (φs j) (hmono j)

end GlobalTheory.CompanionTheory.SWDict

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactPartsStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionary_maximal_compact_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  first | exact @GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | exact GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | (intros; apply GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittakerStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nondegenerate_of_whittaker : PositivityTheory.PfSWUS.NDOfWhit := by
  first | exact @GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | exact GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | (intros; apply GlobalTheory.CompanionTheory.SWGlue.ndOfWhit <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergenceStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_coefficient_of_convergence : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaCoef := by
  first | exact @GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef | exact GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef | (intros; apply GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivityStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.whittaker_additivity : PositivityTheory.PfSWUS.WhitTAdd := by
  first | exact @GlobalTheory.CompanionTheory.WhitAdd.whitTAdd | exact GlobalTheory.CompanionTheory.WhitAdd.whitTAdd | (intros; apply GlobalTheory.CompanionTheory.WhitAdd.whitTAdd <;> assumption)
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitGenLt

section

@[expose] public section

namespace PositivityTheory.PfSWUS

open PositivityTheory.SiegelWeilFormula

theorem whitGenLt : PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt :=
  Gen.whitGenLtOf SwLocFin.locFin2 Gunr.unrWhit (GReal.realWhit_of PositivityTheory.Rg.Sw.WR.wr) GFac.factorX
    PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA

end PositivityTheory.PfSWUS
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.Bridge

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Lit1.SWUS

theorem siegelWeilUnitarySchrodinger_of_lit :
    GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit → GlobalTheory.Published.WeilThetaConvergence →
      GlobalTheory.Published.SiegelWeilUnitarySchrodinger := by
  intro hL hW D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ
  have hn : 0 < n := by omega
  have hS := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have e : ∀ z, sect ω H Φ z = stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) z :=
    fun z => funext fun g => mul_comm _ _
  refine ⟨fun g => GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hn a3 θ hθ ω ν hν Φ g, fun z hz => ⟨?_, fun g => ?_⟩,
    hL D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ⟩
  · exact GlobalTheory.StdUnn.LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hχ hω H hH Φ z
  · rw [e]; exact GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hS hz g

end PositivityTheory.Lit1.SWUS

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CoefND

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilCoefficients

open PositivityTheory.Rg.Sw.Glob PositivityTheory.PfSWUS

theorem coefND : CoefND :=
  GlobalTheory.T.nondegenerate_of_whittaker GlobalTheory.T.unfolding_holds (GlobalTheory.T.theta_coefficient_of_convergence wtc)
    (GlobalTheory.T.whittaker_nondegenerate_of_iwasawa (GlobalTheory.T.whittaker_maximal_compact_general whitGenLt (GlobalTheory.T.dictionary_maximal_compact_parts GlobalTheory.T.fock_splitting_maximal_compact GlobalTheory.T.whittaker_additivity
      (PositivityTheory.PfSWUS.HandIAdd.ifrBAdd_of_weilThetaConvergence wtc) PositivityTheory.PfSWUS.SwMatch.matchMono)
      GlobalTheory.T.anisotropy_of_range))

theorem lit : GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit := by
  intro D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ g
  exact top7 genA_hf (gIdil_gen wtc genA_hf) coefND D n V ψ χ θ μ ω H l s ν Φ
    ⟨hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω, hH, hl, hs, hν, hΦ⟩ ⟨a1, a2, a3⟩ (by omega) g

theorem field : GlobalTheory.Published.SiegelWeilUnitarySchrodinger :=
  PositivityTheory.Lit1.SWUS.siegelWeilUnitarySchrodinger_of_lit lit wtc

end PositivityTheory.SiegelWeilCoefficients

end
end
end
