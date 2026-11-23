module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOfStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwistStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplitStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReductionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHoldStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.DcCount
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.PUnitAE

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExistsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_conjugacy_exists : PositivityTheory.Rg.BcB.G8.Fin.CjEx := by
  first | exact @GlobalTheory.CompanionTheory.CjEx.cjEx | exact GlobalTheory.CompanionTheory.CjEx.cjEx | (intros; apply GlobalTheory.CompanionTheory.CjEx.cjEx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFactsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_level_facts : PositivityTheory.Rg.BcB.G8.FinLevel := by
  first | exact @GlobalTheory.CompanionTheory.FinLevelTw.finLevel | exact GlobalTheory.CompanionTheory.FinLevelTw.finLevel | (intros; apply GlobalTheory.CompanionTheory.FinLevelTw.finLevel <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishingStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  first | exact @GlobalTheory.CompanionTheory.EulerV.main | exact GlobalTheory.CompanionTheory.EulerV.main | (intros; apply GlobalTheory.CompanionTheory.EulerV.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwistStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_support_of_twist : PositivityTheory.Rg.BcB.G8.Fin.SuppFinOf := by
  first | exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | exact GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | (intros; apply GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatementStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.aux_statement_21 : PositivityTheory.Rg.BcB.G8.Fin.Regroup := by
  first | exact @GlobalTheory.CompanionTheory.RegroupFin.regroup | exact GlobalTheory.CompanionTheory.RegroupFin.regroup | (intros; apply GlobalTheory.CompanionTheory.RegroupFin.regroup <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInertStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_comparison_inert : PositivityTheory.Rg.BcB.G8.Fin.LocCompareInert := by
  first | exact @GlobalTheory.CompanionTheory.LocInert.locCompareInert | exact GlobalTheory.CompanionTheory.LocInert.locCompareInert | (intros; apply GlobalTheory.CompanionTheory.LocInert.locCompareInert <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOfStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_comparison_of : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  first | exact @GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | exact GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | (intros; apply GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFactsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_support_facts : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  first | exact @GlobalTheory.CompanionTheory.TwistOrbit.locSupp | exact GlobalTheory.CompanionTheory.TwistOrbit.locSupp | (intros; apply GlobalTheory.CompanionTheory.TwistOrbit.locSupp <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlacesStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.rational_finite_places : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  first | exact @GlobalTheory.CompanionTheory.RatFinG.ratFin | exact GlobalTheory.CompanionTheory.RatFinG.ratFin | (intros; apply GlobalTheory.CompanionTheory.RatFinG.ratFin <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.FinLevelHolds

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.G8.Fin

theorem kfOC_holds : PositivityTheory.Rg.BcB.G8.KfOC := GlobalTheory.T.finite_kernel_compact_open

theorem finLevel_holds : PositivityTheory.Rg.BcB.G8.FinLevel := GlobalTheory.T.finite_level_facts

theorem suppFin_holds : SuppFin := GlobalTheory.T.finite_support_of_twist GlobalTheory.T.local_support_facts unitAE_holds GlobalTheory.T.rational_finite_places GlobalTheory.T.local_good_reduction

theorem eulerFin_holds : EulerFin :=
  GlobalTheory.T.finite_euler_product_of GlobalTheory.T.finite_conjugacy_exists GlobalTheory.T.finite_restriction_vanishing GlobalTheory.T.aux_statement_21 (GlobalTheory.T.local_comparison_of GlobalTheory.T.local_comparison_inert GlobalTheory.T.local_comparison_split) GlobalTheory.T.local_hypotheses_hold GlobalTheory.T.finite_reindexing

theorem finHalf_holds : PositivityTheory.Rg.BcB.G8.FinHalf :=
  GlobalTheory.T.finite_half_of_twist DcCount_pf GlobalTheory.T.finite_mass_product_formula GlobalTheory.T.rational_finite_places suppFin_holds eulerFin_holds kfOC_holds finLevel_holds

end PositivityTheory.Rg.BcB.G8.Fin
end
end
