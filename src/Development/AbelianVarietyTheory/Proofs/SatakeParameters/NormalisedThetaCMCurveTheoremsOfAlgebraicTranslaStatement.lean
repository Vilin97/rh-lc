module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnitConjugateNormTwoPowerTwoAdic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntSExpMulTranslate
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodOrdinaryModelAtTwoCmLatticeSevenModEight

section

@[expose] public section

namespace GlobalTheory.ThLoc

theorem goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight : Formalism.L2.Th1.Top.GoodModelTwo :=
  GlobalTheory.ThLoc.GoodTwo.goodModelTwo

end GlobalTheory.ThLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocJetsAll

section

@[expose] public section

namespace GlobalTheory.ThLoc

theorem locJets_all :
    Formalism.L2.Th1.GD.IntOpLoc ∧ Formalism.L2.Th1.GD.IntOpTwoLoc ∧
      (Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc) :=
  ⟨LocJets.jetsOdd, LocJets.jetsTwo, LocJets.shape⟩

end GlobalTheory.ThLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTransla

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.ThLoc

theorem inputs_of_algT (hT : Formalism.L2.KerInert.AlgTAll) : Inputs := by
  exact
    { jInt := cm1
      modelTwo := goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight
      jetsOdd := locJets_all.1
      jetsTwo := locJets_all.2.1
      jetsThree := thetaZJetsThree
      shape := locJets_all.2.2
      algT := hT
      lamExt := place_extends_to_iso }

end GlobalTheory.ThLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTranslaStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates : Formalism.L2.KerInert.AlgTAll → GlobalTheory.ThLoc.Inputs := by
  first | exact @GlobalTheory.ThLoc.inputs_of_algT | exact GlobalTheory.ThLoc.inputs_of_algT | (intros; apply GlobalTheory.ThLoc.inputs_of_algT <;> assumption)
end
end
