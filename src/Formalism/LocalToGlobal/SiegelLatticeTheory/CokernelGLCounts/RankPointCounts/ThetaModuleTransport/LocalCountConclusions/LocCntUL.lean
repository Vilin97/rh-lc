module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.ThetaMbeU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.CornerU
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.DetEqEllUB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.LocCntULOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.CoordUHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BwdEx
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.Partial

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

theorem locCntUL_of'
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbeU M r n false)) : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  locCntUL_of h1 (fun _ _ _ _ _ _ _ _ _ M _ r => mbeU_holds M r)
    (fun _ _ _ _ _ _ _ _ _ M _ r => cornerU_holds M r)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOfAlg

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

theorem thetaMbeU_false_of_alg (h2 : AlgAll) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (r n : ℕ) : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.ThetaMbeU M r n false :=
  thetaMbeU_false_of coordU_holds h2 M r n

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.PartialA

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

theorem locCntUL_of_alg (h : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll) : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  locCntUL_of' (fun _ _ _ _ _ _ _ _ _ M _ r n => Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.thetaMbeU_false_of_alg h M r n)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.AlgAllHolds

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUL

section

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules

theorem localCountUnitLocal_holds : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.locCntUL_of_alg Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.algAll_holds

end Formalism.L2.SG.LocalCountModules
end
end
