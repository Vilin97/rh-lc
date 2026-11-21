module

public import Mathlib
public import Formalism.PeriodIntegrals.ZuckTensor
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.IsLowUnitH
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
public import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.MultGood
public import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

@[expose] public section

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult

namespace Formalism.IndefR.ModelConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lamS_eq (R : Ranks) (P : HCParam R) (i : Fin R.r) : Formalism.MainNotions.S.lamS R P i = ((lamAt P i : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS lamAt
  split_ifs <;> simp

variable {D : D7}

variable {S : D.what₂.Tau → SPar}

end Formalism.IndefR.ModelConjugation
