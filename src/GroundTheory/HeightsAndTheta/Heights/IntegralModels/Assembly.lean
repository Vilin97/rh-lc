import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
