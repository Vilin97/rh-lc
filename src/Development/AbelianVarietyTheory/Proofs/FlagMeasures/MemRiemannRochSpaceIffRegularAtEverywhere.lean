import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.NonGenericCompare

section Place
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [StarRing E]
variable (o : Type) [CommRing o] [Algebra o F] [Algebra o E]

variable {o}

end Place

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [StarRing E]
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Algebra o F]
  [IsFractionRing o F] [Algebra o E] [IsScalarTower o F E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

namespace Match
variable {P : LocNG.FPair H r} {D : Data o F E V r} {S : Frames M.L r k}
variable (m : Match P D) (c : Coord P S)

include m

include c in

omit m in

end Match

end GlobalTheory.NonGenericCompare
