import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.SelSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.Divisibility.ColPins
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

theorem isJ_smul {D : D7} {u : D.what₂.Word} {S : D.what₂.Tau → SPar} {M : Formalism.IndefR.Mult.DSModel D.sp.X' S}
    {j : SmT M →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)} (h : GlobalTheory.Core.Rk.Top.IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    GlobalTheory.Core.Rk.Top.IsJ u M (a • j) where
  inj := fun _ _ e => h.inj (smul_right_injective _ ha e)
  range := (LinearMap.range_smul j a ha).trans h.range
  eqv := fun τ g hg v w hw y y' hy => congrArg (a * ·) (h.eqv τ g hg v w hw y y' hy)

section True

open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

end True

theorem levG_one {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad} (K : Formalism.L2.Forms.ClassesAtPrimes M bad)
    {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (h1 : ∀ g, g ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1)
    (h2 : ∀ g (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → χ g = star ((K.lev.chi κ : ℂˣ) : ℂ)) : LevG K 1 J χ := by
  simp only [LevG, inv_one, one_mul, mul_one]
  exact ⟨h1, h2⟩

set_option maxHeartbeats 2000000 in

end GlobalTheory.TopVal
