module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifiStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDownStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KplugFill
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.UnrAll

theorem unrCorr_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  intro _hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw _
  by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
  · exact GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  · exact GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc

end GlobalTheory.UnrAll
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  first | exact @GlobalTheory.UnrAll.unrCorr_all | exact GlobalTheory.UnrAll.unrCorr_all | (intros; apply GlobalTheory.UnrAll.unrCorr_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenformStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, DownEig R i t := by
  first | exact @GlobalTheory.DownEigen.downEig | exact GlobalTheory.DownEigen.downEig | (intros; apply GlobalTheory.DownEigen.downEig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGoodStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.downwardThetaLift_preserves_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  first | exact @GlobalTheory.GoodLift.goodMem_of_given | exact GlobalTheory.GoodLift.goodMem_of_given | (intros; apply GlobalTheory.GoodLift.goodMem_of_given <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.goodTypes_exclude_levelCharacter : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  first | exact @GlobalTheory.GoodTypeNoChi.goodNoChi | exact GlobalTheory.GoodTypeNoChi.goodNoChi | (intros; apply GlobalTheory.GoodTypeNoChi.goodNoChi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.thetaLift_generation_at_realPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenInf R i t := by
  first | exact @GlobalTheory.GenReal.genInf | exact GlobalTheory.GenReal.genInf | (intros; apply GlobalTheory.GenReal.genInf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.thetaLift_generation_finitePlaces : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenFin R i t := by
  first | exact @GlobalTheory.DownLift.GenFinite.genFin | exact GlobalTheory.DownLift.GenFinite.genFin | (intros; apply GlobalTheory.DownLift.GenFinite.genFin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke

section

@[expose] public section

namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EulerFactorFromDoubling

section

@[expose] public section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.downNe_of_eulerRight_doubling : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  first | exact @_root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' | exact _root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' | (intros; apply _root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses' <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftInjNonVanTypeNZOfPrints

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory.Core.Rk.LiftOnto
theorem liftInj_nonVan_typeNZ_of_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL →
    GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram →
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
      [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  intro hDec hDbl hGL hHecke hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull
  have hEul : GlobalTheory.Core.Rk.IP.EulerRight D := GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified hDec hGL D
  have hPole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole := GlobalTheory.LiftPoleObj.simplePole_of_hecke hHecke
  have hNe : DownNe D := _root_.GlobalTheory.T.downNe_of_eulerRight_doubling hDbl hPole D hEul
  have hNV : ∀ i t, NonVan R i t := GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown D hNe G Pl0 T A Ks R F hG hFull
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.T.thetaLift_generation_finitePlaces hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.T.thetaLift_generation_at_realPlaces D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.T.downwardThetaLift_preserves_good D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.T.goodTypes_exclude_levelCharacter D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes hDec hHowe D G Pl0 T A Ks R F hG hFull
  have hOk : ∀ i t (ok : Pl D.host.E → Prop), UnrCorr R i t ok := by
    intro i t ok h hh s c y hy h1 h2 B B' hB hB' w hw _
    exact hU i t h hh s c y hy h1 h2 B B' hB hB' w hw trivial
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  exact ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hOk i A.μ0 _, hOk i A.μ0 _, hPar i A.μ0⟩),
    fun i t => ⟨hNV i t, hTNZ i t⟩⟩
end GlobalTheory.Core.Rk.LiftOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  first | exact @_root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | exact _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt <;> assumption)
end
end
end
