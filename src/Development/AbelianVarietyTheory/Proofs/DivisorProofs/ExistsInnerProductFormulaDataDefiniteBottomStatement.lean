module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstOneMemCuspFormsDefiniteBottomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLocalDoublingIntegralConverges
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtNegOfGramOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolynomialFockThetaVectorDefiniteBottomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLFunctionEqNormalizingFactorDefiniteBotto
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeParametersConstOneDefiniteBottom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
noncomputable section
namespace GlobalTheory.BottomIPData

theorem isParamFun_one_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc _ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t
  exact ⟨_, GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar (GlobalTheory.Grid.neg A) X.rA.Λ _
    (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) (fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2)⟩

end GlobalTheory.BottomIPData
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeParametersConstOneDefiniteBottomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  first | exact @GlobalTheory.BottomIPData.isParamFun_one_bottom | exact GlobalTheory.BottomIPData.isParamFun_one_bottom | (intros; apply GlobalTheory.BottomIPData.isParamFun_one_bottom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittIndexEqZeroDefiniteBottom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomWitt

theorem wittIndex_eq_zero :
    GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h _
  exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram h.stdW.1)

end GlobalTheory.BottomWitt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittIndexEqZeroDefiniteBottomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  first | exact @GlobalTheory.BottomWitt.wittIndex_eq_zero | exact GlobalTheory.BottomWitt.wittIndex_eq_zero | (intros; apply GlobalTheory.BottomWitt.wittIndex_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNormalizingFactorNeZeroDefiniteBottom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomIPData

theorem dSfun_bottom_ne_zero : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h t
  apply GlobalTheory.LFun.dSfun_ne_zero_of_re_pos
  have h2 := (GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j).1
  have hp : (0 : ℝ) < A'.rank := by rw [h.rank']; exact_mod_cast (by omega : 0 < SqNum.botSmall D i j)
  rw [show ((A'.rank : ℂ) / 2) = (((A'.rank : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  positivity

end GlobalTheory.BottomIPData
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNormalizingFactorNeZeroDefiniteBottomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  first | exact @GlobalTheory.BottomIPData.dSfun_bottom_ne_zero | exact GlobalTheory.BottomIPData.dSfun_bottom_ne_zero | (intros; apply GlobalTheory.BottomIPData.dSfun_bottom_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem data_exists : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H := gbig_and GlobalTheory.BottomPairData.pair_data (gbig_and GlobalTheory.T.hermitianWittIndex_eq_zero_definiteBottom (gbig_and GlobalTheory.T.isPolynomialFockThetaVector_definiteBottom (gbig_and GlobalTheory.BottomIPData.unram_bottom (gbig_and GlobalTheory.T.const_one_mem_cuspForms_definiteBottom
    (gbig_and GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom (gbig_and GlobalTheory.T.partialNormalizingFactor_ne_zero_definiteBottom (gbig_and GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom GlobalTheory.T.definiteBottom_localDoublingIntegral_converges)))))))
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ W i j A A' WW X hX hA t
  obtain ⟨cA, a, νW, 𝓕W, hP⟩ := h1 W i j A A' WW X hX hA t
  obtain ⟨par, hpar⟩ := h6 W i j A A' WW X hX t
  obtain ⟨κ, hκ, hL⟩ := h8 W i j A A' WW X hX t par hpar
  obtain ⟨P, hloc⟩ := h9 W i j A A' WW X hX t cA a νW 𝓕W hP
  refine ⟨betaB G i j, betaB G i j / alphaB Lc i j t, fun τ => -X.rA.s τ, X.rW.s, cA, a, νW, 𝓕W, X.rA.Λ, X.rW.Λ,
    sfB G t, par, κ, P, hP, h2 W i j A A' WW X hX t, h3 W i j A A' WW X hX t P, h4 W i j A A' WW X hX t P,
    h5 W i j A A' WW X hX t cA hP.setting, hpar, ?_, hκ, h7 W i j A A' WW X hX t, hL, hloc⟩
  intro v _ k _ g
  rfl

end GlobalTheory.BottomIPData

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.exists_innerProductFormula_data_definite_bottom : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  first | exact @GlobalTheory.BottomIPData.data_exists | exact GlobalTheory.BottomIPData.data_exists | (intros; apply GlobalTheory.BottomIPData.data_exists <;> assumption)
end
end
