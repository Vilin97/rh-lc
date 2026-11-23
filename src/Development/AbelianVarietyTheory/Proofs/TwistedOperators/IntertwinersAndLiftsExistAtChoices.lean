module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicityStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnSumMemRange

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

theorem ex_Th_of_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → R.ex_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr t
  obtain ⟨Th, hTh⟩ := GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks R h0 hf hm hr
  exact ⟨Th t, fun x => hTh t x⟩

end GlobalTheory.ProjectedLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lastStep_thetaLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ioX := by
  first | exact @GlobalTheory.Twist.LastStepLift.exists_lastStep_lift | exact GlobalTheory.Twist.LastStepLift.exists_lastStep_lift | (intros; apply GlobalTheory.Twist.LastStepLift.exists_lastStep_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMap

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefLinks

theorem exists_ioP_of_realDat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hω hv i
  obtain ⟨-, io, hio⟩ := GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R h0 hf hm hω hv
  exact ⟨io i, fun t => hio i t⟩

end GlobalTheory.IndefLinks
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  first | exact @GlobalTheory.IndefLinks.exists_ioP_of_realDat | exact GlobalTheory.IndefLinks.exists_ioP_of_realDat | (intros; apply GlobalTheory.IndefLinks.exists_ioP_of_realDat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecay

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.ThetaMap

theorem ex_thF_of_weak : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThPW → R.ex_ioP → R.ex_thF := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity hP D G Pl0 T A Ks R h0 hf hm h.ωP h.vP h.pt_theta
    (fun i t => (h.ioP i).1 (e i) t)
  exact ⟨th i t, h1 i t, h2 i t⟩

end GlobalTheory.DefLift.ThetaMap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThPW → R.ex_ioP → R.ex_thF := by
  first | exact @GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | exact GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | (intros; apply GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist

theorem exists_thG_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks R h0 hf hm fun i t => ((h i t).1 (e i t)).1
  exact ⟨th i t, h1 i t⟩

end GlobalTheory.Twist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_thetaLift_goodProjector_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  first | exact @GlobalTheory.Twist.exists_thG_models | exact GlobalTheory.Twist.exists_thG_models | (intros; apply GlobalTheory.Twist.exists_thG_models <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExAtAssembly

theorem exAt_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  intro h1 h2 h3 h4 D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr hH hc hp
  have eP : R.ex_ioP := GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap D G Pl0 T A Ks R h0 hf hm hp.ωP hp.vP
  have eF : R.ex_thF := GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay h3 D G Pl0 T A Ks R h0 hf hm hp eP
  exact ⟨GlobalTheory.T.exists_innerStepIntertwiners_thetaChain h1 h2 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.T.exists_innerStepThetaLifts h1 h2 h3 h4 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_thetaLift D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.ProjectedLift.ex_Th_of_chain D G Pl0 T A Ks R h0 hf hm hr, eP, eF,
    GlobalTheory.T.exists_thetaLift_goodProjector_models D G Pl0 T A Ks R h0 hf hm hp.thF eF⟩

end GlobalTheory.ExAtAssembly
end
end
