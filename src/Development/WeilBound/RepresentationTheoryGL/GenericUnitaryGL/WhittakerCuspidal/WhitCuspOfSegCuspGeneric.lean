module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.RankDual
public import GroundTheory.AutomorphicForms.WhittakerCriterion
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitLeOneOfDict
public import GroundTheory.AutomorphicForms.WhittakerGroups
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import GroundTheory.AutomorphicForms.ContragredientTranspose
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.RankDual

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep Module

namespace PositivityTheory.rg.gu.whit

theorem rank_le_one_iff_dual (W : Type) [AddCommGroup W] [Module ℂ W] :
    Module.rank ℂ W ≤ 1 ↔ Module.rank ℂ (Module.Dual ℂ W) ≤ 1 := by
  apply CompanionTheory.rg.gu.whit.rank_le_one_iff_dual <;> assumption

theorem rank_twJacquet_le_one_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1 := by
  apply CompanionTheory.rg.gu.whit.rank_twJacquet_le_one_iff <;> assumption

end PositivityTheory.rg.gu.whit
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitLeOneOfDict

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitLeOne_of_dict
    (hU : ∀ n : ℕ, unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n)
    (hC : ∀ (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)),
      ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) =
        GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k))
    (hR : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
      (θ : N →* ℂˣ), Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
        Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1)
    (hA : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ) :
    GlobalTheory.BZMir.Whit.WhitLeOne k := by
  apply CompanionTheory.rg.gu.whit.whitLeOne_of_dict <;> assumption

end PositivityTheory.rg.gu.whit
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitLeOne : GlobalTheory.BZMir.Whit.WhitLeOne k :=
  whitLeOne_of_dict k (unipB_eq_unipotent k) (whitChar_eq_psiN k)
    (fun ρ N θ => rank_twJacquet_le_one_iff ρ N θ) (fun ρ => isAdmissible_iff ρ)

theorem whitRankIrr : GlobalTheory.BZSeg.WhitRankIrr k :=
  fun ψ hψc hψ1 N V _ _ π hs hirr => whitLeOne k N ψ V π hs hirr hψc hψ1

end PositivityTheory.rg.gu.whit
end
end
end
