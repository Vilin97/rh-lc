module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement

section

@[expose] public section



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FlatDegProof

theorem flatDegAt_of_st {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hS : FlatDegreeSt) : FlatDegAt p i Y := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL : Laws Y.U (xiR D) := GlobalTheory.LawsDeep.laws_deep D p.T _ Y _ _ p.fw.laws hj hY.1
  obtain ⟨hd, χ, hχ, h1, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have := hS D.host.E p.T.Q.H hH χ hχ (p.T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL
  unfold FlatDegAt
  rwa [← h1]

end GlobalTheory.CovTop.FlatDegProof
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeHypotheses

section

@[expose] public section

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

abbrev _root_.GlobalTheory.T.FlatDegreeHypotheses : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt
end
end
end

-- Source module: Development.WeilBound.CoreStatements.ComplexPeriods.FlatDegreeResidues.FlatSlim

section

@[expose] public section

theorem FlatDegreeResidue.flatDegreeSt_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.FlatCore.FlatDegreeSt :=
  fun h => GlobalTheory.CompanionTheory.Ar.Br.flatDegreeSt_of_resK_gaga h GlobalTheory.CompanionTheory.Gaga.gagaSections
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatTensorSwapIsIso

section

@[expose] public section

section
theorem UpperTheory.Lit.Flat.flat_tensor_swap_isIso : _root_.GlobalTheory.T.FlatDegreeHypotheses :=
  fun _ _ _ => FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatDegreeStatement

section

@[expose] public section



section
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FlatDegProof
theorem flatDeg_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.FlatDegreeCondition := by
  intro hP
  have hS : FlatDegreeSt := _root_.UpperTheory.Lit.Flat.flat_tensor_swap_isIso hP hP.q2 hP.q4
  exact ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, le_rfl, 0, fun x hx _ ι p _ i _ Y hY => flatDegAt_of_st p i Y hY hS⟩⟩⟩
end GlobalTheory.CovTop.FlatDegProof
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.FlatDegreeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt | exact _root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.FlatDegProof.flatDeg_alt_alt <;> assumption)
end
end
end
end
