module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqConst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibraryStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cmLieStatements_iff_library : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ), GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧ (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) := by
  first | exact @GlobalTheory.LamF.lambdaBundle_conditions_iff | exact GlobalTheory.LamF.lambdaBundle_conditions_iff | (intros; apply GlobalTheory.LamF.lambdaBundle_conditions_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqParametersConstantStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_kronecker_cmLogPeriod_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  first | exact @GlobalTheory.LamF.exists_kronecker_logOm_eq | exact GlobalTheory.LamF.exists_kronecker_logOm_eq | (intros; apply GlobalTheory.LamF.exists_kronecker_logOm_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamIndLenDeg

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem GlobalTheory.LamF.lam_ind_len_deg :
    Formalism.L2.Pj.abelian₂.LamIndSt ∧ Formalism.L2.Pj.abelian₂.LamLenSt ∧
      ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, Formalism.L2.Pj.abelian₂.LamDegSt Q.H large₂.logOm := by
  obtain ⟨hdeg, hind, hlen⟩ := GlobalTheory.T.cmLieStatements_iff_library
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  refine ⟨hind.1 GlobalTheory.LamF.Ind.lamInd, hlen.1 (GlobalTheory.LamF.lamLen GlobalTheory.thetaUnifAV_all hL), fun D Q hQ large₂ => ?_⟩
  obtain ⟨_, χ, hχ, h⟩ := GlobalTheory.T.exists_kronecker_cmLogPeriod_eq D Q hQ large₂
  rw [← h]
  exact (hdeg _ _ _).1 (GlobalTheory.LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all hL _ Q.H χ hχ)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem GlobalTheory.ArcCM.lamDegSt_logOm₂ : Known → ∀ (D : D7) (T : Core D) (large₂ : SizeData₂ D), T.Q.Pins → GlobalTheory.LamF.LamDegSt T.Q.H large₂.logOm :=
  fun _ D T large₂ h => (GlobalTheory.LamF.lambdaBundle_conditions_iff.1 _ _ _).2 (GlobalTheory.LamF.lam_ind_len_deg.2.2 D T.Q h.1 large₂)
end
end
